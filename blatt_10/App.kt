package fufu

/**
 * Contains implementation of a graph and an argumentation instance for it.
 *
 * Created by Pazuzu on 27.06.2016.
 */

/**
 * A directed graph on nodes of type [X]. Does not allow unconnected nodes.
 *
 * [edges] The edges of the graph
 */
data class Graph<X>(val edges: Set<Pair<X, X>>) {
	/**
	 * Constructs a graph on a number of pairs
	 */
	constructor(vararg pairs: Pair<X, X>) : this(setOf(*pairs))

	/**
	 * The reverse of this graph
	 */
	val reverse: Graph<X> get() = Graph(edges.map { it.second to it.first }.toSet())

	/**
	 * All nodes in the graph
	 */
	val nodes: Set<X> get() = edges
			.flatMap { it.toList() }
			.toSet()

	/**
	 * Navigates all first order outgoing edges
	 */
	fun direct(vararg origin: X) = direct(setOf(*origin))

	/**
	 * Navigates all first order outgoing edges
	 */
	fun direct(origin: Set<X>) = edges
			.filter { it.first in origin }
			.map { it.second }
			.toSet()

	/**
	 * Finds all reachable nodes including the origin nodes
	 */
	fun reachable(vararg origin: X) = reachable(setOf(*origin))

	/**
	 * Finds all reachable nodes including the origin nodes
	 */
	fun reachable(origin: Set<X>): Set<X> {
		// Start out with the origin set
		val result = origin.toMutableSet()

		// Repeat until returned from
		while (true) {
			// Get the next extension of the front
			val next = direct(result)

			// If no new element is found, stop
			if ((next subtract result).isEmpty())
				return result.toSet()

			// Extend current result set
			result += next
		}
	}

	/**
	 * Performs graph union
	 */
	infix fun union(other: Graph<X>) = Graph(edges union other.edges)

	/**
	 * Performs graph intersection
	 */
	infix fun intersect(other: Graph<X>) = Graph(edges intersect other.edges)

	/**
	 * Performs graph subtraction
	 */
	infix fun subtract(other: Graph<X>) = Graph(edges subtract other.edges)

	/**
	 * Adds an edge
	 */
	operator fun plus(edge: Pair<X, X>) = Graph(edges union setOf(edge))

	/**
	 * Removes an edge
	 */
	operator fun minus(edge: Pair<X, X>) = Graph(edges subtract setOf(edge))
}

/**
 * True if bit is set in number
 */
infix fun Int.setIn(number: Int) = number and (1 shl this) == (1 shl this)

/**
 * Returns all subsets of a set
 */
fun <E> Set<E>.powerSet() = (0 until (1 shl size)).map { filterIndexed { p, e -> p setIn it }.toSet() }.toSet()

/**
 * Argumentation graph paired with a set of arguments
 * [graph] The graph representing argument attacks
 * [arguments] The arguments assumed to be true
 */
data class Instance<X>(val graph: Graph<X>, val arguments: Set<X>) {
	/**
	 * Constructs the instance of a graph and the arguments assumed to be true
	 */
	constructor(graph: Graph<X>, vararg arguments: X) : this(graph, setOf(*arguments))

	/**
	 * All conflicted edges
	 */
	val conflicted by lazy {
		arguments.flatMap { a -> arguments.map { b -> a to b }.filter { it in graph.edges } }
	}

	/**
	 * All defended nodes
	 */
	val defended by lazy {
		graph.nodes
				// Find all nodes A
				.filter { a ->
					graph.edges
							// Filter edges targeting A
							.filter { it.second == a }
							// Check that all have any edge, where the source is in the arguments nad the second is the
							// origin of an edge targeting A
							.all { ba -> graph.edges.any { it.first in arguments && it.second == ba.first } }
				}
	}

	/**
	 * True if instance is valid
	 */
	val isValid by lazy { conflicted.none() && defended.containsAll(arguments) }

	/**
	 * True if instance is complete
	 */
	val isComplete by lazy { arguments == characteristic.arguments }

	/**
	 * True if instance is stable
	 */
	val isStable by lazy { conflicted.none() && graph.direct(arguments).containsAll(graph.nodes subtract arguments) }

	/**
	 * Gets the characteristic value of the arguments, that is F_{AF}([arguments])
	 */
	val characteristic by lazy { Instance(graph, defended.toSet()) }
}

/**
 * Returns all Instances of an argumentation
 */
fun <X> Graph<X>.allInstances() = nodes.powerSet().map { Instance(this, it) }

/**
 * Returns from [allInstances] those that are valid
 */
fun <X> Graph<X>.validInstances() = allInstances()
		.filter { it.isValid }

/**
 * Returns from [allInstances] those that are complete extensions
 */
fun <X> Graph<X>.completeInstances() = validInstances()
		.filter { it.isComplete }

/**
 * Returns from [allInstances] those that are stable extensions
 */
fun <X> Graph<X>.stableInstances() = validInstances()
		.filter { it.isStable }

/**
 * Returns from [validInstances] the preferred instances
 */
fun <X> Graph<X>.preferredInstances() = validInstances()
		.let { vs -> vs.filter { e -> vs.none { e != it && it.arguments.containsAll(e.arguments) } } }

/**
 * The recursive union fixpoint of the characteristic function
 */
fun <X> Graph<X>.groundedInstance(): Instance<X> {
	tailrec fun Instance<X>.fixpoint(): Instance<X> =
			if (arguments.containsAll(characteristic.arguments))
				this
			else Instance(graph, arguments union characteristic.arguments).fixpoint()

	return Instance(this).fixpoint()
}

fun main(args: Array<String>) {
	assignment10_1()
	println("-".repeat(60))
	assignment10_2()
}

fun <X> Instance<X>.summary() {
	println(this)
	println("  - conflicted:   $conflicted")
	println("  - defended:     $defended")
	println("  - valid:        $isValid")
	println("  - complete:     ${graph.completeInstances().map { it.arguments }}")
	println("  - in complete:  ${this in graph.completeInstances()}")
	println("  - grounded:     ${graph.groundedInstance().arguments}")
	println("  - in grounded:  ${this == graph.groundedInstance()}")
	println("  - preferred:    ${graph.preferredInstances().map { it.arguments }}")
	println("  - in preferred: ${this in graph.preferredInstances()}")
	println("  - stable:       ${graph.stableInstances().map { it.arguments }}")
	println("  - in stable:    ${this in graph.stableInstances()}")
}

private fun assignment10_2() {
	val ret = Graph("A1" to "A2",
			"A1" to "A3",
			"A2" to "A3",
			"A3" to "A5",
			"A5" to "A4",
			"A4" to "A5",
			"A5" to "A6")

	println("Complete")
	for (ci in ret.completeInstances()) {
		ci.summary()
		println()
	}

	println("Stable")
	for (si in ret.stableInstances()) {
		si.summary()
		println()
	}
}

private fun assignment10_1() {
	val ret = Graph("A1" to "A2",
			"A2" to "A3",
			"A3" to "A4",
			"A3" to "A5",
			"A5" to "A2",
			"A6" to "A5",
			"A6" to "A1")

	val arg_a = Instance(ret, setOf("A1", "A3", "A6"))
	val arg_b = Instance(ret, setOf("A2", "A4", "A6"))
	val arg_c = Instance(ret, setOf("A1", "A3", "A4", "A6"))


	arg_a.summary()
	println()
	arg_b.summary()
	println()
	arg_c.summary()
	println()
}

private fun slide_340() {
	val ret = Graph("A1" to "A2") +
			("A2" to "A1") +
			("A2" to "A3") +
			("A3" to "A4") +
			("A4" to "A5") +
			("A5" to "A4") +
			("A5" to "A3")

	for (si in ret.stableInstances())
		println("Stable instance: ${si.arguments}")
}

private fun slide_338() {
	val ret = Graph("A1" to "A2", "A2" to "A1")

	for (ci in ret.completeInstances())
		println("Complete instance: ${ci.arguments}")
}

private fun slide_337() {
	val ret = Graph("A1" to "A2") +
			("A2" to "A1") +
			("A2" to "A3") +
			("A3" to "A4") +
			("A4" to "A5") +
			("A5" to "A4") +
			("A5" to "A3")

	println(Instance(ret, "A1").characteristic)
	println(Instance(ret, "A2").characteristic)
	println(Instance(ret, "A5").characteristic)
	println(Instance(ret, "A1", "A5").characteristic)
	println(Instance(ret, "A2", "A5").characteristic)
	println(Instance(ret, "A2", "A4").characteristic)

	for (ci in ret.completeInstances())
		println("Complete instance: ${ci.arguments}")
}

private fun slide_334() {
	val ret = Graph("A1" to "A2", "A2" to "A1")
	println(ret.groundedInstance())
}

private fun slide_333() {
	val ret = Graph("Autopsie" to "Pistole") +
			("Pistole" to "Messer") +
			("Messer" to "Pistole") +
			("Pistole" to "unschuldig") +
			("Messer" to "unschuldig") +
			("unschuldig" to "schuldig")

	val faf_a0 = Instance(ret)
	println(faf_a0)
	val faf_a1 = faf_a0.characteristic
	println(faf_a1)
	val faf_a2 = faf_a1.characteristic
	println(faf_a2)
	val faf_a3 = faf_a2.characteristic
	println(faf_a3)
	val faf_a4 = faf_a3.characteristic
	println(faf_a4)
	println()

	println(ret.groundedInstance())

}

private fun slide_330() {
	val ret = Graph("A1" to "A2") +
			("A2" to "A3")

	val faf_a0 = Instance(ret)
	println(faf_a0)
	val faf_a1 = faf_a0.characteristic
	println(faf_a1)
	val faf_a2 = faf_a1.characteristic
	println(faf_a2)
	val faf_a3 = faf_a2.characteristic
	println(faf_a3)
	println()

	val faf_b0 = Instance(ret, "A2")
	println(faf_b0)
	val faf_b1 = faf_b0.characteristic
	println(faf_b1)
}

private fun slide_327() {
	val ret = Graph("A1" to "A2") +
			("A2" to "A1") +
			("A2" to "A3") +
			("A3" to "A4") +
			("A4" to "A5") +
			("A5" to "A4") +
			("A5" to "A3")

	for (vi in ret.validInstances())
		println("Valid: ${vi.arguments}")
	for (pi in ret.preferredInstances())
		println("Preferred: ${pi.arguments}")
}

private fun slide_326() {
	val ret = Graph("A1" to "A2") +
			("A2" to "A3")

	for (vi in ret.validInstances())
		println("Valid: ${vi.arguments}")
	for (pi in ret.preferredInstances())
		println("Preferred: ${pi.arguments}")
}
