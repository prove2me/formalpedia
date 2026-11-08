-- Prove2me | Definitions.Def_TreeEdgeRankPC_Circuit
-- name    : TreeEdgeRankPC_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:28.035433+00:00
-- url     : https://prove2.me/theorems/30102a6a-443c-40df-bba7-e1d0b30fa024
-- title:
--   Boolean circuits of fan-in at most two: size, depth, evaluation and binary code
-- statement:
--   A **Boolean circuit** on $n$ input bits is a finite directed acyclic multigraph whose vertices are inputs or gates. Inputs have indegree zero. Each gate $v$ has an ordered list of $k\in\{0,1,2\}$ incoming wires and a function $f_v:\{0,1\}^k\to\{0,1\}$; a gate with $k=0$ is a constant. A binary gate has distinct left and right input slots even if both wires have the same source. An input assignment determines the value of each vertex in topological order. An ordered list of designated vertices gives the outputs. The **size** is the number of vertices, and the **depth** is the maximum number of edges on a directed path.
--
--   This is the machine model of NC¹ on which the mission's reductions run.
--
--   **Formalization Note** Vertices are numbered in a topological order, so predecessors are earlier numbers and acyclicity is built in; every finite DAG has such a numbering. An output vertex need not have outdegree zero. `BoolCircuit.enc` is a fixed binary code: `encNat` of the number of vertices (with `encNat` a self-delimiting binary code), then the vertex codes with truth tables, then the outputs. A logspace-uniform family must print this code.
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), §3.2, p.12 (Boolean circuits)

import Mathlib

namespace TreeEdgeRankPC

/-- A vertex of a Boolean circuit, §3.2, p.12 (arXiv:2610.12438, held version of 2026-11-02, sha256
9e04ca7b…): "A Boolean circuit is a finite directed acyclic multigraph whose vertices are inputs or
gates. Inputs have indegree zero. Each gate v has an ordered list of k ∈ {0, 1, 2} incoming wires and a
function f_v : {0, 1}^k → {0, 1}; a gate with k = 0 is a constant."

**Formalization Note.** Predecessors are vertex numbers; a binary gate has distinct left and right
slots even if both wires have the same source. -/
inductive CircuitNode where
  /-- An input vertex, reading the bit of the input word with this index. -/
  | input (i : ℕ)
  /-- A gate with `k = 0`. -/
  | const (b : Bool)
  /-- A gate with `k = 1`. -/
  | unary (f : Bool → Bool) (u : ℕ)
  /-- A gate with `k = 2`: left slot `u`, right slot `w`. -/
  | binary (f : Bool → Bool → Bool) (u w : ℕ)

/-- Vertex number `i` of a circuit on `n` inputs is well formed: an input index is below `n`, and all
predecessors are earlier vertices. -/
def CircuitNode.WF (n i : ℕ) : CircuitNode → Prop
  | .input j => j < n
  | .const _ => True
  | .unary _ u => u < i
  | .binary _ u w => u < i ∧ w < i

/-- A **Boolean circuit** on `n` input bits, §3.2, p.12.

**Formalization Note.** The vertices are numbered `0, …, nodes.length - 1` in a topological order, which
makes the graph acyclic by construction; every finite DAG has such a numbering. The ordered list of
"designated sinks" is `outputs`. As usual for a circuit computing a function, an output need not be a
vertex of outdegree zero: this changes size and depth by at most a constant factor and additive term. -/
structure BoolCircuit (n : ℕ) where
  /-- The vertices, in a topological order. -/
  nodes : List CircuitNode
  /-- The ordered list of output vertices. -/
  outputs : List ℕ
  nodes_wf : ∀ i (h : i < nodes.length), nodes[i].WF n i
  outputs_wf : ∀ o ∈ outputs, o < nodes.length

/-- The value of a vertex from the input word `x` and the values `vals` of the earlier vertices. -/
def CircuitNode.value (x vals : List Bool) : CircuitNode → Bool
  | .input i => x.getD i false
  | .const b => b
  | .unary f u => f (vals.getD u false)
  | .binary f u w => f (vals.getD u false) (vals.getD w false)

/-- The length of the longest directed path ending at a vertex, from those of the earlier vertices:
`0` at inputs and constants, one more than the deepest predecessor at other gates. -/
def CircuitNode.depthAt (ds : List ℕ) : CircuitNode → ℕ
  | .input _ => 0
  | .const _ => 0
  | .unary _ u => ds.getD u 0 + 1
  | .binary _ u w => max (ds.getD u 0) (ds.getD w 0) + 1

namespace BoolCircuit

variable {n : ℕ} (C : BoolCircuit n)

/-- The **size**: "Its size is its number of vertices" (§3.2, p.12). -/
def size : ℕ := C.nodes.length

/-- The **depth**: "its depth is the maximum number of edges on a directed path" (§3.2, p.12). -/
def depth : ℕ :=
  (C.nodes.foldl (fun ds nd => ds ++ [nd.depthAt ds]) []).foldr max 0

/-- The values of all vertices on the input word `x`, computed in topological order (§3.2, p.12). -/
def values (x : List Bool) : List Bool :=
  C.nodes.foldl (fun vals nd => vals ++ [nd.value x vals]) []

/-- The output of the circuit on the input word `x`. -/
def eval (x : List Bool) : List Bool :=
  C.outputs.map fun o => (C.values x).getD o false

end BoolCircuit

/-- The self-delimiting binary code of a natural number used in the mission's encodings: each bit of
`Nat.bits a` (least significant first) is preceded by `true`, and a final `false` ends the code. It is
prefix-free and injective. -/
def encNat (a : ℕ) : List Bool := (Nat.bits a).flatMap (fun b => [true, b]) ++ [false]

/-- The binary code of a vertex: a two-bit tag, then the truth table (four rows for binary gates, two
for unary gates) or the constant, then the predecessors or input index by `encNat`. -/
def CircuitNode.enc : CircuitNode → List Bool
  | .input i => [false, false] ++ encNat i
  | .const b => [false, true, b]
  | .unary f u => [true, false, f false, f true] ++ encNat u
  | .binary f u w =>
      [true, true, f false false, f false true, f true false, f true true] ++ encNat u ++ encNat w

/-- The binary code of a circuit that a logspace-uniform family must print: `encNat` of the number of
vertices, the codes of the vertices in order, and the output vertices by `encNat`. It is injective, and
is the usual standard encoding of a circuit up to logspace translation. -/
def BoolCircuit.enc {n : ℕ} (C : BoolCircuit n) : List Bool :=
  encNat C.nodes.length ++ C.nodes.flatMap CircuitNode.enc ++ C.outputs.flatMap encNat

end TreeEdgeRankPC


