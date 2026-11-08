-- Prove2me | Definitions.Def_TreeEdgeRankPC_AM2CVP
-- name    : TreeEdgeRankPC_AM2CVP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:29.572867+00:00
-- url     : https://prove2.me/theorems/a8809a37-4ced-425f-88aa-8d565c31660f
-- title:
--   AM2CVP: alternating monotone circuit value with fan-in 2 and fan-out 2
-- statement:
--   The **circuit value problem** asks whether a designated output of a given circuit evaluates to 1 on a given input assignment. **AM2CVP** is its restriction to binary AND and OR gates with fan-out at most two, in which every wire between gates joins opposite types, inputs feed only OR gates, and the designated output is an OR sink. Vertices are given in topological order $1,\dots,m$ with the designated sink last.
--
--   A language over $\{0,1\}$ of codes of such instances, it is the source problem of the mission's reduction.
--
--   **Formalization Note** Nodes are numbered from $0$; the paper's node $i$ is element $i-1$. A gate has a left and a right predecessor, both earlier nodes, and parallel wires are allowed and count separately in the fan-out. An AND gate reads only OR gates; an OR gate reads only inputs and AND gates. A non-output node may have fan-out zero. `AM2Instance.enc` is the list of node codes (a tag, then the bit or the two predecessors by `encNat`). A string that encodes no instance is not in the language.
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), §3.2, p.13 (Circuit value); §4.2, p.17; §3.2, p.12 (slots)

import Mathlib
import Definitions.Def_TreeEdgeRankPC_Circuit

namespace TreeEdgeRankPC

/-- A node of an AM2CVP instance, §3.2, p.13 and §4.2, p.17 (arXiv:2610.12438, held version of 2026-11-02,
sha256 9e04ca7b…): "Boolean input values, nodes representing inputs, AND gates, or OR gates, and directed
wires between nodes". A gate has distinct left and right input slots (p.12). -/
inductive AM2Node where
  /-- An input node with its assigned bit. -/
  | input (b : Bool)
  /-- A binary AND gate with its left and right predecessors. -/
  | andGate (l r : ℕ)
  /-- A binary OR gate with its left and right predecessors. -/
  | orGate (l r : ℕ)

/-- The node is an OR gate. -/
def AM2Node.isOr : AM2Node → Bool
  | .orGate _ _ => true
  | _ => false

/-- The number of wires from node `i` into this node, counting the two input slots separately. -/
def AM2Node.wiresFrom (i : ℕ) : AM2Node → ℕ
  | .input _ => 0
  | .andGate l r => (if l = i then 1 else 0) + (if r = i then 1 else 0)
  | .orGate l r => (if l = i then 1 else 0) + (if r = i then 1 else 0)

/-- An **instance of AM2CVP** with its input assignment, §3.2, p.13: "binary AND and OR gates and fan-out
at most two. Every wire between gates joins opposite types, inputs feed only OR gates, and the designated
output is an OR sink. ... We number them 1, ..., m and place the designated sink last".

**Formalization Note.** Nodes are numbered from `0`, so the paper's node `i` is `nodes[i - 1]` and the
designated sink is the last element. The vertices are in topological order: predecessors are earlier
nodes. Parallel wires are allowed and count separately (p.12, p.20). -/
structure AM2Instance where
  /-- The nodes in topological order. -/
  nodes : List AM2Node
  /-- Node numbers are in topological order. An AND gate reads only OR gates. An OR gate reads inputs and
  AND gates only. These two conditions say "Every wire between gates joins opposite types, inputs feed
  only OR gates". -/
  gates_wf : ∀ i (h : i < nodes.length), match nodes[i] with
    | .input _ => True
    | .andGate l r => ∃ (hl : l < i) (hr : r < i),
        (nodes[l]'(hl.trans h)).isOr = true ∧ (nodes[r]'(hr.trans h)).isOr = true
    | .orGate l r => ∃ (hl : l < i) (hr : r < i),
        (nodes[l]'(hl.trans h)).isOr = false ∧ (nodes[r]'(hr.trans h)).isOr = false
  /-- Fan-out at most two, counting parallel wires separately. -/
  fanout_le : ∀ i, (nodes.map (AM2Node.wiresFrom i)).sum ≤ 2
  /-- There is a last node. -/
  nonempty : nodes ≠ []
  /-- The last node is an OR gate. -/
  last_isOr : (nodes.getLast nonempty).isOr = true
  /-- The last node is a sink. -/
  last_sink : (nodes.map (AM2Node.wiresFrom (nodes.length - 1))).sum = 0

/-- The values `c_i` of all nodes, in topological order. -/
def AM2Instance.values (C : AM2Instance) : List Bool :=
  C.nodes.foldl (fun vals nd => vals ++ [match nd with
    | .input b => b
    | .andGate l r => vals.getD l false && vals.getD r false
    | .orGate l r => vals.getD l false || vals.getD r false]) []

/-- The value `c_m` of the designated sink. -/
def AM2Instance.value (C : AM2Instance) : Bool := C.values.getLastD false

/-- The binary code of a node: tag `0` and the bit for an input; tags `10`, `11` for AND, OR, followed by
`encNat` of the two predecessors. -/
def AM2Node.enc : AM2Node → List Bool
  | .input b => [false, b]
  | .andGate l r => [true, false] ++ encNat l ++ encNat r
  | .orGate l r => [true, true] ++ encNat l ++ encNat r

/-- The binary code of an instance: the codes of its nodes in order. It is injective since node codes are
prefix-free. The conditions of `AM2Instance` are local checks on it, as p.20 notes: "The source
restrictions can also be checked in NC¹". -/
def AM2Instance.enc (C : AM2Instance) : List Bool := C.nodes.flatMap AM2Node.enc

/-- **AM2CVP** as a language over `{0, 1}`, §3.2, p.13: "whether a designated output of a given circuit
evaluates to 1 on a given input assignment", on the alternating monotone fan-in 2, fan-out 2 instances. A
string that encodes no instance is not in the language. -/
def AM2CVP : Set (List Bool) := {s | ∃ C : AM2Instance, s = C.enc ∧ C.value = true}

end TreeEdgeRankPC


