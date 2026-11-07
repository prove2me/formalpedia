-- Prove2me | Definitions.Def_FanInSemigroup_Circuit
-- name    : FanInSemigroup_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:56.954304+00:00
-- url     : https://prove2.me/theorems/078bb8e7-8fc7-4629-97ff-37ab267497d1
-- title:
--   Unbounded fan-in boolean circuit, its evaluation, size and depth
-- statement:
--   A **boolean circuit** is a directed acyclic graph whose nodes of indegree $0$ are inputs, labelled by variables from a type $V$, and whose other nodes are gates labelled $\wedge$, $\vee$ or $\neg$. A $\neg$ gate has indegree exactly one; $\wedge$ and $\vee$ gates have any positive indegree, with no bound on fan-in. Some nodes are selected as outputs, indexed by a type $O$.
--
--   Each node carries a boolean value on an assignment $x:V\to\{0,1\}$ in the obvious way, which gives the boolean function of each output node. The **size** of the circuit is the number of its edges, and its **depth** is the length of a longest path from an input node to an output node.
--
--   This is the model of the whole mission: constant depth and polynomial size are measured in it.
--
--   **Formalization Note** The gates are numbered in a topological order, each reading variables or lower-numbered gates. Every gate has a nonempty source set and there are no constant gates; a constant is available as $x\wedge\neg x$. There is one input node per variable, since merging inputs with the same label only lowers the edge count. The depth is a maximum over output nodes only, so a gate from which no output is reachable counts toward the size and not toward the depth.
-- source:
--   Chandra, Fortune, Lipton, Unbounded Fan-in Circuits and Associative Functions, STOC 1983, doi:10.1145/800061.808732, §2, p.54

import Mathlib

set_option autoImplicit false

namespace FanInSemigroup

/-- The three gate labels of a boolean circuit: `∧`, `∨` and `¬`. Chandra, Fortune, Lipton,
STOC 1983, §2, p.54: "Gate nodes are labelled with ∧, ∨, and ¬." -/
inductive GateKind where
  | and
  | or
  | not

/-- An **unbounded fan-in boolean circuit** with input variables `V` and outputs `O`. Chandra,
Fortune, Lipton, STOC 1983, §2, p.54: "A boolean circuit is a directed acyclic graph whose nodes
of indegree 0 are inputs and whose other nodes are gates. Input nodes are labelled with variables
{x1,x2,...}. Gate nodes are labelled with ∧, ∨, and ¬. Nodes labelled with ¬ have indegree one;
other nodes may arbitrary indegree. Certain nodes are selected as output nodes".

The nodes are the variables and the gates, numbered below `gates`; gate `g` reads variables and
gates numbered below `g`, which is a topological order of the directed acyclic graph.

**Formalization Note.** Indegree-0 nodes are exactly the inputs, so every gate has a nonempty
source set and there are no constant gates (a constant is available as `x ∧ ¬x`). There is one
input node per variable: merging input nodes with the same label only lowers the edge count. -/
structure Circuit (V O : Type*) where
  /-- The number of gates. -/
  gates : ℕ
  /-- The label of each gate. -/
  kind : Fin gates → GateKind
  /-- The in-neighbours of each gate: variables, or gates numbered below it. -/
  srcs : (g : Fin gates) → Finset (V ⊕ Fin g)
  /-- A gate has indegree at least one. -/
  srcs_nonempty : ∀ g, (srcs g).Nonempty
  /-- A `¬` gate has indegree exactly one. -/
  srcs_not : ∀ g, kind g = GateKind.not → (srcs g).card = 1
  /-- The node selected as each output. -/
  out : O → V ⊕ Fin gates

namespace Circuit

variable {V O : Type*}

/-- The boolean value at gate `g` on the input assignment `x`: the `∧` of the values of its
sources, their `∨`, or the negation of its unique source. -/
noncomputable def gateVal (C : Circuit V O) (x : V → Bool) (g : Fin C.gates) : Bool :=
  let source : V ⊕ Fin g → Bool := fun s =>
    match s with
    | Sum.inl v => x v
    | Sum.inr h => gateVal C x ⟨h.val, h.isLt.trans g.isLt⟩
  match C.kind g with
  | GateKind.and => (C.srcs g).inf source
  | GateKind.or => (C.srcs g).sup source
  | GateKind.not => !((C.srcs g).inf source)
termination_by g.val
decreasing_by exact h.isLt

/-- The boolean value at a node, input or gate. -/
noncomputable def nodeVal (C : Circuit V O) (x : V → Bool) : V ⊕ Fin C.gates → Bool
  | Sum.inl v => x v
  | Sum.inr g => C.gateVal x g

/-- The boolean function of an output node, p.54: "with each output node is associated a boolean
function in the obvious way". -/
noncomputable def eval (C : Circuit V O) (x : V → Bool) (o : O) : Bool :=
  C.nodeVal x (C.out o)

/-- The size, p.54: "The size of a circuit is the number of edges in it." -/
def size (C : Circuit V O) : ℕ :=
  ∑ g : Fin C.gates, (C.srcs g).card

/-- The length of a longest path from an input node to gate `g`. Every gate has a source, so a
longest path into `g` starts at an input node. -/
def gateLevel (C : Circuit V O) (g : Fin C.gates) : ℕ :=
  (C.srcs g).sup (fun s =>
    match s with
    | Sum.inl _ => 0
    | Sum.inr h => gateLevel C ⟨h.val, h.isLt.trans g.isLt⟩) + 1
termination_by g.val
decreasing_by exact h.isLt

/-- The length of a longest path from an input node to a node; an input node has level `0`. -/
def nodeLevel (C : Circuit V O) : V ⊕ Fin C.gates → ℕ
  | Sum.inl _ => 0
  | Sum.inr g => C.gateLevel g

/-- The depth, p.54: "The depth of a circuit is the length of a longest path from an input node
to an output node."

**Formalization Note.** The maximum runs over output nodes only, as on the page, so a gate from
which no output is reachable counts toward `size` but not toward `depth`. -/
def depth [Fintype O] (C : Circuit V O) : ℕ :=
  Finset.univ.sup fun o => C.nodeLevel (C.out o)

end Circuit

end FanInSemigroup


