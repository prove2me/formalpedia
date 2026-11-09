-- Prove2me | Definitions.Def_CodedSorting_Circuit
-- name    : CodedSorting_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:05:02.748437+00:00
-- url     : https://prove2.me/theorems/f2ba822a-6702-4b0b-bbbc-32d48265966f
-- title:
--   Binary linear circuits with temporary wires, their networks and subspace labelings
-- statement:
--   A **binary linear circuit** on registers $\iota$ consists of gates $g_0,\dots,g_{G-1}$ executed in this order and temporary wires indexed by $\kappa$. Gate $g$ has a target register, a set of register operands not containing the target, and a set of temporary copies it reads; over $\mathbb F_2$ it replaces the target by the sum of its current value, the current values of the operands and the values of the copies. A **temporary wire** is a copy of one register taken at its input node or right after a gate the register participates in; it carries the register's value at that point and may be read only by later gates. The circuit **implements** $f$ when every initial state $x$ is mapped to $f(x)$.
--
--   The **network** of the circuit has an input node $s_r$ and an output node $t_r$ for every register $r$ and one node per gate. The **main wire** of $r$ is $s_r$, the gates $r$ participates in (in order), and $t_r$; a **temporary wire** is its branch node followed by the gates reading the copy (in order). The edges are the consecutive pairs of every wire, kept separately, so parallel edges count separately.
--
--   A **labeling** assigns a subspace of $\mathbb Q^m$ to every node. It is **admissible** when the labels grow by inclusion along every main wire and the two endpoint labels of every temporary-wire edge are nested. The **length** of an edge is the absolute difference of the dimensions of its endpoint labels, and the **total length** is
--   $$S=\sum_{(u,w)\in E}\big|\dim U_u-\dim U_w\big|,$$
--   split into the main-wire part and the temporary-wire part.
--
--   This is the circuit model of §4.2 and §5 shared by Lemma 5.1, Lemmas 5.2–5.3 and Corollary 5.4.
--
--   **Formalization Note** A gate is a single node, so all registers participating in a gate share its label, as the paper requires ("At every XOR gate, all participating registers have the same subspace label").
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), §4.2, p.7 (PDF 8), and §5, pp.11, 16 (PDF 12, 17)

import Mathlib

namespace CodedSorting

/-! # Binary linear (XOR) circuits with temporary wires, and their subspace labels

arXiv:2610.20079 (held version, sha256 6e149d97…8850b), §4.2, p.7, and §5, pp.11–16. -/

/-- A gate of an XOR circuit over registers `ι` and temporary copies `κ`: it updates its `target`
register to the XOR of the target's current value, the current values of the registers in
`mainOps`, and the values carried by the temporary copies in `tempOps` (§5, p.11: "A gate reads
the current values of specified registers and updates its target to an XOR of current values,
leaving all other registers unchanged"). -/
structure Gate (ι κ : Type) where
  target : ι
  mainOps : Finset ι
  tempOps : Finset κ
  target_not_mem : target ∉ mainOps

/-- Register `r` participates in gate `g` (as its target or as a register operand). -/
def Gate.Involves {ι κ : Type} (g : Gate ι κ) (r : ι) : Prop :=
  r = g.target ∨ r ∈ g.mainOps

/-- A temporary wire of a circuit with `G` gates: a copy of register `reg` taken at its input
node (`branch = none`) or right after gate `b` (`branch = some b`) (§5, p.11: "the circuit branches
a temporary wire from a register node to transmit certain intermediate values"). -/
structure TempWire (ι : Type) (G : ℕ) where
  reg : ι
  branch : Option (Fin G)

/-- The copy of temporary wire `tw` exists before gate `j`: it branches at the input node, or after
a gate `b < j`. -/
def TempWire.Before {ι : Type} {G : ℕ} (tw : TempWire ι G) (j : Fin G) : Prop :=
  match tw.branch with
  | none => True
  | some b => b < j

/-- A binary linear circuit: `G` gates executed in the order `0, 1, …, G−1`, and temporary wires
indexed by `κ`. A temporary wire branches only from a node of its own register (an input node or a
gate the register participates in), and a gate reads a copy only after the copy is made. -/
structure XorCircuit (ι κ : Type) where
  G : ℕ
  gates : Fin G → Gate ι κ
  temps : κ → TempWire ι G
  branch_involves : ∀ k b, (temps k).branch = some b → (gates b).Involves (temps k).reg
  read_after_branch : ∀ j k, k ∈ (gates j).tempOps → (temps k).Before j

namespace XorCircuit

variable {ι κ : Type}

open Classical in
/-- Execute gate `j` on a state `(s, c)` of register values `s` and copy values `c` over `𝔽₂`: the
target gets `s target + Σ_{r ∈ mainOps} s r + Σ_{k ∈ tempOps} c k`, and then every copy that
branches right after gate `j` takes the new value of its register. -/
noncomputable def gateStep (C : XorCircuit ι κ) (j : Fin C.G)
    (st : (ι → ZMod 2) × (κ → ZMod 2)) : (ι → ZMod 2) × (κ → ZMod 2) :=
  let g := C.gates j
  let v := st.1 g.target + ∑ r ∈ g.mainOps, st.1 r + ∑ k ∈ g.tempOps, st.2 k
  let s' := Function.update st.1 g.target v
  (s', fun k => if (C.temps k).branch = some j then s' (C.temps k).reg else st.2 k)

open Classical in
/-- Initial copy values: a copy taken at an input node carries that register's initial value; the
other copies are not made yet (value `0`, never read before they are made). -/
noncomputable def initCopies (C : XorCircuit ι κ) (x : ι → ZMod 2) : κ → ZMod 2 :=
  fun k => if (C.temps k).branch = none then x (C.temps k).reg else 0

/-- The final register values of the circuit on initial register values `x`. -/
noncomputable def eval (C : XorCircuit ι κ) (x : ι → ZMod 2) : ι → ZMod 2 :=
  ((List.finRange C.G).foldl (fun st j => C.gateStep j st) (x, C.initCopies x)).1

/-- The circuit implements `f`: on every initial state `x` (including arbitrary auxiliary values)
the final register values are `f x`. -/
def Implements (C : XorCircuit ι κ) (f : (ι → ZMod 2) → (ι → ZMod 2)) : Prop :=
  ∀ x, C.eval x = f x

end XorCircuit

/-- The nodes of the network of a circuit with `G` gates (§5, p.11): one input vertex `s_r` and one
output vertex `t_r` per register, and one vertex per gate. -/
inductive Node (ι : Type) (G : ℕ) where
  | source : ι → Node ι G
  | gate : Fin G → Node ι G
  | sink : ι → Node ι G

namespace XorCircuit

variable {ι κ : Type}

open Classical in
/-- The horizontal main wire of register `r` (§5, p.11): its input vertex, the gates `r`
participates in, in execution order, and its output vertex. -/
noncomputable def mainWire (C : XorCircuit ι κ) (r : ι) : List (Node ι C.G) :=
  Node.source r ::
    ((List.finRange C.G).filter (fun j => decide ((C.gates j).Involves r))).map Node.gate ++
    [Node.sink r]

/-- The node a temporary wire branches from: the input vertex of its register, or the gate after
which the copy is taken. -/
def branchNode (C : XorCircuit ι κ) (k : κ) : Node ι C.G :=
  match (C.temps k).branch with
  | none => Node.source (C.temps k).reg
  | some b => Node.gate b

open Classical in
/-- The temporary wire `k` (§5, p.11): its branch node, then the gates that read the copy, in
execution order; it ends after its last use. -/
noncomputable def tempWire (C : XorCircuit ι κ) (k : κ) : List (Node ι C.G) :=
  C.branchNode k ::
    ((List.finRange C.G).filter (fun j => decide (k ∈ (C.gates j).tempOps))).map Node.gate

end XorCircuit

/-- The edges of a wire: its consecutive pairs of nodes (each segment is one undirected edge;
edges of different wires are kept separately, so parallel edges count separately). -/
def wireEdges {α : Type} (w : List α) : List (α × α) :=
  w.zip w.tail

/-- A subspace labeling of the nodes by subspaces of `ℚ^m` is admissible (§5.1, p.11; §5.2, p.16):
labels grow by inclusion along every main wire ("the subspace labels grow by inclusion,
U_0 ⊆ U_1 ⊆ ⋯"), and the two endpoint labels of every temporary-wire edge are nested ("Every edge has
nested endpoint subspaces in one order or the other"). All registers participating in a gate share
that gate's node label. -/
def LabeledCircuit {ι κ : Type} {m : ℕ} (C : XorCircuit ι κ)
    (lab : Node ι C.G → Submodule ℚ (Fin m → ℚ)) : Prop :=
  (∀ r, ∀ e ∈ wireEdges (C.mainWire r), lab e.1 ≤ lab e.2) ∧
    (∀ k, ∀ e ∈ wireEdges (C.tempWire k), lab e.1 ≤ lab e.2 ∨ lab e.2 ≤ lab e.1)

/-- The length of an edge: the absolute difference of the dimensions of its endpoint labels. -/
noncomputable def edgeLength {N : Type} {m : ℕ} (lab : N → Submodule ℚ (Fin m → ℚ)) (e : N × N) :
    ℕ :=
  Int.natAbs ((Module.finrank ℚ (lab e.1) : ℤ) - Module.finrank ℚ (lab e.2))

/-- The total length of the main-wire edges. -/
noncomputable def mainLength {ι κ : Type} [Fintype ι] {m : ℕ} (C : XorCircuit ι κ)
    (lab : Node ι C.G → Submodule ℚ (Fin m → ℚ)) : ℕ :=
  ∑ r, ((wireEdges (C.mainWire r)).map (edgeLength lab)).sum

/-- The total length of the temporary-wire edges. -/
noncomputable def tempLength {ι κ : Type} [Fintype κ] {m : ℕ} (C : XorCircuit ι κ)
    (lab : Node ι C.G → Submodule ℚ (Fin m → ℚ)) : ℕ :=
  ∑ k, ((wireEdges (C.tempWire k)).map (edgeLength lab)).sum

/-- The total edge length `S` of the network (§5.2, p.16:
`S = Σ_{(u,w) ∈ E} |dim U_u − dim U_w|`). -/
noncomputable def totalLength {ι κ : Type} [Fintype ι] [Fintype κ] {m : ℕ} (C : XorCircuit ι κ)
    (lab : Node ι C.G → Submodule ℚ (Fin m → ℚ)) : ℕ :=
  mainLength C lab + tempLength C lab

end CodedSorting


