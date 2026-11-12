-- Prove2me | Definitions.Def_ReadOnceParityBP_LowerBound_Circuit
-- name    : ReadOnceParityBP_LowerBound_Circuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:23:55.776291+00:00
-- url     : https://prove2.me/theorems/da4b0487-30a1-41e1-9ecd-b6a420cc67ef
-- title:
--   Arithmetic circuits with syntactic supports and edge size
-- statement:
--   A circuit Γ is a list of variable, constant, finite-sum, and binary-product gates in topological order; its last gate is the output. Well-formedness requires a nonempty list and every input pointer to refer to an earlier gate. Repeated pointers are separate wires. Values and syntactic supports are computed together, with supports formed by unions even when polynomial terms cancel. Γ is syntactically multilinear when the input supports of every product gate are disjoint.
--
--   $$|\Gamma|=\sum_{g\in\Gamma}\operatorname{fanin}(g).$$
--
--   Sum gates have arbitrary finite fan-in and pay for every wire; products have fan-in two. Isolated constant or variable circuits have size zero. This matches the edge accounting in Claim 2.2 and permits sharing. Default values at malformed pointers are immaterial because theorem statements require well-formedness.
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), syntactic circuit definition and Claim 2.2 proof, p.4; size discussion p.11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- A gate of an arithmetic circuit over `F` with variables indexed by `ι`, presented as a
straight-line program: an input gate (a variable or a constant), or a sum of any finite list of earlier gates or a product of two
earlier gates, referred to by their positions. -/
inductive Gate (ι F : Type) where
  | var (i : ι)
  | const (c : F)
  | add (args : List ℕ)
  | mul (a b : ℕ)

/-- An arithmetic circuit: a list of gates in topological order; the output is the last gate.
Sharing of subcircuits is allowed (a gate may be used by many later gates). -/
structure Circuit (ι F : Type) where
  gates : List (Gate ι F)

namespace Circuit

variable {ι F : Type} [CommSemiring F]

/-- Value of one gate given the table of the earlier gates: the polynomial it computes and the
set of variables occurring syntactically in its subcircuit. -/
noncomputable def gateVal (acc : List (MvPolynomial ι F × Set ι)) :
    Gate ι F → MvPolynomial ι F × Set ι
  | .var i => (MvPolynomial.X i, {i})
  | .const c => (MvPolynomial.C c, ∅)
  | .add args => ((args.map fun a => (acc.getD a (0, ∅)).1).sum,
      {i | ∃ a ∈ args, i ∈ (acc.getD a (0, ∅)).2})
  | .mul a b => ((acc.getD a (0, ∅)).1 * (acc.getD b (0, ∅)).1,
      (acc.getD a (0, ∅)).2 ∪ (acc.getD b (0, ∅)).2)

/-- The table of all gates: entry `k` is the polynomial computed at gate `k` and the set of
variables appearing in the subcircuit rooted at gate `k`. -/
noncomputable def table (C : Circuit ι F) : List (MvPolynomial ι F × Set ι) :=
  C.gates.foldl (fun acc g => acc ++ [gateVal acc g]) []

/-- Children of a gate. -/
def Gate.children : Gate ι F → List ℕ
  | .var _ => []
  | .const _ => []
  | .add args => args
  | .mul a b => [a, b]

/-- Well-formedness: the circuit has at least one gate and every gate only refers to strictly
earlier gates (so the circuit is a DAG listed in topological order). -/
def WellFormed (C : Circuit ι F) : Prop :=
  C.gates ≠ [] ∧ ∀ (k : ℕ) (hk : k < C.gates.length), ∀ a ∈ Gate.children (C.gates[k]), a < k

/-- Volk, p. 4: a circuit is syntactically multilinear if every multiplication gate multiplies
two variable-disjoint subcircuits (the sets of variables occurring in the two subcircuits are
disjoint, regardless of cancellations in the polynomials they compute). -/
def SyntacticallyMultilinear (C : Circuit ι F) : Prop :=
  ∀ (k : ℕ) (hk : k < C.gates.length) (a b : ℕ), C.gates[k] = .mul a b →
    Disjoint (C.table.getD a (0, ∅)).2 (C.table.getD b (0, ∅)).2

/-- The circuit computes the polynomial `f`: its output (last) gate computes `f`. -/
def Computes (C : Circuit ι F) (f : MvPolynomial ι F) : Prop :=
  (C.table.getLast?).map Prod.fst = some f

/-- Edge size, as in Claim 2.2's proof (p.4): every incoming wire is charged.
Sum gates have arbitrary finite fan-in, products have fan-in two. Repeated inputs are
separate wires. An isolated variable or constant has size zero. -/
def size (C : Circuit ι F) : ℕ :=
  (C.gates.map fun g => (Gate.children g).length).sum

end Circuit

end ReadOnceParityBP.LowerBound


