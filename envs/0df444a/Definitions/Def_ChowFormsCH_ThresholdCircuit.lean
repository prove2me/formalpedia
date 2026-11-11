-- Prove2me | Definitions.Def_ChowFormsCH_ThresholdCircuit
-- name    : ChowFormsCH_ThresholdCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:56:32.275191+00:00
-- url     : https://prove2.me/theorems/e8f0c45d-f3e0-495e-9d07-c9cbd923f35d
-- title:
--   Threshold circuits: gates, well-formedness, depth, evaluation and size
-- statement:
--   A **threshold circuit** has numbered gates of five types: input gates, NOT gates, and unbounded fan-in AND, OR and (strict) MAJORITY gates; each gate has a list of immediate predecessors. The $m$ input gates are numbered $0,\dots,m-1$ and the $m'$ output gates $m,\dots,m+m'-1$; other gates may carry any numbers. On input bits $x$, input gate $i$ reads $x_i$ and every other gate applies its operation to its predecessors' values; MAJORITY is true iff more than half of its predecessors are true. The circuit has **depth at most $\Delta$** if there is a rank function, strictly increasing along wires, with values at most $\Delta$ (every path has at most $\Delta$ wires). The **size** is the number of wires.
--
--   These are the circuits of Lemmas 2.13, 2.18 and Theorem 4.9.
--
--   **Formalization Note** The paper does not define threshold circuits; this is the standard TC$^0$ basis following Vollmer. Size counts wires as in the paper's Definition 2.6; with an admissible numbering the number of gates is polynomially bounded by it. Evaluation propagates values for as many rounds as there are gates, which gives the true values on acyclic circuits.
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), §2.3, pp.11–12; Definition 2.6, p.11; Definition 2.7, p.12

import Mathlib

set_option autoImplicit false

namespace ChowFormsCH

/-- Gate types of threshold circuits: input gates, NOT, unbounded fan-in AND and OR, and
unbounded fan-in strict MAJORITY (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric
computations in CH via Chow forms*, arXiv:2611.05289, held version, sha256 75e796c6…, §2.3,
pp.11–12, following Vollmer [Vol99]). -/
inductive GateType where
  | input
  | neg
  | conj
  | disj
  | maj
  deriving DecidableEq

/-- The fixed numbering of gate types used by the direct connection language (Definition 2.8,
p.12: "Suppose a numbering of the gate types is fixed"). -/
def GateType.code : GateType → ℕ
  | .input => 0
  | .neg => 1
  | .conj => 2
  | .disj => 3
  | .maj => 4

/-- A threshold circuit with numbered gates (§2.3, Definitions 2.7–2.8, pp.11–12).

* `gates`: the gate numbers (any natural numbers; Remark 2.10 allows names via pairing functions);
* `numIn`, `numOut`: the number of input and output gates; input gates are numbered
  `0, …, numIn − 1` and output gates `numIn, …, numIn + numOut − 1` (Definition 2.7 items 1–2);
* `type a`, `preds a`: the type of gate `a` and the list of its immediate predecessors.

**Formalization Note** The paper does not define threshold circuits; this is the standard model
(TC⁰ basis AND, OR, NOT, MAJORITY). Well-formedness and acyclicity are separate predicates
(`WellFormed`, `HasDepthAtMost`). -/
structure ThresholdCircuit where
  gates : Finset ℕ
  numIn : ℕ
  numOut : ℕ
  type : ℕ → GateType
  preds : ℕ → List ℕ

namespace ThresholdCircuit

/-- Structural well-formedness: inputs and outputs are numbered as in Definition 2.7 items 1–2,
exactly the gates `0, …, numIn − 1` are inputs, predecessors are gates, inputs have no
predecessors, and NOT gates have exactly one. -/
def WellFormed (C : ThresholdCircuit) : Prop :=
  (∀ a, a < C.numIn + C.numOut → a ∈ C.gates) ∧
  (∀ a ∈ C.gates, (C.type a = GateType.input ↔ a < C.numIn)) ∧
  (∀ a ∈ C.gates, ∀ b ∈ C.preds a, b ∈ C.gates) ∧
  (∀ a ∈ C.gates, C.type a = GateType.input → C.preds a = []) ∧
  (∀ a ∈ C.gates, C.type a = GateType.neg → (C.preds a).length = 1)

/-- The circuit is acyclic of depth at most `Δ`: there is a rank function, strictly increasing
along wires, with values at most `Δ`. Equivalently every path has at most `Δ` wires (§2.3, p.11:
"The depth of the circuit is the length of the longest path from an input to an output"). -/
def HasDepthAtMost (C : ThresholdCircuit) (Δ : ℕ) : Prop :=
  ∃ rank : ℕ → ℕ, (∀ a ∈ C.gates, ∀ b ∈ C.preds a, rank b < rank a) ∧ ∀ a ∈ C.gates, rank a ≤ Δ

/-- Gate values after `k` rounds of propagation on the input bits `x` (input gate `i` reads
`x i`). MAJORITY is strict: true iff more than half of the predecessors are true. -/
def evalAux (C : ThresholdCircuit) (x : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, a => if C.type a = GateType.input then x a else false
  | k + 1, a =>
    match C.type a with
    | .input => x a
    | .neg => !(evalAux C x k ((C.preds a).headD 0))
    | .conj => (C.preds a).all (fun b => evalAux C x k b)
    | .disj => (C.preds a).any (fun b => evalAux C x k b)
    | .maj => decide ((C.preds a).length < 2 * (C.preds a).countP (fun b => evalAux C x k b))

/-- The value of gate `a` on the input bits `x`. For an acyclic circuit every path has fewer wires
than there are gates, so `|gates|` rounds of propagation give the true values. -/
def eval (C : ThresholdCircuit) (x : ℕ → Bool) (a : ℕ) : Bool :=
  evalAux C x C.gates.card a

/-- The `j`-th output bit, the value of gate `numIn + j`. -/
def output (C : ThresholdCircuit) (x : ℕ → Bool) (j : ℕ) : Bool :=
  C.eval x (C.numIn + j)

/-- The size of the circuit: its number of wires (§2.3, Definition 2.6, p.11: "The size of the
circuit is the number of wires in the circuit"). -/
def size (C : ThresholdCircuit) : ℕ :=
  ∑ a ∈ C.gates, (C.preds a).length

end ThresholdCircuit

end ChowFormsCH


