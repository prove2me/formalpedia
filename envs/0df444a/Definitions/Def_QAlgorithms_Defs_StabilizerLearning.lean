-- Prove2me | Definitions.Def_QAlgorithms_Defs_StabilizerLearning
-- name    : QAlgorithms_Defs_StabilizerLearning
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:09:23.019395+00:00
-- url     : https://prove2.me/theorems/773dcb29-b8a5-45a1-85fa-b42967865739
-- title:
--   Stabilizer states and adaptive learners from copies (shared definition layer)
-- statement:
--   # Stabilizer states and adaptive learners from copies (shared definition layer)
--
--   A. Montanaro, *Learning stabilizer states by Bell sampling* (arXiv:1707.04012v2), cited
--   "Montanaro p.N" (PDF pages), §§1–2.
--
--   Model of a learner. A learner proceeds in rounds `k = 0, …, R − 1`; round `k` takes `copies k`
--   fresh copies of the unknown state `|ψ⟩` and `anc k` ancillas in `|0⟩`, applies a circuit over
--   the standard gate set `{H, T, CNOT}` (frozen `htcxGateSet`) whose gates may be classically
--   controlled by bits computed (by a Boolean circuit) from the outcomes of the earlier rounds, and
--   measures all its qubits in the computational basis. A final Boolean circuit maps all outcomes
--   to `n(2n + 2)` bits, decoded as a stabilizer tableau by the frozen `decodeTableau`. The learner
--   is data fixed before `|ψ⟩` (trap Q2). Time counts quantum gates, ancilla preparations and
--   classical Boolean gates.
--   -/
--
--   namespace QAlgorithms
--
--   open Stabilizer
--
--   /-- Montanaro p.2: `|ψ⟩` is a stabilizer state: a unit vector stabilized by (fixed by every
--   element of) a commuting subgroup of the Pauli group (signs included, `−I` excluded; the frozen
--   `IsStabilizerGroup`) of order `2ⁿ`.
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\StabilizerLearning.lean

import Definitions.Def_QAlgorithms_Defs_IQAE
/-!
# Stabilizer states and adaptive learners from copies (shared definition layer)

A. Montanaro, *Learning stabilizer states by Bell sampling* (arXiv:1707.04012v2), cited
"Montanaro p.N" (PDF pages), §§1–2.

Model of a learner. A learner proceeds in rounds `k = 0, …, R − 1`; round `k` takes `copies k`
fresh copies of the unknown state `|ψ⟩` and `anc k` ancillas in `|0⟩`, applies a circuit over
the standard gate set `{H, T, CNOT}` (frozen `htcxGateSet`) whose gates may be classically
controlled by bits computed (by a Boolean circuit) from the outcomes of the earlier rounds, and
measures all its qubits in the computational basis. A final Boolean circuit maps all outcomes
to `n(2n + 2)` bits, decoded as a stabilizer tableau by the frozen `decodeTableau`. The learner
is data fixed before `|ψ⟩` (trap Q2). Time counts quantum gates, ancilla preparations and
classical Boolean gates.
-/

namespace QAlgorithms

open Stabilizer

/-- Montanaro p.2: `|ψ⟩` is a stabilizer state: a unit vector stabilized by (fixed by every
element of) a commuting subgroup of the Pauli group (signs included, `−I` excluded; the frozen
`IsStabilizerGroup`) of order `2ⁿ`. -/
def IsStabilizerState {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) : Prop :=
  IsState ψ ∧ ∃ S : Subgroup (Matrix.unitaryGroup (Qubits n) ℂ), IsStabilizerGroup S ∧
    Nat.card S = 2 ^ n ∧ ∀ M ∈ S, act (M : Matrix (Qubits n) (Qubits n) ℂ) ψ = ψ

/-- Montanaro pp.1–2: the input `|ψ⟩^{⊗c} ⊗ |0^w⟩` of a round on `c` copies and `w` ancillas;
copy `t` occupies wires `finProdFinEquiv (t, j)`, `j < n`, the ancillas come last (the layout of
the frozen `qexInputState`). -/
noncomputable def copiesInputState (n c w : ℕ) (ψ : EuclideanSpace ℂ (Qubits n)) :
    EuclideanSpace ℂ (Qubits (c * n + w)) :=
  WithLp.toLp 2 fun z =>
    if ∀ a : Fin w, z (Fin.natAdd (c * n) a) = false then
      ∏ t : Fin c, ψ (fun j => z (Fin.castAdd w (finProdFinEquiv (t, j))))
    else 0

/-- Montanaro pp.1–2: an adaptive learner from copies (see the module docstring). Round `k`
consumes `copies k ⩾ 1` copies and `anc k` ancillas; `template k` is its circuit, a gate tagged
`some b` being applied iff control bit `b` is `1`; the control bits of round `k` are
`ctrl k` evaluated on the record of all outcomes with the bits of rounds `⩾ k` set to `0` (so only
earlier outcomes are visible); `out` maps the full record to the `n(2n + 2)` bits of a tableau.
"At most two copies at a time" is the statements' hypothesis `∀ k, copies k ≤ 2`. -/
structure CopyLearner (n : ℕ) where
  /-- The number of rounds. -/
  R : ℕ
  /-- Copies consumed by each round. -/
  copies : Fin R → ℕ
  /-- Every round consumes at least one copy. -/
  copies_pos : ∀ k, 1 ≤ copies k
  /-- Ancillas of each round. -/
  anc : Fin R → ℕ
  /-- Classical control bits of each round. -/
  cbits : Fin R → ℕ
  /-- The circuit of each round, each gate optionally controlled by a control bit. -/
  template : (k : Fin R) → List (GateApp htcxGateSet (copies k * n + anc k) × Option (Fin (cbits k)))
  /-- The Boolean circuit computing the control bits of each round from the outcome record. -/
  ctrl : (k : Fin R) → BoolCircuit (∑ j, (copies j * n + anc j)) (cbits k)
  /-- The Boolean circuit computing the output tableau from the outcome record. -/
  out : BoolCircuit (∑ j, (copies j * n + anc j)) (n * (2 * n + 2))

namespace CopyLearner

variable {n : ℕ}

/-- Montanaro pp.1–2: the unitary of round `k` for control bits `bits`: the template's untagged
gates and the gates whose control bit is `1`, in order. -/
def roundUnitary (L : CopyLearner n) (k : Fin L.R) (bits : Fin (L.cbits k) → Bool) :
    Matrix (Qubits (L.copies k * n + L.anc k)) (Qubits (L.copies k * n + L.anc k)) ℂ :=
  Circuit.unitary ((L.template k).filterMap fun g => if g.2.all bits then some g.1 else none)

/-- Montanaro p.1: the number of copies of `|ψ⟩` consumed. -/
def copiesUsed (L : CopyLearner n) : ℕ :=
  ∑ k, L.copies k

/-- Montanaro pp.1–2: the running time: quantum gates, ancilla preparations and classical Boolean
gates (Gaussian elimination over `F₂` counts as Boolean gates). -/
def time (L : CopyLearner n) : ℕ :=
  ∑ k, ((L.template k).length + L.anc k + (L.ctrl k).size) + L.out.size

/-- The record of all outcomes of all rounds, concatenated (round `k`'s outcome is
`z k : Qubits (copies k * n + anc k)`), via `finSigmaFinEquiv`. -/
def record (L : CopyLearner n) (z : (k : Fin L.R) → Qubits (L.copies k * n + L.anc k)) :
    Fin (∑ j, (L.copies j * n + L.anc j)) → Bool :=
  fun i => z (finSigmaFinEquiv.symm i).1 (finSigmaFinEquiv.symm i).2

/-- The record visible to round `k`: the outcomes of the rounds `< k`, the later bits `0`. -/
def recordBefore (L : CopyLearner n) (z : (k : Fin L.R) → Qubits (L.copies k * n + L.anc k))
    (k : Fin L.R) : Fin (∑ j, (L.copies j * n + L.anc j)) → Bool :=
  fun i => if (finSigmaFinEquiv.symm i).1 < k then z (finSigmaFinEquiv.symm i).1
    (finSigmaFinEquiv.symm i).2 else false

/-- Montanaro pp.1–2: the probability that the learner identifies `|ψ⟩`: the sum over all outcome
records of the chain-rule probability of the record (each round on fresh copies, its circuit
fixed by the earlier outcomes) times the indicator that the output tableau's projector is
`|ψ⟩⟨ψ|` (identification up to global phase, trap Q11). -/
noncomputable def successProb (L : CopyLearner n) (ψ : EuclideanSpace ℂ (Qubits n)) : ℝ :=
  ∑ z : (k : Fin L.R) → Qubits (L.copies k * n + L.anc k),
    (∏ k, prob (act (L.roundUnitary k ((L.ctrl k).eval (L.recordBefore z k)))
      (copiesInputState n (L.copies k) (L.anc k) ψ)) (z k)) *
    (open Classical in
      if tableauProjector (decodeTableau n (List.ofFn (L.out.eval (L.record z)))) = pureDensity ψ
      then 1 else 0)

end CopyLearner

/-! ### Sanity tests -/

example (n : ℕ) (ψ : EuclideanSpace ℂ (Qubits n)) (z : Qubits (0 * n + 0)) :
    copiesInputState n 0 0 ψ z = 1 := by
  simp [copiesInputState]

example (n : ℕ) (ψ : EuclideanSpace ℂ (Qubits n)) (z : Qubits (1 * n + 0)) :
    copiesInputState n 1 0 ψ z = ψ (fun j => z (Fin.castAdd 0 (finProdFinEquiv ((0 : Fin 1), j)))) := by
  simp [copiesInputState]

example {n : ℕ} (L : CopyLearner n) : L.copiesUsed = ∑ k, L.copies k := rfl

example {n : ℕ} (L : CopyLearner n) (z : (k : Fin L.R) → Qubits (L.copies k * n + L.anc k))
    (k : Fin L.R) (i : Fin (∑ j, (L.copies j * n + L.anc j))) (h : (finSigmaFinEquiv.symm i).1 = k) :
    L.recordBefore z k i = false := by
  simp [CopyLearner.recordBefore, h]

example {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) (h : IsStabilizerState ψ) : ‖ψ‖ = 1 :=
  h.1

end QAlgorithms


