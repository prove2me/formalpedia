-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P06
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P06
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T04:02:44.855516+00:00
-- url     : https://prove2.me/theorems/7725bab8-e4e5-4625-9c94-2559720bc28a
-- title:
--   Definitions for Is Entanglement Monogamous?
-- statement:
--   The objects the formalized statements of *Is Entanglement Monogamous?* (arXiv:quant-ph/0307120) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Opinion`: PDF p.5: each opinion system is one qubit in the displayed 0/1 basis.
--   - `eprDensity`: PDF p.5, (1): the normalized plus-sign EPR density, using the frozen vector.
--   - `IsCoordinateDensity`: PDF pp.5-7: positive trace-class density operators of trace one. This paper-local adapter reuses the pinned accepted predicate verbatim: nuclearity, real nonnegative finite quadratic forms, summable diagonal and trace one. No global-purity, finite-rank or countable-basis restriction is imposed.
--   - `swapBobJoe`: PDF pp.5,7: interchange Bob and Joe, fixing Alice; both are the same qubit.
--   - `aliceJoeMarginal`: PDF p.7, weak extension terminology applied to the p.5 example: trace Bob out, leaving Alice and Joe in that order.
--   - `eveBlock`: PDF pp.5-6: the unnormalized Eve operator for the outcome (a,b) of computational-basis measurement of both qubits. Zero blocks remain zero; there is no division by the outcome probability.
--   - `sharedBitLaw`: PDF p.5: classical common-bit law on n parties. p is the probability of 0 (false); 1-p is the probability of 1 (true). The two contributions are added, so even at n=0 this raw formula remains a normalized one-point law; the sharing theorem requires at least one actual party.
-- source:
--   Is Entanglement Monogamous?, arXiv:quant-ph/0307120v1, https://arxiv.org/abs/quant-ph/0307120v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P09

/-!
# Is Entanglement Monogamous? Elementary statements

Source: Barbara M. Terhal, arXiv:quant-ph/0307120v1, PDF pp.5-7.
All new definitions are local to this paper. Nuclear expansions and density
positivity are reused from pinned accepted Dependency50.P33, lines 29-60.
The unrestricted partial trace is reused from pinned accepted Frontier18.P09.
These accepted-library imports follow the independent-paper override. Arbitrary orthonormal index types retain
arbitrary Hilbert dimension, including nonseparable spaces. No Countable or
Fintype hypothesis is imposed on the third system.

Equation (2), p.5, prints Joe as a ket. The statements retain the prose's actual
hypothesis (only AB is pure), and use the computed, possibly mixed, third marginal.
This correction of ket shorthand requires independent moderation. All theorem
proofs are intentionally sorry. Compilation is pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P06

open scoped BigOperators

open QAlgorithms.Papers.Independent.Dependency50.P33 (NuclearExpansion)
open QAlgorithms.Papers.Independent.Frontier18.P09 (partialTraceRightCoeff)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5: each opinion system is one qubit in the displayed 0/1 basis. -/
abbrev Opinion := Qubits 1

/-- PDF p.5, (1): the normalized plus-sign EPR density, using the frozen vector. -/
def eprDensity : Matrix (Opinion × Opinion) (Opinion × Opinion) ℂ :=
  pureDensity (maxEntangled 1)

/-- PDF pp.5-7: positive trace-class density operators of trace one.
This paper-local adapter reuses the pinned accepted predicate verbatim:
nuclearity, real nonnegative finite quadratic forms, summable diagonal and trace
one. No global-purity, finite-rank or countable-basis restriction is imposed. -/
abbrev IsCoordinateDensity {I : Type} (X : Matrix I I ℂ) : Prop :=
  QAlgorithms.Papers.Independent.Dependency50.P33.IsDensity X

/-- PDF pp.5,7: interchange Bob and Joe, fixing Alice; both are the same qubit. -/
def swapBobJoe (X : Matrix ((Opinion × Opinion) × Opinion)
    ((Opinion × Opinion) × Opinion) ℂ) :
    Matrix ((Opinion × Opinion) × Opinion) ((Opinion × Opinion) × Opinion) ℂ :=
  fun x y => X ((x.1.1, x.2), x.1.2) ((y.1.1, y.2), y.1.2)

/-- PDF p.7, weak extension terminology applied to the p.5 example:
trace Bob out, leaving Alice and Joe in that order. -/
def aliceJoeMarginal (X : Matrix ((Opinion × Opinion) × Opinion)
    ((Opinion × Opinion) × Opinion) ℂ) : Matrix (Opinion × Opinion) (Opinion × Opinion) ℂ :=
  fun x y => ∑ b : Opinion, X ((x.1, b), x.2) ((y.1, b), y.2)

/-- PDF pp.5-6: the unnormalized Eve operator for the outcome (a,b)
of computational-basis measurement of both qubits. Zero blocks remain zero;
there is no division by the outcome probability. -/
def eveBlock {E : Type} (X : Matrix ((Opinion × Opinion) × E)
    ((Opinion × Opinion) × E) ℂ) (a b : Opinion) : Matrix E E ℂ :=
  fun e f => X ((a, b), e) ((a, b), f)

/-- PDF p.5: classical common-bit law on n parties. p is the probability
of 0 (false); 1-p is the probability of 1 (true). The two contributions are
added, so even at n=0 this raw formula remains a normalized one-point law;
the sharing theorem requires at least one actual party. -/
def sharedBitLaw (n : ℕ) (p : ℝ) (x : Fin n → Bool) : ℝ :=
  (if x = (fun _ => false) then p else 0) +
    (if x = (fun _ => true) then 1 - p else 0)

/-- Nuclearity includes the zero operator, while normalization excludes it as a state. -/
example {I : Type} : Nonempty (NuclearExpansion (0 : Matrix I I ℂ)) := by
  refine ⟨{ left := fun _ => 0
            right := fun _ => 0
            summable := ?_
            coefficients := ?_ }⟩
  · simp
  · intro i j
    simp

example {I : Type} : ¬ IsCoordinateDensity (0 : Matrix I I ℂ) := by
  intro h
  simpa using h.2.2.2

example {A E : Type} :
    partialTraceRightCoeff (0 : Matrix (A × E) (A × E) ℂ) = 0 := by
  funext a b
  simp [partialTraceRightCoeff]

example {A E : Type} [Fintype E] (X : Matrix (A × E) (A × E) ℂ) :
    partialTraceRightCoeff X = traceRight X := by
  funext a b
  simp [partialTraceRightCoeff, traceRight]

/-- The mismatched 01 outcome has zero EPR probability. -/
example : eprDensity ((fun _ : Fin 1 => false), (fun _ => true))
    ((fun _ : Fin 1 => false), (fun _ => true)) = 0 := by
  have h : (fun _ : Fin 1 => false) ≠ (fun _ : Fin 1 => true) := by decide
  simp [eprDensity, pureDensity, maxEntangled, h]

example {E : Type} (X : Matrix ((Opinion × Opinion) × E)
    ((Opinion × Opinion) × E) ℂ) (a b : Opinion) (e f : E) :
    eveBlock X a b e f = X ((a, b), e) ((a, b), f) := by
  rfl

example (p : ℝ) : sharedBitLaw 1 p (fun _ => false) = p := by
  have h : (fun _ : Fin 1 => false) ≠ (fun _ : Fin 1 => true) := by decide
  simp [sharedBitLaw, h]

example (p : ℝ) : sharedBitLaw 0 p (fun _ => false) = 1 := by
  have h : (fun _ : Fin 0 => false) = (fun _ : Fin 0 => true) := by
    funext i
    exact Fin.elim0 i
  simp [sharedBitLaw, h] <;> ring

/-- The ownership permutation is an involution. -/
example (X : Matrix ((Opinion × Opinion) × Opinion)
    ((Opinion × Opinion) × Opinion) ℂ) : swapBobJoe (swapBobJoe X) = X := by
  rfl

example : aliceJoeMarginal (0 : Matrix ((Opinion × Opinion) × Opinion)
    ((Opinion × Opinion) × Opinion) ℂ) = 0 := by
  funext a b
  simp [aliceJoeMarginal]

end QAlgorithms.Papers.Independent.Intakethird100.P06


