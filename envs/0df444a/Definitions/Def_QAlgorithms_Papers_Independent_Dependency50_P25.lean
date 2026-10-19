-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P25
-- name    : QAlgorithms_Papers_Independent_Dependency50_P25
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T08:16:13.310713+00:00
-- url     : https://prove2.me/theorems/e47146a2-9757-469a-b514-a8fbac2e2db8
-- title:
--   Definitions for On properties of the space of quantum states and their application to construction of entanglement monotones
-- statement:
--   The objects the formalized statements of *On properties of the space of quantum states and their application to construction of entanglement monotones* (arXiv:0804.1515) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `extendedConvexOn`: Appendix A1, PDF pp.30–31: finite convexity for an extended cost. The endpoint convention is `0 * (+∞) = 0 * (−∞) = 0`. On semibounded costs the right-hand side never adds opposing infinities. In the lower semicontinuous cases used below, convexity excludes mixed infinite signs by restriction to the segment joining any two proposed such points.
--   - `extendedAffineOn`: Appendix A1, PDF p.31, Corollary A-1: affine equality for extended costs, with the same zero-weight convention as finite convexity.
--   - `extendedSeries`: Appendix A1, PDF p.31: the extended weighted cost of a countable ensemble. Positive and negative parts are summed in `ENNReal`, separately. For normalized weights and an upper-bounded cost, the positive part is finite, while the answer may be negative infinity. This is not the conditionally totalized `tsum` of an `EReal` sequence.
--   - `extendedIntegral`: Appendix A1, PDF p.31, Eqs.(27)–(28): signed extended Lebesgue expectation, using the positive and negative parts. The source hypotheses in the statements below ensure that opposing infinite integrals do not occur. No Bochner integral is used for the extended cost.
--   - `banachBarycenter`: Appendix A1, PDF p.31: the actual Banach-space barycenter of a Borel probability on a closed bounded convex domain. Boundedness, separability, and the Borel structure in the theorem binders ensure Bochner integrability of the inclusion. Outside those hypotheses the integral retains Mathlib's default; no theorem here relies on that default.
-- source:
--   On properties of the space of quantum states and their application to construction of entanglement monotones, arXiv:0804.1515v4, https://arxiv.org/abs/0804.1515v4

import Mathlib

/-!
# Extended Jensen inequalities from Shirokov, arXiv:0804.1515v4

The three appendix results below are independent of the missing trace-class
state-space interface. All other planned results are explicitly deferred in
this paper's HARD.md and GAPS.json. Only theorem statements are admitted.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P25

/-- Appendix A1, PDF pp.30–31: finite convexity for an extended cost.
The endpoint convention is `0 * (+∞) = 0 * (−∞) = 0`. On semibounded
costs the right-hand side never adds opposing infinities. In the lower
semicontinuous cases used below, convexity excludes mixed infinite signs
by restriction to the segment joining any two proposed such points. -/
def extendedConvexOn {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Set E) (f : E → EReal) : Prop :=
  Convex ℝ A ∧
    ∀ x ∈ A, ∀ y ∈ A, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y

/-- Appendix A1, PDF p.31, Corollary A-1: affine equality for extended
costs, with the same zero-weight convention as finite convexity. -/
def extendedAffineOn {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Set E) (f : E → EReal) : Prop :=
  Convex ℝ A ∧
    ∀ x ∈ A, ∀ y ∈ A, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) = (a : EReal) * f x + (b : EReal) * f y

/-- Appendix A1, PDF p.31: the extended weighted cost of a countable
ensemble. Positive and negative parts are summed in `ENNReal`, separately.
For normalized weights and an upper-bounded cost, the positive part is
finite, while the answer may be negative infinity. This is not the
conditionally totalized `tsum` of an `EReal` sequence. -/
def extendedSeries (w : ℕ → ℝ) (c : ℕ → EReal) : EReal :=
  ((∑' i : ℕ, ENNReal.ofReal (w i) * (c i).toENNReal) : EReal) -
    ((∑' i : ℕ, ENNReal.ofReal (w i) * (-c i).toENNReal) : EReal)

/-- Appendix A1, PDF p.31, Eqs.(27)–(28): signed extended Lebesgue
expectation, using the positive and negative parts. The source hypotheses
in the statements below ensure that opposing infinite integrals do not
occur. No Bochner integral is used for the extended cost. -/
def extendedIntegral {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (c : X → EReal) : EReal :=
  ((∫⁻ x, (c x).toENNReal ∂mu) : EReal) -
    ((∫⁻ x, (-c x).toENNReal ∂mu) : EReal)

/-- Appendix A1, PDF p.31: the actual Banach-space barycenter of a Borel
probability on a closed bounded convex domain. Boundedness, separability,
and the Borel structure in the theorem binders ensure Bochner integrability
of the inclusion. Outside those hypotheses the integral retains Mathlib's
default; no theorem here relies on that default. -/
def banachBarycenter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Set E} [MeasurableSpace A] (mu : Measure A) : E :=
  ∫ x : A, (x : E) ∂mu

example {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Set E) (hA : Convex ℝ A) : extendedConvexOn A (fun _ => 0) := by
  refine ⟨hA, ?_⟩
  intro x hx y hy a b ha hb hab
  simp

example {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Set E) (hA : Convex ℝ A) : extendedAffineOn A (fun _ => 0) := by
  refine ⟨hA, ?_⟩
  intro x hx y hy a b ha hb hab
  simp

example (w : ℕ → ℝ) : extendedSeries w (fun _ => 0) = 0 := by
  simp [extendedSeries, EReal.toENNReal_zero]

example {X : Type*} [MeasurableSpace X] (mu : Measure X) :
    extendedIntegral mu (fun _ => 0) = 0 := by
  simp [extendedIntegral, EReal.toENNReal_zero]

example {X : Type*} [MeasurableSpace X] (mu : Measure X)
    [IsProbabilityMeasure mu] : extendedIntegral mu (fun _ => ⊤) = ⊤ := by
  simp [extendedIntegral, EReal.toENNReal_top, EReal.toENNReal_bot]

example {X : Type*} [MeasurableSpace X] (mu : Measure X)
    [IsProbabilityMeasure mu] : extendedIntegral mu (fun _ => ⊥) = ⊥ := by
  simp [extendedIntegral, EReal.toENNReal_top, EReal.toENNReal_bot]

example : extendedSeries (fun _ => 0) (fun _ => ⊤) = 0 := by
  simp [extendedSeries, EReal.toENNReal_top, EReal.toENNReal_bot]

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    {A : Set E} [MeasurableSpace A] [MeasurableSingletonClass A] (x : A) :
    banachBarycenter (Measure.dirac x) = (x : E) := by
  simp [banachBarycenter]

end QAlgorithms.Papers.Independent.Dependency50.P25


