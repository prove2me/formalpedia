-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:38.371059+00:00
-- url     : https://prove2.me/theorems/8e770eb4-66e6-4596-ae09-0972890da4b2
-- title:
--   Statements Cone Tangent Average
-- statement:
--   Definitions and structural lemmas for Statements Cone Tangent Average, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeTangentAverage.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
variable {m n : ℕ}
theorem HermNorm.pointOf_add' (h : HermNorm n) (v w : EuclideanSpace ℂ (Fin n)) :
    h.pointOf (v + w) = h.pointOf v + h.pointOf w := by
  simp only [HermNorm.pointOf]
  rw [← Matrix.mulVec_add]
  rfl
theorem HermNorm.pointOf_smul' (h : HermNorm n) (c : ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    h.pointOf (c • v) = c • h.pointOf v := by
  simp only [HermNorm.pointOf]
  rw [← Matrix.mulVec_smul]
  rfl
def coneTangent (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (y : EuclideanSpace ℂ (Fin n)) : Submodule ℂ (EuclideanSpace ℂ (Fin n)) where
  carrier := {v | ∀ q ∈ J, ∑ j, eval (h.pointOf y) (pderiv j q) * h.pointOf v j = 0}
  add_mem' {v w} hv hw q hq := by
    simp only [HermNorm.pointOf_add', Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hv q hq, hw q hq, add_zero]
  zero_mem' q _ := by
    have h0 : h.pointOf 0 = 0 := by simpa using h.pointOf_smul' 0 0
    simp [h0]
  smul_mem' c v hv q hq := by
    simp only [HermNorm.pointOf_smul', Pi.smul_apply, smul_eq_mul, mul_left_comm _ c,
      ← Finset.mul_sum]
    rw [hv q hq, mul_zero]
def tangentJac (π : Fin m → Fin n → ℂ) (T : Submodule ℂ (EuclideanSpace ℂ (Fin n))) : ℝ :=
  LinearMap.normDet (𝕜 := ℂ) (U := T) (V := EuclideanSpace ℂ (Fin m)) ((linProjₗ π).comp T.subtype) ^ 2
def coneJac (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (π : Fin m → Fin n → ℂ)
    (y : EuclideanSpace ℂ (Fin n)) : ℝ :=
  tangentJac π (coneTangent h J y)
def firstCoordVec (n : ℕ) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun j => if (j : ℕ) = 0 then 1 else 0
def leadCoordPlane (n m : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Fin n)) where
  carrier := {y | ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0}
  add_mem' {v w} hv hw j hj := by
    simp [hv j hj, hw j hj]
  zero_mem' j _ := by
    simp
  smul_mem' c v hv j hj := by
    simp [hv j hj]
def tangentGaussProfile (n m : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
    (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π ((r : ℂ) • firstCoordVec n)) *
      ENNReal.ofReal (tangentJac π (leadCoordPlane n m))
def ConeAreaFormula.Statement : Prop :=
  ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
    ∀ (π : Fin m → Fin n → ℂ) (g : EuclideanSpace ℂ (Fin m) → ℝ≥0∞), Measurable g →
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ y in coneSet h J, g (linProj π y) * ENNReal.ofReal (coneJac h J π y)
            ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ w : EuclideanSpace ℂ (Fin m), (fibreCount h J π w : ℝ≥0∞) * g w
def ConeTangentAverage.Statement : Prop :=
  ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
      ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
          ∫⁻ y in coneSet h J,
            (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
              ENNReal.ofReal (coneJac h J π y) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
        ∫⁻ y in coneSet h J, tangentGaussProfile n m ‖y‖ ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ))
def ConeRadialIntegral.Statement : Prop :=
  ∀ (n m : ℕ), 0 < m → ∀ C : Set (EuclideanSpace ℂ (Fin n)),
    (∀ y ∈ C, ∀ t : ℝ, 0 < t → t • y ∈ C) →
    Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) {y | ‖y‖ < 1 ∧ y ∈ C} < ⊤ →
    ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ y in C, f ‖y‖ ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) {y | ‖y‖ < 1 ∧ y ∈ C} *
          ∫⁻ r in Set.Ioi (0 : ℝ), f r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1))
def TangentGaussMoment.Statement : Prop :=
  ∀ (n m : ℕ), 0 < m → m ≤ n →
    Measurable (tangentGaussProfile n m) ∧ AntitoneOn (tangentGaussProfile n m) (Set.Ici 0) ∧
      (∀ r : ℝ, 0 < tangentGaussProfile n m r) ∧
      0 < ∫⁻ r in Set.Ioi (0 : ℝ), tangentGaussProfile n m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) ∧
      ∫⁻ r in Set.Ioi (0 : ℝ), tangentGaussProfile n m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) < ⊤
end
end GroundTheory.Heights₂.Heights


