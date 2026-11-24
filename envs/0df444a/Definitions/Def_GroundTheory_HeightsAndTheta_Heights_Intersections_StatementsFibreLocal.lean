-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreLocal
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:41.023439+00:00
-- url     : https://prove2.me/theorems/5f82a5b1-f01f-427a-9cf7-7c01d727b7ff
-- title:
--   Statements Fibre Local
-- statement:
--   Definitions and structural lemmas for Statements Fibre Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsFibreLocal.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
def momentPoly {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ)
    (Q : MvPolynomial (Fin 3) (Ω → ℝ)) : MvPolynomial (Fin 3) ℝ :=
  ∑ m ∈ Q.support, monomial m (∫ p, w p * coeff m Q p ∂μ)
def dotPoly {Ω : Type*} (n : Ω → S2) : MvPolynomial (Fin 3) (Ω → ℝ) :=
  ∑ i, X i * C (fun p => (n p : E3) i)
def fibreMomentPoly (k : ℕ) : MvPolynomial (Fin 3) ℝ :=
  momentPoly (sphereMeasure.prod sphereMeasure)
    (fun p : S2 × S2 => (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2))
    (aeval ![dotPoly Prod.fst, dotPoly Prod.snd] (dgPoly k))
def pushMomentPoly (k : ℕ) : MvPolynomial (Fin 3) ℝ :=
  (-(2 * (k : ℝ) - 1)) • momentPoly sphereMeasure (fun _ => 1) (dotPoly id ^ (2 * k - 2))
def FibreLocal.Statement : Prop :=
  (∀ (k : ℕ) (a : E3),
    ∫ n₁ : S2, ∫ n₂ : S2, (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (n₁ : E3) (n₂ : E3)) / 2) *
        eval ![inner ℝ a (n₁ : E3), inner ℝ a (n₂ : E3)] (dgPoly k) ∂sphereMeasure ∂sphereMeasure =
      -kappa k * inner ℝ a a ^ (k - 1)) ∧
  (∀ (k : ℕ) (B : Type) [CommRing B] [Algebra ℝ B] (a : Fin 3 → B),
    aeval a (fibreMomentPoly k) = algebraMap ℝ B (-kappa k) * (∑ i, a i ^ 2) ^ (k - 1)) ∧
  (∀ k : ℕ, 1 ≤ k → ∀ a : E3,
    -(2 * (k : ℝ) - 1) * ∫ n : S2, inner ℝ a (n : E3) ^ (2 * k - 2) ∂sphereMeasure =
      -(inner ℝ a a ^ (k - 1))) ∧
  (∀ k : ℕ, 1 ≤ k → ∀ (B : Type) [CommRing B] [Algebra ℝ B] (a : Fin 3 → B),
    aeval a (pushMomentPoly k) = -(∑ i, a i ^ 2) ^ (k - 1)) ∧
  ∀ k : ℕ, kappa k = (1 / 2) * ∑ j ∈ Finset.range k, (1 : ℝ) / (2 * j + 1)
end
end GroundTheory.Heights₂.Heights.Inter


