-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeGraphCover
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeGraphCover
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:03.588285+00:00
-- url     : https://prove2.me/theorems/6016f2c3-d9f2-42a1-8147-be5b6f43c1c1
-- title:
--   Statements Cone Graph Cover
-- statement:
--   Definitions and structural lemmas for Statements Cone Graph Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeGraphCover.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGraphAreaFibre
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
open MeasureTheory
open scoped ENNReal
noncomputable section
def ConeGraphCover.Statement : Prop :=
  ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
    ∃ (e : ℕ → (Fin n ≃ Fin m ⊕ Fin (n - m))) (Ω : ℕ → Set (EuclideanSpace ℂ (Fin m)))
      (Φ : ℕ → EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin (n - m))),
      (∀ i, IsOpen (Ω i) ∧ DifferentiableOn ℂ (Φ i) (Ω i) ∧
        graphPt (e i) (Φ i) '' Ω i ⊆ coneSet h J ∧
        ∀ x ∈ Ω i, coneTangent h J (graphPt (e i) (Φ i) x) =
          LinearMap.range (fderiv ℂ (graphPt (e i) (Φ i)) x :
            EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))) ∧
      Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (coneSet h J \ ⋃ i, graphPt (e i) (Φ i) '' Ω i) = 0
end
end GroundTheory.Heights₂.Heights


