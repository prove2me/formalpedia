-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:58.440285+00:00
-- url     : https://prove2.me/theorems/ad9c6589-8862-4364-a0c2-99e7d54447a7
-- title:
--   Card Support Le And Sum Two Pow Le
-- statement:
--   Definitions and structural lemmas for Card Support Le And Sum Two Pow Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/CardSupportLeAndSumTwoPowLe.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegralMulConjGaussianEqCoeffNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
open Complex in

noncomputable def fockIP {g : ℕ} (F G : EuclideanSpace ℂ (Fin g) → ℂ) : ℂ :=
  ((Real.pi ^ g)⁻¹ : ℝ) * ∫ z, F z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)
open Complex in

noncomputable def fockU {g : ℕ} (a : EuclideanSpace ℂ (Fin g)) (F : EuclideanSpace ℂ (Fin g) → ℂ) :
    EuclideanSpace ℂ (Fin g) → ℂ :=
  fun z => cexp ((∑ i, z i * (starRingEnd ℂ) (a i)) - (‖a‖ ^ 2 / 2 : ℝ)) * F (z - a)
def IsPolyLE {g : ℕ} (c : ℕ) (F : EuclideanSpace ℂ (Fin g) → ℂ) : Prop :=
  ∃ p : MvPolynomial (Fin g) ℂ, p.totalDegree ≤ c ∧ ∀ z, F z = MvPolynomial.eval (fun i => z i) p
end ReciprocityTheory.ChartRestriction.G.I2


