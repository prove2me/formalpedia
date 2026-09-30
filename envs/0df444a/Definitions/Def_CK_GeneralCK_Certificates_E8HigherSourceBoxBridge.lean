-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8HigherSourceBoxBridge
-- name    : CK_GeneralCK_Certificates_E8HigherSourceBoxBridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:08:56.330633+00:00
-- url     : https://prove2.me/theorems/b8e5d162-f3e8-42be-9939-fcacfeae59cb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8HigherSourceBoxBridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8HigherSourceBoxBridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8HigherSourceBoxBridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8HigherSourceBoxBridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8HigherSourceBoxBridge.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8AnalyticInverseRecurrence

-- ===== source module GeneralCK.Certificates.E8HigherSourceBoxBridge =====
section

/-!
# Recurrence handoff for the retained higher E8 coefficient boxes

This file removes the analytic composition equation from the numerical
certificate interface.  The only remaining inputs are the five concrete
bounds on the exact recurrence expressions.
-/

namespace GeneralCK.Certificates.E8HigherSourceBoxBridge

open E8AnalyticGerm E8AnalyticCoefficientBoxes
open E8AnalyticInverseRecurrence

/-- The linear coefficient of the concrete slope germ is nonzero.  This is
deduced from the already-proved local inverse composition, so it does not
require a separate derivative calculation. -/
theorem thetaTaylorCoeff_one_ne : thetaTaylorCoeff 1 ≠ 0 := by
  intro hzero
  have h := composeCoeff_theta_q 1
  rw [composeCoeff_eq_remainder_add_linear thetaTaylorCoeff qTaylorCoeff
    (by norm_num : 1 ≤ 1)] at h
  have hrem : remainderCoeff thetaTaylorCoeff qTaylorCoeff 1 = 0 := by
    unfold remainderCoeff
    rw [show (Finset.range 2).erase 1 = {0} by decide]
    simp [thetaTaylorCoeff, iteratedDeriv_zero]
  rw [hrem, hzero] at h
  norm_num [targetCoeff] at h

/-- Every positive coefficient of the concrete analytic inverse is exactly
the output of the executable recurrence. -/
theorem qTaylorCoeff_eq_inverseStep {n : ℕ} (hn : 1 ≤ n) :
    qTaylorCoeff n = inverseStep thetaTaylorCoeff qTaylorCoeff n :=
  coefficient_eq_inverseStep hn thetaTaylorCoeff_one_ne
    (composeCoeff_theta_q n)

/-- The five retained higher source boxes follow from bounds on the five
exact recurrence expressions.  No analytic-composition premise remains. -/
theorem higher_source_boxes_of_inverseStep_bounds
    (h7 : ‖inverseStep thetaTaylorCoeff qTaylorCoeff 7 -
        (sourceCenter 7 : ℂ)‖ ≤ (sourceHalfWidth 7 : ℝ))
    (h9 : ‖inverseStep thetaTaylorCoeff qTaylorCoeff 9 -
        (sourceCenter 9 : ℂ)‖ ≤ (sourceHalfWidth 9 : ℝ))
    (h11 : ‖inverseStep thetaTaylorCoeff qTaylorCoeff 11 -
        (sourceCenter 11 : ℂ)‖ ≤ (sourceHalfWidth 11 : ℝ))
    (h13 : ‖inverseStep thetaTaylorCoeff qTaylorCoeff 13 -
        (sourceCenter 13 : ℂ)‖ ≤ (sourceHalfWidth 13 : ℝ))
    (h15 : ‖inverseStep thetaTaylorCoeff qTaylorCoeff 15 -
        (sourceCenter 15 : ℂ)‖ ≤ (sourceHalfWidth 15 : ℝ)) :
    (‖qTaylorCoeff 7 - (sourceCenter 7 : ℂ)‖ ≤
        (sourceHalfWidth 7 : ℝ)) ∧
    (‖qTaylorCoeff 9 - (sourceCenter 9 : ℂ)‖ ≤
        (sourceHalfWidth 9 : ℝ)) ∧
    (‖qTaylorCoeff 11 - (sourceCenter 11 : ℂ)‖ ≤
        (sourceHalfWidth 11 : ℝ)) ∧
    (‖qTaylorCoeff 13 - (sourceCenter 13 : ℂ)‖ ≤
        (sourceHalfWidth 13 : ℝ)) ∧
    (‖qTaylorCoeff 15 - (sourceCenter 15 : ℂ)‖ ≤
        (sourceHalfWidth 15 : ℝ)) := by
  rw [qTaylorCoeff_eq_inverseStep (by norm_num : 1 ≤ 7),
    qTaylorCoeff_eq_inverseStep (by norm_num : 1 ≤ 9),
    qTaylorCoeff_eq_inverseStep (by norm_num : 1 ≤ 11),
    qTaylorCoeff_eq_inverseStep (by norm_num : 1 ≤ 13),
    qTaylorCoeff_eq_inverseStep (by norm_num : 1 ≤ 15)]
  exact ⟨h7, h9, h11, h13, h15⟩

/-- An endpoint enclosure in an exact rational box implies the midpoint / half
width norm enclosure used by the analytic source interface. -/
theorem norm_sub_sourceCenter_le_of_real_endpoint_bounds
    {n : ℕ} {z : ℂ} {x : ℝ}
    (hz : z = (x : ℂ))
    (hlo : ((sourceBox n).lo : ℝ) ≤ x)
    (hhi : x ≤ ((sourceBox n).hi : ℝ)) :
    ‖z - (sourceCenter n : ℂ)‖ ≤ (sourceHalfWidth n : ℝ) := by
  subst z
  rw [show (x : ℂ) - (sourceCenter n : ℂ) =
      ((x - (sourceCenter n : ℝ) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;>
    simp only [sourceCenter, sourceHalfWidth, Rat.cast_div, Rat.cast_add,
      Rat.cast_sub] <;> linarith

/-- Certificate-shaped data for the five retained higher inverse steps.  The
values are required to be real, and their two endpoints are compared against
the exact decimal rationals imported from `cert_local_K.cpp`. -/
structure HigherInverseStepInRetainedBoxes where
  x7 : ℝ
  eq7 : inverseStep thetaTaylorCoeff qTaylorCoeff 7 = (x7 : ℂ)
  lo7 : ((sourceBox 7).lo : ℝ) ≤ x7
  hi7 : x7 ≤ ((sourceBox 7).hi : ℝ)
  x9 : ℝ
  eq9 : inverseStep thetaTaylorCoeff qTaylorCoeff 9 = (x9 : ℂ)
  lo9 : ((sourceBox 9).lo : ℝ) ≤ x9
  hi9 : x9 ≤ ((sourceBox 9).hi : ℝ)
  x11 : ℝ
  eq11 : inverseStep thetaTaylorCoeff qTaylorCoeff 11 = (x11 : ℂ)
  lo11 : ((sourceBox 11).lo : ℝ) ≤ x11
  hi11 : x11 ≤ ((sourceBox 11).hi : ℝ)
  x13 : ℝ
  eq13 : inverseStep thetaTaylorCoeff qTaylorCoeff 13 = (x13 : ℂ)
  lo13 : ((sourceBox 13).lo : ℝ) ≤ x13
  hi13 : x13 ≤ ((sourceBox 13).hi : ℝ)
  x15 : ℝ
  eq15 : inverseStep thetaTaylorCoeff qTaylorCoeff 15 = (x15 : ℂ)
  lo15 : ((sourceBox 15).lo : ℝ) ≤ x15
  hi15 : x15 ≤ ((sourceBox 15).hi : ℝ)

/-- Exact retained endpoint checks close all five higher analytic source
boxes. -/
theorem higher_source_boxes_of_retained_endpoint_checks
    (h : HigherInverseStepInRetainedBoxes) :
    (‖qTaylorCoeff 7 - (sourceCenter 7 : ℂ)‖ ≤
        (sourceHalfWidth 7 : ℝ)) ∧
    (‖qTaylorCoeff 9 - (sourceCenter 9 : ℂ)‖ ≤
        (sourceHalfWidth 9 : ℝ)) ∧
    (‖qTaylorCoeff 11 - (sourceCenter 11 : ℂ)‖ ≤
        (sourceHalfWidth 11 : ℝ)) ∧
    (‖qTaylorCoeff 13 - (sourceCenter 13 : ℂ)‖ ≤
        (sourceHalfWidth 13 : ℝ)) ∧
    (‖qTaylorCoeff 15 - (sourceCenter 15 : ℂ)‖ ≤
        (sourceHalfWidth 15 : ℝ)) := by
  apply higher_source_boxes_of_inverseStep_bounds
  · exact norm_sub_sourceCenter_le_of_real_endpoint_bounds h.eq7 h.lo7 h.hi7
  · exact norm_sub_sourceCenter_le_of_real_endpoint_bounds h.eq9 h.lo9 h.hi9
  · exact norm_sub_sourceCenter_le_of_real_endpoint_bounds h.eq11 h.lo11 h.hi11
  · exact norm_sub_sourceCenter_le_of_real_endpoint_bounds h.eq13 h.lo13 h.hi13
  · exact norm_sub_sourceCenter_le_of_real_endpoint_bounds h.eq15 h.lo15 h.hi15

end GeneralCK.Certificates.E8HigherSourceBoxBridge

end


