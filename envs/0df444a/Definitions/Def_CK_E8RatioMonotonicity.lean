-- Prove2me | Definitions.Def_CK_E8RatioMonotonicity
-- name    : CK_E8RatioMonotonicity
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T21:29:56.072985+00:00
-- url     : https://prove2.me/theorems/fa52cb74-5b03-4d81-8eba-2ef351bc215f
-- title:
--   Courtade–Kumar proof module `E8RatioMonotonicity` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `E8RatioMonotonicity` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `E8RatioMonotonicity` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module E8RatioMonotonicity (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/E8RatioMonotonicity.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8LargeSStableCriterion

-- ===== source module E8RatioMonotonicity =====
section

/-!
# E8 reciprocal forward-derivative criterion

This staged module does not assert the open sign condition. It identifies it
with convexity of `g = 1 / Θ'`, preserving ratios throughout the reduction.
-/

namespace GeneralCK.E8RatioMonotonicity

open Set Filter
open Certificates.E8InverseJet5Bridge
open Certificates.E8TAxisDeltaDirectionalJet

noncomputable def reciprocal (u : ℝ) : ℝ := (deriv e8Theta u)⁻¹

noncomputable def ratio (u : ℝ) : ℝ :=
  -deriv (deriv e8Theta) u / deriv e8Theta u ^ 2

/-- A two-term relative-derivative expression; no profile expansion. -/
noncomputable def curvature (u : ℝ) : ℝ :=
  2 * (deriv (deriv e8Theta) u / deriv e8Theta u) ^ 2 -
    deriv (deriv (deriv e8Theta)) u / deriv e8Theta u

theorem reciprocal_pos {u : ℝ} (hu : 0 < u) : 0 < reciprocal u :=
  inv_pos.mpr (deriv_e8Theta_pos hu)

theorem hasDerivAt_reciprocal {u : ℝ} (hu : 0 < u) :
    HasDerivAt reciprocal (ratio u) u := by
  have hd := (e8ThetaCanonicalJet5_replay_unconditional.1 u hu).2.1
  have hi := hd.inv (deriv_e8Theta_pos hu).ne'
  rw [hasDerivAt_iff_isLittleO] at hi ⊢
  simpa only [e8ThetaCanonicalJet5, reciprocal, ratio, Pi.inv_apply, smul_eq_mul] using hi

theorem hasDerivAt_ratio {u : ℝ} (hu : 0 < u) :
    HasDerivAt ratio (reciprocal u * curvature u) u := by
  have hA : HasDerivAt (deriv e8Theta) (deriv (deriv e8Theta) u) u := by
    have hd := (e8ThetaCanonicalJet5_replay_unconditional.1 u hu).2.1
    rw [hasDerivAt_iff_isLittleO] at hd ⊢
    simpa only [e8ThetaCanonicalJet5, smul_eq_mul] using hd
  have hB : HasDerivAt (deriv (deriv e8Theta))
      (deriv (deriv (deriv e8Theta)) u) u := by
    have hd := (e8ThetaCanonicalJet5_replay_unconditional.1 u hu).2.2.1
    rw [hasDerivAt_iff_isLittleO] at hd ⊢
    simpa only [e8ThetaCanonicalJet5, smul_eq_mul] using hd
  have hne := (deriv_e8Theta_pos hu).ne'
  have hd := hB.neg.div (hA.pow 2) (pow_ne_zero 2 hne)
  have hi := hd.congr_deriv (show _ = reciprocal u * curvature u from by
    simp only [reciprocal, curvature, Pi.pow_apply, Pi.neg_apply,
      Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp
    <;> ring)
  rw [hasDerivAt_iff_isLittleO] at hi ⊢
  simpa only [ratio, Pi.div_apply, Pi.neg_apply, Pi.pow_apply, smul_eq_mul] using hi

theorem deriv_reciprocal {u : ℝ} (hu : 0 < u) :
    deriv reciprocal u = ratio u := (hasDerivAt_reciprocal hu).deriv

theorem deriv_ratio {u : ℝ} (hu : 0 < u) :
    deriv ratio u = reciprocal u * curvature u := (hasDerivAt_ratio hu).deriv

/-- Exact correspondence with the existing certificate-facing numerator. -/
theorem jet_numerator_eq {y : ℝ} (hy : y ∈ e8SlopeRange) :
    e8LogDerivativeJetNumerator y =
      reciprocal (e8Q y) ^ 4 * curvature (e8Q y) := by
  have hne := (deriv_e8Theta_pos (e8Q_pos hy)).ne'
  simp only [e8LogDerivativeJetNumerator, qJet, e8QJet5,
    e8ThetaCanonicalJet5, reciprocal, curvature]
  field_simp
  <;> ring

theorem jet_numerator_nonneg_iff {y : ℝ} (hy : y ∈ e8SlopeRange) :
    0 ≤ e8LogDerivativeJetNumerator y ↔ 0 ≤ curvature (e8Q y) := by
  rw [jet_numerator_eq hy]
  exact mul_nonneg_iff_of_pos_left (pow_pos (reciprocal_pos (e8Q_pos hy)) 4)

theorem ratio_monotone_iff_curvature_nonneg :
    MonotoneOn ratio (Ioi 0) ↔ ∀ u : ℝ, 0 < u → 0 ≤ curvature u := by
  constructor
  · intro hm u hu
    have hd := hm.derivWithin_nonneg (x := u)
    rw [derivWithin_of_mem_nhds (Ioi_mem_nhds hu), deriv_ratio hu] at hd
    exact (mul_nonneg_iff_of_pos_left (reciprocal_pos hu)).mp hd
  · intro hn
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · exact fun u hu => (hasDerivAt_ratio hu).continuousAt.continuousWithinAt
    · intro u hu
      exact (hasDerivAt_ratio (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu' : 0 < u := interior_subset hu
      rw [deriv_ratio hu']
      exact mul_nonneg (reciprocal_pos hu').le (hn u hu')

theorem reciprocal_convex_iff_ratio_monotone :
    ConvexOn ℝ (Ioi 0) reciprocal ↔ MonotoneOn ratio (Ioi 0) := by
  constructor
  · intro hc a ha b hb hab
    have hm := hc.monotoneOn_deriv
      (fun u hu => (hasDerivAt_reciprocal hu).differentiableAt)
    simpa only [deriv_reciprocal ha, deriv_reciprocal hb] using hm ha hb hab
  · intro hm
    apply MonotoneOn.convexOn_of_deriv (convex_Ioi 0)
    · exact fun u hu => (hasDerivAt_reciprocal hu).continuousAt.continuousWithinAt
    · intro u hu
      exact (hasDerivAt_reciprocal (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro a ha b hb hab
      rw [deriv_reciprocal (interior_subset ha), deriv_reciprocal (interior_subset hb)]
      exact hm (interior_subset ha) (interior_subset hb) hab

theorem jet_numerator_nonnegative_iff_curvature_nonneg :
    E8LogDerivativeJetNumeratorNonnegative ↔
      ∀ u : ℝ, 0 < u → 0 ≤ curvature u := by
  constructor
  · intro hn u hu
    have hy : e8Theta u ∈ e8SlopeRange := ⟨u, hu, rfl⟩
    have hc := (jet_numerator_nonneg_iff hy).mp (hn _ hy)
    simpa only [e8Q_e8Theta hu] using hc
  · intro hn y hy
    exact (jet_numerator_nonneg_iff hy).mpr (hn _ (e8Q_pos hy))

/-- A complete equivalence: reciprocal convexity is exactly the existing
numerator certificate, not a stronger substitute. -/
theorem jet_numerator_nonnegative_iff_reciprocal_convex :
    E8LogDerivativeJetNumeratorNonnegative ↔ ConvexOn ℝ (Ioi 0) reciprocal := by
  rw [reciprocal_convex_iff_ratio_monotone, ratio_monotone_iff_curvature_nonneg]
  exact jet_numerator_nonnegative_iff_curvature_nonneg

theorem stable_numerator_nonnegative_iff_ratio_monotone :
    E8StableLogDerivativeJetNumeratorNonnegative ↔ MonotoneOn ratio (Ioi 0) := by
  rw [ratio_monotone_iff_curvature_nonneg,
    ← jet_numerator_nonnegative_iff_curvature_nonneg]
  constructor
  · exact e8LogDerivativeJetNumeratorNonnegative_of_stable
  · intro h a ha
    apply h
    exact ⟨Certificates.E8TAxisStableScalar.X a,
      Certificates.E8TAxisStableScalar.X_pos ha,
      Certificates.E8TAxisStableScalar.e8Theta_X ha⟩

/-- Reuses the checked derivative-monotonicity and scalar-shift owners. -/
theorem largeSStructure_of_ratio_monotone (hm : MonotoneOn ratio (Ioi 0)) :
    E8LargeSStructure :=
  e8LargeSStructure_of_stable_jet_numerator
    (stable_numerator_nonnegative_iff_ratio_monotone.mpr hm)

theorem largeSStructure_of_reciprocal_convex
    (hc : ConvexOn ℝ (Ioi 0) reciprocal) : E8LargeSStructure :=
  largeSStructure_of_ratio_monotone (reciprocal_convex_iff_ratio_monotone.mp hc)

theorem largeS_of_ratio_monotone (hm : MonotoneOn ratio (Ioi 0)) :
    E8PositiveOn (fun s _ => (63 / 20 : ℝ) ≤ s) :=
  e8_largeS_of_structure (largeSStructure_of_ratio_monotone hm)

#print axioms hasDerivAt_reciprocal
#print axioms hasDerivAt_ratio
#print axioms jet_numerator_eq
#print axioms jet_numerator_nonneg_iff
#print axioms ratio_monotone_iff_curvature_nonneg
#print axioms reciprocal_convex_iff_ratio_monotone
#print axioms jet_numerator_nonnegative_iff_curvature_nonneg
#print axioms jet_numerator_nonnegative_iff_reciprocal_convex
#print axioms stable_numerator_nonnegative_iff_ratio_monotone
#print axioms largeSStructure_of_ratio_monotone
#print axioms largeSStructure_of_reciprocal_convex
#print axioms largeS_of_ratio_monotone

end GeneralCK.E8RatioMonotonicity

end


