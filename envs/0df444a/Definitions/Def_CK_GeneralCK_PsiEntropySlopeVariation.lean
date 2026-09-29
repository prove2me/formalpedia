-- Prove2me | Definitions.Def_CK_GeneralCK_PsiEntropySlopeVariation
-- name    : CK_GeneralCK_PsiEntropySlopeVariation
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T08:07:04.691245+00:00
-- url     : https://prove2.me/theorems/bc26f374-69c1-44ba-9687-de29aba96bcd
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiEntropySlopeVariation` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiEntropySlopeVariation` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiEntropySlopeVariation` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiEntropySlopeVariation (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiEntropySlopeVariation.lean)

import Definitions.Def_CK_GeneralCK_EntropyCurvatureReduction
import Definitions.Def_CK_GeneralCK_PureGapHalfMeanAnalytic

-- ===== source module GeneralCK.PsiEntropySlopeVariation =====
section

/-!
# Radius variation of the entropy slope

For a fixed entropy in `(0,1)`, the entropy derivative of `radialPhi`
increases with radius at a rate between zero and `13/(6E)`.  The reverse
mixed derivative is proved directly from the perspective formula, rather
than assuming an interchange of derivatives.  The variation estimate
includes radius zero, using the smooth even extension of the radial term.
-/

namespace GeneralCK.PsiEntropySlopeVariation

open Set Filter

/-- The radius derivative of the entropy slope of the perspective term. -/
theorem hasDerivAt_deriv_F_entropy_radius {r E : ℝ}
    (hr : 0 < r) (hE : 0 < E) :
    HasDerivAt (fun z => deriv (F z) E)
      (-(r / E) * deriv (deriv (fun z => F z E)) r) r := by
  have hunit := (hasDerivAt_F_radius (h := 1) (div_pos hr hE)
    (by norm_num)).differentiableAt.hasDerivAt
  have hunit2 := (hasDerivAt_deriv_F_radius (h := 1) (div_pos hr hE)
    (by norm_num)).differentiableAt.hasDerivAt
  have hratio := (hasDerivAt_id r).div_const E
  have hcalc := (hunit.comp r hratio).sub (hratio.mul (hunit2.comp r hratio))
  have heq : (fun z => deriv (F z) E) =ᶠ[nhds r]
      (fun z => F (z / E) 1 - (z / E) * deriv (fun u => F u 1) (z / E)) := by
    filter_upwards [Ioi_mem_nhds hr] with z hz
    exact deriv_F_entropy hz hE
  convert! hcalc.congr_of_eventuallyEq heq using 1
  rw [deriv2_F_radius_normalize hr hE]
  dsimp only [id_eq, Function.comp_apply]
  ring

/-- The mixed derivative in the order needed for entropy-split coupling. -/
theorem hasDerivAt_radialPhi_entropySlope {r E : ℝ}
    (hr : 0 < r) (hE : 0 < E) (hE1 : E < 1) :
    HasDerivAt (fun z => deriv (radialPhi z) E)
      ((r / E) * deriv (deriv (fun z => F z E)) r) r := by
  have hcalc := (hasDerivAt_deriv_F_entropy_radius hr hE).const_sub (deriv eta E)
  have heq : (fun z => deriv (radialPhi z) E) =ᶠ[nhds r]
      (fun z => deriv eta E - deriv (F z) E) := by
    filter_upwards [Ioi_mem_nhds hr] with z hz
    exact (EntropyCurvature.hasDerivAt_radialPhi_entropy hz hE hE1).deriv
  convert! hcalc.congr_of_eventuallyEq heq using 1
  ring

theorem radialPhi_entropySlope_derivative_bounds {r E : ℝ}
    (hr : 0 < r) (hE : 0 < E) (hE1 : E < 1) :
    0 ≤ deriv (fun z => deriv (radialPhi z) E) r ∧
      deriv (fun z => deriv (radialPhi z) E) r ≤ 13 / (6 * E) := by
  rw [(hasDerivAt_radialPhi_entropySlope hr hE hE1).deriv]
  constructor
  · exact mul_nonneg (div_pos hr hE).le (deriv2_F_radius_nonneg hr hE)
  · have h := mul_le_mul_of_nonneg_left (global_mixed_derivative_bound hr hE)
      (show 0 ≤ 1 / E by positivity)
    convert! h using 1 <;> ring

private theorem deriv_F_radius_eq_evenRadial {r : ℝ} (hr : 0 < r) :
    deriv (fun z => F z 1) r = deriv (HalfMeanAnalytic.evenRadial 1) r := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds hr] with z hz
  rw [HalfMeanAnalytic.evenRadial_eq_abs (by norm_num : (0 : ℝ) < 1),
    abs_of_pos hz]

/-- A smooth expression for the entropy slope on the nonnegative radius
axis, including its value at zero. -/
theorem radialPhi_entropySlope_eq_evenRadial {r E : ℝ}
    (hr : 0 ≤ r) (hE : 0 < E) (hE1 : E < 1) :
    deriv (radialPhi r) E = deriv eta E -
      (HalfMeanAnalytic.evenRadial 1 (r / E) -
        (r / E) * deriv (HalfMeanAnalytic.evenRadial 1) (r / E)) := by
  rcases hr.eq_or_lt with he | hp
  · rw [← he, EntropyCurvature.radialPhi_zero]
    simp [HalfMeanAnalytic.evenRadial]
  · rw [(EntropyCurvature.hasDerivAt_radialPhi_entropy hp hE hE1).deriv,
      deriv_F_entropy hp hE, deriv_F_radius_eq_evenRadial (div_pos hp hE),
      HalfMeanAnalytic.evenRadial_eq_abs (by norm_num : (0 : ℝ) < 1),
      abs_of_pos (div_pos hp hE)]

/-- Right continuity at radius zero; no differentiability assertion for the
zero-filled radial function at zero is needed. -/
theorem radialPhi_entropySlope_continuousWithinAt_zero {E : ℝ}
    (hE : 0 < E) (hE1 : E < 1) :
    ContinuousWithinAt (fun r => deriv (radialPhi r) E) (Ici 0) 0 := by
  let g : ℝ → ℝ := fun r => deriv eta E -
    (HalfMeanAnalytic.evenRadial 1 (r / E) -
      (r / E) * deriv (HalfMeanAnalytic.evenRadial 1) (r / E))
  have hratio : ContinuousAt (fun r : ℝ => r / E) 0 :=
    continuousAt_id.div_const E
  have hval : ContinuousAt (fun r : ℝ => HalfMeanAnalytic.evenRadial 1 (r / E)) 0 :=
    (HalfMeanAnalytic.hasDerivAt_evenRadial 1 (0 / E)).continuousAt.comp
      (f := fun r : ℝ => r / E) hratio
  have hder0 : ContinuousAt (deriv (HalfMeanAnalytic.evenRadial 1)) (0 / E) := by
    simpa using (HalfMeanAnalytic.hasDerivAt_deriv_evenRadial_zero
      (by norm_num : (0 : ℝ) < 1)).continuousAt
  have hder : ContinuousAt
      (fun r : ℝ => deriv (HalfMeanAnalytic.evenRadial 1) (r / E)) 0 :=
    hder0.comp (f := fun r : ℝ => r / E) hratio
  have hg : ContinuousAt g 0 := continuousAt_const.sub (hval.sub (hratio.mul hder))
  apply hg.continuousWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact radialPhi_entropySlope_eq_evenRadial hr hE hE1
  · exact radialPhi_entropySlope_eq_evenRadial le_rfl hE hE1

theorem radialPhi_entropySlope_continuousOn {E : ℝ}
    (hE : 0 < E) (hE1 : E < 1) :
    ContinuousOn (fun r => deriv (radialPhi r) E) (Ici 0) := by
  intro r hr
  change 0 ≤ r at hr
  rcases hr.eq_or_lt with he | hp
  · rw [← he]
    exact radialPhi_entropySlope_continuousWithinAt_zero hE hE1
  · exact (hasDerivAt_radialPhi_entropySlope hp hE hE1).continuousAt.continuousWithinAt

/-- The exact radius variation estimate used by the active-psi entropy
split. There is no upper bound on radius and no entropy-cap premise. -/
theorem radialPhi_entropySlope_variation {E r0 r1 : ℝ}
    (hE : 0 < E) (hE1 : E < 1) (hr0 : 0 ≤ r0) (horder : r0 ≤ r1) :
    0 ≤ deriv (radialPhi r1) E - deriv (radialPhi r0) E ∧
      deriv (radialPhi r1) E - deriv (radialPhi r0) E ≤
        13 / (6 * E) * (r1 - r0) := by
  rcases horder.eq_or_lt with he | hlt
  · simp [he]
  let f : ℝ → ℝ := fun r => deriv (radialPhi r) E
  have hcont : ContinuousOn f (Icc r0 r1) :=
    (radialPhi_entropySlope_continuousOn hE hE1).mono (fun _ hx => hr0.trans hx.1)
  have hdiff : DifferentiableOn ℝ f (Ioo r0 r1) := by
    intro r hr
    exact (hasDerivAt_radialPhi_entropySlope (hr0.trans_lt hr.1) hE hE1).differentiableAt.differentiableWithinAt
  obtain ⟨r, hr, hder⟩ := exists_deriv_eq_slope f hlt hcont hdiff
  have hb := radialPhi_entropySlope_derivative_bounds (hr0.trans_lt hr.1) hE hE1
  change 0 ≤ deriv f r ∧ deriv f r ≤ 13 / (6 * E) at hb
  rw [hder] at hb
  constructor
  · have hn := (le_div_iff₀ (sub_pos.mpr hlt)).mp hb.1
    simpa only [zero_mul] using hn
  · exact (div_le_iff₀ (sub_pos.mpr hlt)).mp hb.2

#print axioms hasDerivAt_deriv_F_entropy_radius
#print axioms hasDerivAt_radialPhi_entropySlope
#print axioms radialPhi_entropySlope_variation

end GeneralCK.PsiEntropySlopeVariation

end


