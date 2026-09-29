-- Prove2me | Definitions.Def_CK_GeneralCK_PsiEndpointPlaneCoefficients
-- name    : CK_GeneralCK_PsiEndpointPlaneCoefficients
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:19:19.504981+00:00
-- url     : https://prove2.me/theorems/7ef534d0-c4cc-40d3-a521-b3d759d40585
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiEndpointPlaneCoefficients` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiEndpointPlaneCoefficients` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiEndpointPlaneCoefficients` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiEndpointPlaneCoefficients (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiEndpointPlaneCoefficients.lean)

import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneQuotientDefs
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

-- ===== source module GeneralCK.PsiEndpointPlaneCoefficients =====
section

/-! Positive coefficients for the strict cross-half endpoint contact. -/

namespace GeneralCK.PsiEndpointPlane

open Set

private noncomputable def entropyAsymmetry (z : ℝ) : ℝ :=
  Real.negMulLog z - Real.negMulLog (1 - z)

private theorem entropyAsymmetry_hasDerivAt {z : ℝ} (hz : 0 < z) (hz' : z < 1) :
    HasDerivAt entropyAsymmetry (-Real.log (z * (1 - z)) - 2) z := by
  have hc : 0 < 1 - z := by linarith
  have h := (Real.hasDerivAt_negMulLog hz.ne').sub
    ((Real.hasDerivAt_negMulLog hc.ne').comp z ((hasDerivAt_id z).const_sub 1))
  convert! h using 1
  rw [Real.log_mul hz.ne' hc.ne']
  ring

private theorem entropyAsymmetry_strictConcave :
    StrictConcaveOn ℝ (Icc 0 (1 / 2)) entropyAsymmetry := by
  have hcont : Continuous entropyAsymmetry :=
    Real.continuous_negMulLog.sub
      (Real.continuous_negMulLog.comp (continuous_const.sub continuous_id))
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Icc 0 (1 / 2)) hcont.continuousOn
  intro a ha b hb hab
  rw [interior_Icc] at ha hb
  rw [(entropyAsymmetry_hasDerivAt ha.1 (by linarith [ha.2])).deriv,
    (entropyAsymmetry_hasDerivAt hb.1 (by linarith [hb.2])).deriv]
  have hp : 0 < a * (1 - a) := mul_pos ha.1 (by linarith [ha.2])
  have hprod : a * (1 - a) < b * (1 - b) := by
    have := mul_pos (sub_pos.mpr hab) (show 0 < 1 - a - b by linarith [ha.2, hb.2])
    nlinarith only [this]
  have := Real.log_lt_log hp hprod
  linarith

/-- On the lower half of the unit interval, the entropy contribution of `z`
is strictly larger than that of its complement. -/
theorem negMulLog_gt_complement {z : ℝ} (hz : 0 < z) (hz' : z < 1 / 2) :
    Real.negMulLog (1 - z) < Real.negMulLog z := by
  have h := entropyAsymmetry_strictConcave.2
    (show (0 : ℝ) ∈ Icc 0 (1 / 2) by norm_num)
    (show (1 / 2 : ℝ) ∈ Icc 0 (1 / 2) by norm_num)
    (show (0 : ℝ) ≠ 1 / 2 by norm_num)
    (show 0 < 1 - 2 * z by linarith)
    (show 0 < 2 * z by linarith)
    (show (1 - 2 * z) + 2 * z = 1 by ring)
  have harg : (1 - 2 * z) * (0 : ℝ) + 2 * z * (1 / 2) = z := by ring
  simp only [smul_eq_mul, harg] at h
  have hzero : entropyAsymmetry 0 = 0 := by simp [entropyAsymmetry]
  have hhalf : entropyAsymmetry (1 / 2) = 0 := by norm_num [entropyAsymmetry]
  rw [hzero, hhalf] at h
  dsimp [entropyAsymmetry] at h
  linarith

private theorem positive_linear_system {a b c d p q : ℝ}
    (hdet : 0 < a * d - b * c) (hA : 0 < p * d - b * q)
    (hB : 0 < a * q - c * p) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ a * A + b * B = p ∧ c * A + d * B = q := by
  refine ⟨(p * d - b * q) / (a * d - b * c),
    (a * q - c * p) / (a * d - b * c), div_pos hA hdet, div_pos hB hdet, ?_, ?_⟩
  all_goals
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
    apply (div_eq_iff hdet.ne').2
    ring

/-- The matrix specifying the endpoint plane has a strictly positive solution
at every strict cross-half contact. This is a proved existence statement, not
a hypothesis about the global supporting inequality. -/
theorem exists_positive_contact_coefficients_uv {u v : ℝ}
    (hu : 0 < u) (hu' : u < 1 / 2) (hv : 0 < v) (hv' : v < 1 / 2) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      contactLevel1 A B u (1 - v) = 0 ∧ contactLevel0 A B u (1 - v) = 0 := by
  have hu1 : u < 1 := by linarith
  have hv1 : v < 1 := by linarith
  have huc : 0 < 1 - u := by linarith
  have hvc : 0 < 1 - v := by linarith
  have hcu : 1 - u < 1 := by linarith
  have hcv : 1 - v < 1 := by linarith
  let a := -Real.log u
  let b := -Real.log (1 - v)
  let c := -Real.log (1 - u)
  let d := -Real.log v
  have ha : 0 < a := neg_pos.mpr (Real.log_neg hu hu1)
  have hb : 0 < b := neg_pos.mpr (Real.log_neg hvc hcv)
  have hc : 0 < c := neg_pos.mpr (Real.log_neg huc hcu)
  have hd : 0 < d := neg_pos.mpr (Real.log_neg hv hv1)
  have hca : c < a := by
    dsimp [c, a]
    have := Real.log_lt_log hu (show u < 1 - u by linarith)
    linarith
  have hbd : b < d := by
    dsimp [b, d]
    have := Real.log_lt_log hv (show v < 1 - v by linarith)
    linarith
  have hdet : 0 < a * d - b * c := by
    have h1 := mul_lt_mul_of_pos_right hca hd
    have h2 := mul_lt_mul_of_pos_left hbd hc
    nlinarith only [h1, h2]
  have heu : (1 - u) * c < u * a := by
    have h := negMulLog_gt_complement hu hu'
    dsimp [Real.negMulLog, a, c] at *
    nlinarith only [h]
  have hev : (1 - v) * b < v * d := by
    have h := negMulLog_gt_complement hv hv'
    dsimp [Real.negMulLog, b, d] at *
    nlinarith only [h]
  have hAbase : u * (1 - v) * b < (1 - u) * v * d := by
    have h1 := mul_lt_mul_of_pos_left hev huc
    have h2 := mul_pos (show 0 < 1 - 2 * u by linarith) (mul_pos hvc hb)
    nlinarith only [h1, h2]
  have hBbase : (1 - u) * v * c < u * (1 - v) * a := by
    have h1 := mul_lt_mul_of_pos_left heu hvc
    have h2 := mul_pos (show 0 < 1 - 2 * v by linarith) (mul_pos huc hc)
    nlinarith only [h1, h2]
  have hgap : 0 < 1 - u - v := by linarith
  have hsq : 0 < (1 - u - v) ^ 2 := sq_pos_of_pos hgap
  have hpden : 0 < 2 * u * (1 - v) := by positivity
  have hqden : 0 < 2 * (1 - u) * v := by positivity
  let p := (1 - u - v) ^ 2 / (2 * u * (1 - v))
  let q := (1 - u - v) ^ 2 / (2 * (1 - u) * v)
  have hA : 0 < p * d - b * q := by
    apply sub_pos.mpr
    dsimp [p, q]
    rw [← mul_div_assoc, div_mul_eq_mul_div]
    apply (div_lt_div_iff₀ hqden hpden).2
    have h := mul_pos hsq (sub_pos.mpr hAbase)
    nlinarith only [h]
  have hB : 0 < a * q - c * p := by
    apply sub_pos.mpr
    dsimp [p, q]
    rw [← mul_div_assoc, ← mul_div_assoc]
    apply (div_lt_div_iff₀ hpden hqden).2
    have h := mul_pos hsq (sub_pos.mpr hBbase)
    nlinarith only [h]
  obtain ⟨A, B, hApos, hBpos, hlevel1, hlevel0⟩ := positive_linear_system hdet hA hB
  refine ⟨A, B, hApos, hBpos, ?_, ?_⟩
  · have hsqeq : (u - (1 - v)) ^ 2 = (1 - u - v) ^ 2 := by ring
    simp only [contactLevel1, hsqeq]
    dsimp [a, b, p] at hlevel1
    nlinarith only [hlevel1]
  · have hsqeq : (u - (1 - v)) ^ 2 = (1 - u - v) ^ 2 := by ring
    have hcomp : 1 - (1 - v) = v := by ring
    simp only [contactLevel0, hsqeq, hcomp]
    dsimp [c, d, q] at hlevel0
    nlinarith only [hlevel0]

theorem exists_positive_contact_coefficients {x y : ℝ}
    (hx : 0 < x) (hx' : x < 1 / 2) (hy : 1 / 2 < y) (hy' : y < 1) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      contactLevel1 A B x y = 0 ∧ contactLevel0 A B x y = 0 := by
  have hv : 0 < 1 - y := by linarith
  have hv' : 1 - y < 1 / 2 := by linarith
  simpa only [sub_sub_cancel] using exists_positive_contact_coefficients_uv hx hx' hv hv'

#print axioms negMulLog_gt_complement
#print axioms exists_positive_contact_coefficients

end GeneralCK.PsiEndpointPlane

end


