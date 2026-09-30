-- Prove2me | Definitions.Def_CK_GeneralCK_PsiSameRatioTail14Entropy425
-- name    : CK_GeneralCK_PsiSameRatioTail14Entropy425
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:25:11.888129+00:00
-- url     : https://prove2.me/theorems/4a8fbe00-1b85-46c1-af70-85c75bf4acb2
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiSameRatioTail14Entropy425` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiSameRatioTail14Entropy425` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiSameRatioTail14Entropy425` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiSameRatioTail14Entropy425 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiSameRatioTail14Entropy425.lean)

import Definitions.Def_CK_GeneralCK_PsiSameRatioTail14SmallB

-- ===== source module GeneralCK.PsiSameRatioTail14Entropy425 =====
section

/-! A sharper rational entropy anchor for the active-Psi ratio-fourteen
same-side strip. It uses an exact integer-power logarithm comparison and
the checked antitonicity of the entropy derivative. -/

namespace GeneralCK.PsiSameRatioTail14Entropy425

open Set
set_option exponentiation.threshold 1024
set_option maxRecDepth 4096

theorem entropy_fifth_le_181_250 :
    H (1 / 5) ≤ (181 / 250 : ℝ) := by
  have hpow : (5 : ℝ) ^ (250 : ℕ) ≤ (2 : ℝ) ^ (581 : ℕ) := by
    exact_mod_cast (show (5 : ℕ) ^ (250 : ℕ) ≤ (2 : ℕ) ^ (581 : ℕ) by decide)
  have hlog := Real.log_le_log
    (by positivity : (0 : ℝ) < (5 : ℝ) ^ (250 : ℕ)) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog
  have he := Certificates.SmallMean.entropy_log_identity (1 / 5)
  have h5 : -Real.log (1 / 5 : ℝ) = Real.log 5 := by
    rw [show (1 / 5 : ℝ) = (5 : ℝ)⁻¹ by norm_num, Real.log_inv, neg_neg]
  have h4 : -Real.log (1 - (1 / 5 : ℝ)) = Real.log 5 - 2 * Real.log 2 := by
    rw [show 1 - (1 / 5 : ℝ) = (4 : ℝ) / 5 by norm_num,
      Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)]
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    ring
  rw [h5, h4] at he
  have hbound : H (1 / 5) * Real.log 2 ≤ (181 / 250) * Real.log 2 := by
    nlinarith only [he, hlog]
  have hbound' : Real.log 2 * H (1 / 5) ≤ Real.log 2 * (181 / 250) := by
    simpa only [mul_comm] using hbound
  exact (mul_le_mul_iff_right₀ log_two_pos).mp hbound'

theorem J_fifth_eq_two : J (1 / 5 : ℝ) = 2 := by
  unfold J
  rw [show (1 - (1 / 5 : ℝ)) / (1 / 5) = 4 by norm_num]
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
  field_simp [log_two_pos.ne']
  norm_num

theorem entropy_213_le_three_quarters :
    H (213 / 1000) ≤ (3 / 4 : ℝ) := by
  have hcont : ContinuousOn H (Icc (1 / 5 : ℝ) (213 / 1000)) :=
    H_continuous.continuousOn
  have hdiff : DifferentiableOn ℝ H
      (interior (Icc (1 / 5 : ℝ) (213 / 1000))) := by
    intro x hx
    have hx' : x ∈ Ioo (1 / 5 : ℝ) (213 / 1000) := by
      simpa only [interior_Icc] using hx
    exact (Comparison.hasDerivAt_H (by linarith [hx'.1])
      (by linarith [hx'.2])).differentiableAt.differentiableWithinAt
  have hderiv : ∀ x ∈ interior (Icc (1 / 5 : ℝ) (213 / 1000)),
      deriv H x ≤ 2 := by
    intro x hx
    have hx' : x ∈ Ioo (1 / 5 : ℝ) (213 / 1000) := by
      simpa only [interior_Icc] using hx
    rw [(Comparison.hasDerivAt_H (by linarith [hx'.1])
      (by linarith [hx'.2])).deriv]
    rw [← J_fifth_eq_two]
    exact J_antitone (by norm_num : (0 : ℝ) < 1 / 5)
      (by linarith [hx'.2] : x ≤ 1 / 2) hx'.1.le
  have hinc := (convex_Icc (1 / 5 : ℝ) (213 / 1000)).image_sub_le_mul_sub_of_deriv_le
    hcont hdiff hderiv (1 / 5) (by norm_num) (213 / 1000)
    (by norm_num) (by norm_num : (1 / 5 : ℝ) ≤ 213 / 1000)
  linarith [entropy_fifth_le_181_250]

#print axioms entropy_fifth_le_181_250
#print axioms entropy_213_le_three_quarters

end GeneralCK.PsiSameRatioTail14Entropy425

end


