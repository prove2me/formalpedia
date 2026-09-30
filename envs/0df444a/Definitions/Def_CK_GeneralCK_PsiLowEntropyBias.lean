-- Prove2me | Definitions.Def_CK_GeneralCK_PsiLowEntropyBias
-- name    : CK_GeneralCK_PsiLowEntropyBias
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:02:36.413328+00:00
-- url     : https://prove2.me/theorems/1c43ec03-8193-4454-b67f-5c3faf62f53c
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiLowEntropyBias` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiLowEntropyBias` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiLowEntropyBias` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiLowEntropyBias (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiLowEntropyBias.lean)

import Definitions.Def_CK_GeneralCK_PsiParentPhiFloor
import Definitions.Def_CK_GeneralCK_PsiParentDominance

-- ===== source module GeneralCK.PsiLowEntropyBias =====
section

/-! # Active low-entropy parents have small bias

A dyadic entropy witness excludes the intermediate bias interval. The
checked five-leaf cover, now with its analytic parent floor proved, handles
larger bias. Thus all active parents in the residual low-entropy domain
satisfy the factor-eight small-bias bound.
-/

namespace GeneralCK.PsiLowEntropyBias
open Set

theorem entropy_dyadic : H (1 / 2048 : ℝ) ≤ 1 / 140 := by
  have hL : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog : Real.log ((1 / 2048 : ℝ)⁻¹) = 11 * Real.log 2 := by
    norm_num
    rw [show (2048 : ℝ) = 2 ^ (11 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hupper : H (1 / 2048 : ℝ) * Real.log 2 ≤
      (1 / 2048) * Real.log ((1 / 2048 : ℝ)⁻¹) + 1 / 2048 := by
    have hc : (0 : ℝ) < 1 - 1 / 2048 := by norm_num
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hc)
    have hm := mul_le_mul_of_nonneg_left h hc.le
    norm_num at hm
    rw [H, div_mul_cancel₀ _ log_two_pos.ne', Real.binEntropy]
    norm_num
    linarith
  rw [hlog] at hupper
  nlinarith

theorem J_dyadic : J (1 / 2048 : ℝ) ≤ 11 := by
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2047)
    (by norm_num : (2047 : ℝ) ≤ 2048)
  rw [show (2048 : ℝ) = 2 ^ (11 : ℕ) by norm_num, Real.log_pow] at hlog
  norm_num at hlog
  unfold J
  norm_num
  exact (div_le_iff₀ log_two_pos).mpr (by linarith)

theorem medium_bias_psi_le {q E : ℝ} (hq : 1 / 10 ≤ q) (hq1 : q ≤ 2 / 5)
    (hE : 0 < E) (hEs : E ≤ 1 / 1000000) : psi ((1 - q) / 2) E ≤ 11 := by
  let C := 1 - H ((1 - q) / 2)
  have hC : 0 ≤ C := sub_nonneg.mpr (H_le_one _)
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hClow : 1 / 140 ≤ C := by
    have h := SmallMean.Cn_ge_half_sq (show 0 ≤ q by linarith) (by linarith : q ≤ 1)
    change q ^ 2 / 2 ≤ Real.log 2 * C at h
    have hm := mul_le_mul_of_nonneg_right hL hC
    nlinarith [sq_nonneg (q - 1 / 10)]
  have hphys : E + C ≤ 1 := by
    have hh := PsiParentPhiFloor.entropy_chord
      (show 0 ≤ (1 - q) / 2 by linarith) (show (1 - q) / 2 ≤ 1 / 2 by linarith)
    dsimp [C]
    linarith
  have hh := LowEntropyLeaf.eta_le_of_witness (E + C) (1 / 2048) 11
    (by linarith) hphys (by norm_num) (by norm_num)
    (by linarith [entropy_dyadic]) J_dyadic (by norm_num)
  have heq : psi ((1 - q) / 2) E = eta (E + C) := by
    unfold psi C
    congr 1
    ring
  rw [heq]
  linarith

theorem logarithmic_floor {E : ℝ} (hE : 0 < E) (hEs : E ≤ 1 / 1000000) :
    20 ≤ Real.log ((2 - E) / E) / Real.log 2 := by
  have hratio : (2 : ℝ) ^ (20 : ℕ) ≤ (2 - E) / E := by
    apply (le_div_iff₀ hE).mpr
    norm_num
    linarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (20 : ℕ)) hratio
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ log_two_pos).mpr (by norm_num at hlog ⊢; exact hlog)

theorem medium_bias_parent_dominance {q E : ℝ} (hq : 1 / 10 ≤ q) (hq1 : q ≤ 2 / 5)
    (hE : 0 < E) (hEs : E ≤ 1 / 1000000) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  have hp := medium_bias_psi_le hq hq1 hE hEs
  have hf := PsiParentPhiFloor.phi_lower (by linarith : 0 < q) hE (by linarith)
  have hl := mul_le_mul_of_nonneg_left (logarithmic_floor hE hEs)
    (show 0 ≤ 1 - q - E by linarith)
  nlinarith only [hp, hf, hl, hq1, hEs]

theorem active_bias_lt_tenth {q E : ℝ} (hq1 : q ≤ 15 / 16)
    (hE : 0 < E) (hEs : E ≤ 1 / 1000000)
    (hactive : phi ((1 - q) / 2) E ≤ psi ((1 - q) / 2) E) : q < 1 / 10 := by
  by_contra hn
  have hq : 1 / 10 ≤ q := le_of_not_gt hn
  by_cases hq2 : q ≤ 2 / 5
  · exact (not_lt_of_ge hactive) (medium_bias_parent_dominance hq hq2 hE hEs)
  · have h := PsiParentPhiFloor.high_bias_parent_dominance (lt_of_not_ge hq2).le hq1 hE hEs
    linarith

theorem active_bias_lt_eight_entropy {q E : ℝ} (hq1 : q ≤ 15 / 16)
    (hE : 0 < E) (hEs : E ≤ 1 / 1000000)
    (hactive : phi ((1 - q) / 2) E ≤ psi ((1 - q) / 2) E) : q < 8 * E := by
  have hqsmall := active_bias_lt_tenth hq1 hE hEs hactive
  by_contra hn
  have hr : 8 * E ≤ q := le_of_not_gt hn
  exact (not_lt_of_ge hactive) (PsiParentDominance.parent_dominance_ratio8_small_bias
    hE (by linarith) hqsmall.le hr)

end GeneralCK.PsiLowEntropyBias

#print axioms GeneralCK.PsiLowEntropyBias.medium_bias_parent_dominance
#print axioms GeneralCK.PsiLowEntropyBias.active_bias_lt_eight_entropy

end


