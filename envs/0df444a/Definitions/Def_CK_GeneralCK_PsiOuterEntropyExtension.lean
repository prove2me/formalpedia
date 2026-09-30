-- Prove2me | Definitions.Def_CK_GeneralCK_PsiOuterEntropyExtension
-- name    : CK_GeneralCK_PsiOuterEntropyExtension
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:06:25.485724+00:00
-- url     : https://prove2.me/theorems/0e6ef2d1-7c47-47f1-ace5-4cf78e2c3361
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiOuterEntropyExtension` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiOuterEntropyExtension` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiOuterEntropyExtension` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiOuterEntropyExtension (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiOuterEntropyExtension.lean)

import Definitions.Def_CK_GeneralCK_PsiModerateEntropy
import Definitions.Def_CK_GeneralCK_PsiParentPhiFloor

-- ===== source module GeneralCK.PsiOuterEntropyExtension =====
section

/-! # A larger low-entropy region for outer opposite means -/

namespace GeneralCK.PsiOuterEntropyExtension

theorem entropy_upper {p n : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hlog : Real.log p⁻¹ = n * Real.log 2) : H p ≤ (n + 2) * p := by
  have hL : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hc : 0 < 1 - p := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hc)
  have hm := mul_le_mul_of_nonneg_left h hc.le
  have hid : (1 - p) * ((1 - p)⁻¹ - 1) = p := by field_simp; ring
  rw [hid] at hm
  have hb : H p * Real.log 2 ≤ p * Real.log p⁻¹ + p := by
    rw [H, div_mul_cancel₀ _ log_two_pos.ne', Real.binEntropy]
    linarith only [hm]
  rw [hlog] at hb
  apply (mul_le_mul_iff_right₀ log_two_pos).mp
  nlinarith [mul_nonneg hp.le (show 0 ≤ 2 * Real.log 2 - 1 by linarith)]

theorem logit_upper {p n : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hlog : Real.log p⁻¹ = n * Real.log 2) : J p ≤ n := by
  have hratio : (1 - p) / p ≤ p⁻¹ := by
    rw [div_le_iff₀ hp]
    rw [inv_mul_cancel₀ hp.ne']
    linarith
  have h := Real.log_le_log (div_pos (sub_pos.mpr hp1) hp) hratio
  rw [hlog] at h
  exact (div_le_iff₀ log_two_pos).mpr h

theorem psi_dyadic_cap {q E p n l : ℝ}
    (hl : 0 ≤ l) (hlq : l ≤ q) (hq : q ≤ 1 / 2)
    (hE : 0 < E) (hEs : E ≤ 1 / 32768)
    (hp : 0 < p) (hph : p ≤ 1 / 2) (hn : 0 ≤ n)
    (hlog : Real.log p⁻¹ = n * Real.log 2)
    (hsmall : (n + 2) * p ≤ 5 * l ^ 2 / 7) :
    psi ((1 - q) / 2) E ≤ (1 - 2 * p) * n := by
  let C := 1 - H ((1 - q) / 2)
  have hq0 : 0 ≤ q := hl.trans hlq
  have hC : 0 ≤ C := sub_nonneg.mpr (H_le_one _)
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hClow : 5 * l ^ 2 / 7 ≤ C := by
    have h := SmallMean.Cn_ge_half_sq hq0 (by linarith : q ≤ 1)
    change q ^ 2 / 2 ≤ Real.log 2 * C at h
    have hm := mul_le_mul_of_nonneg_right hL hC
    have hs := mul_nonneg (sub_nonneg.mpr hlq) (show 0 ≤ q + l by linarith)
    nlinarith only [h, hm, hs]
  have hphys : E + C ≤ 1 := by
    have hh := PsiParentPhiFloor.entropy_chord
      (show 0 ≤ (1 - q) / 2 by linarith) (show (1 - q) / 2 ≤ 1 / 2 by linarith)
    dsimp [C]
    linarith
  have hh := LowEntropyLeaf.eta_le_of_witness (E + C) p n (by linarith) hphys hp hph
    ((entropy_upper hp (by linarith) hlog).trans (hsmall.trans (by linarith)))
    (logit_upper hp (by linarith) hlog) hn
  convert! hh using 1
  unfold psi C
  congr 1
  ring

theorem log_floor {E : ℝ} (hE : 0 < E) (hEs : E ≤ 1 / 32768) :
    15 ≤ Real.log ((2 - E) / E) / Real.log 2 := by
  have hratio : (2 : ℝ) ^ (15 : ℕ) ≤ (2 - E) / E := by
    apply (le_div_iff₀ hE).mpr
    norm_num
    linarith
  have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (15 : ℕ)) hratio
  rw [Real.log_pow] at h
  norm_num at h
  exact (le_div_iff₀ log_two_pos).mpr h

theorem parent_dominance {q E : ℝ} (hq0 : 1 / 10 ≤ q) (hq : q ≤ 1 / 2)
    (hE : 0 < E) (hEs : E ≤ 1 / 32768) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  have hf := PsiParentPhiFloor.phi_lower (by linarith : 0 < q) hE (by linarith)
  have hg := mul_le_mul_of_nonneg_left (log_floor hE hEs) (show 0 ≤ 1 - q - E by linarith)
  by_cases hq2 : q ≤ 1 / 5
  · have hp := psi_dyadic_cap (l := 1 / 10) (p := 1 / 2048) (n := 11)
      (by norm_num) hq0 hq hE hEs (by norm_num) (by norm_num) (by norm_num)
      (by norm_num; rw [show (2048 : ℝ) = 2 ^ (11 : ℕ) by norm_num, Real.log_pow]; norm_num)
      (by norm_num)
    nlinarith only [hp, hf, hg, hq2, hEs]
  · by_cases hq4 : q ≤ 2 / 5
    · have hp := psi_dyadic_cap (l := 1 / 5) (p := 1 / 512) (n := 9)
        (by norm_num) (lt_of_not_ge hq2).le hq hE hEs (by norm_num) (by norm_num) (by norm_num)
        (by norm_num; rw [show (512 : ℝ) = 2 ^ (9 : ℕ) by norm_num, Real.log_pow]; norm_num)
        (by norm_num)
      nlinarith only [hp, hf, hg, hq4, hEs]
    · have hp := psi_dyadic_cap (l := 2 / 5) (p := 1 / 128) (n := 7)
        (by norm_num) (lt_of_not_ge hq4).le hq hE hEs (by norm_num) (by norm_num) (by norm_num)
        (by norm_num; rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.log_pow]; norm_num)
        (by norm_num)
      nlinarith only [hp, hf, hg, hq, hEs]

theorem law_gap_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (ha : μ.a ≤ 1 / 10) (hb : 1 / 2 ≤ μ.b)
    (hEs : μ.meanEntropy ≤ 1 / 32768)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hq : 1 - μ.a - μ.b < 1 / 10 := by
    by_contra hn
    have hp := parent_dominance (le_of_not_gt hn)
      (by linarith [μ.a_interior.1] : 1 - μ.a - μ.b ≤ 1 / 2) hE hEs
    have heq : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
      unfold InteriorLaw.midpoint
      ring
    rw [heq] at hp
    exact (not_lt_of_ge hactive) hp
  exact PsiModerateEntropy.law_gap_le_cost_ceiling μ hsum (by linarith)
    (by linarith) hq.le hactive

end GeneralCK.PsiOuterEntropyExtension

#print axioms GeneralCK.PsiOuterEntropyExtension.parent_dominance
#print axioms GeneralCK.PsiOuterEntropyExtension.law_gap_le_cost

end


