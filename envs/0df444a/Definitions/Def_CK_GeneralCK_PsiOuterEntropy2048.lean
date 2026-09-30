-- Prove2me | Definitions.Def_CK_GeneralCK_PsiOuterEntropy2048
-- name    : CK_GeneralCK_PsiOuterEntropy2048
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:11:22.208045+00:00
-- url     : https://prove2.me/theorems/2b073dd2-3473-468c-ab83-e1e8a49dc51c
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiOuterEntropy2048` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiOuterEntropy2048` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiOuterEntropy2048` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiOuterEntropy2048 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiOuterEntropy2048.lean)

import Definitions.Def_CK_GeneralCK_PsiOuterEntropyExtension

-- ===== source module GeneralCK.PsiOuterEntropy2048 =====
section

/-!
# An analytic outer opposite owner through entropy 1/2048

The factor-eight parent exclusion extends to bias 1/8. Above that bias,
six elementary logarithm/entropy comparisons exclude the active parent.
The surviving low-bias laws use the retained-child endpoint theorem.
-/

namespace GeneralCK.PsiOuterEntropy2048
open Set

theorem logarithmic_eight_comparison {x : ℝ} (hx : 8 ≤ x) :
    Real.log x < 4 * Real.log (1 + 5 * x / 56) := by
  have hy : 0 ≤ x - 8 := by linarith
  have he : (1 + 5 * x / 56) ^ 4 - x =
      625 * (x - 8) ^ 4 / 9834496 +
      375 * (x - 8) ^ 3 / 76832 +
      675 * (x - 8) ^ 2 / 4802 +
      1919 * (x - 8) / 2401 + 1528 / 2401 := by ring
  have hp : 0 < (1 + 5 * x / 56) ^ 4 - x := by rw [he]; positivity
  have hh := Real.log_lt_log (by linarith : 0 < x)
    (show x < (1 + 5 * x / 56) ^ 4 by linarith)
  rw [Real.log_pow] at hh
  simpa using hh

theorem logarithmic_bias_scale {q x : ℝ} (hq : 0 ≤ q) (hqu : q ≤ 1 / 8)
    (hx : 0 ≤ x) :
    8 * q * Real.log (1 + 5 * x / 56) ≤ Real.log (1 + 5 * q * x / 7) := by
  have hh := strictConcaveOn_log_Ioi.concaveOn.2
    (show 0 < 1 + 5 * x / 56 by positivity)
    (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show 0 ≤ 8 * q by positivity) (show 0 ≤ 1 - 8 * q by linarith)
    (show 8 * q + (1 - 8 * q) = 1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hh
  convert! hh using 1
  congr 1
  ring

/-- Ratio-eight dominance on the enlarged bias interval, including both
upper faces. It uses no child-cap or finite-law assumption. -/
theorem parent_dominance_ratio8 {q E : ℝ} (hE : 0 < E)
    (hq : 0 < q) (hqu : q ≤ 1 / 8) (hratio : 8 * E ≤ q) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  let C := 1 - H ((1 - q) / 2)
  let x := q / E
  have hx : 8 ≤ x := (le_div_iff₀ hE).mpr hratio
  have hC : 0 ≤ C := sub_nonneg.mpr (H_le_one _)
  have hCup : C ≤ q ^ 2 := by
    have hh := H_gt_parabola (p := (1 - q) / 2) (by linarith) (by linarith)
    dsimp [C]
    nlinarith only [hh]
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have hh := Certificates.PilotData.log_two.2
    norm_num at hh
    linarith
  have hClow : 5 * q ^ 2 / 7 ≤ C := by
    have hh := SmallMean.Cn_ge_half_sq hq.le (by linarith : q ≤ 1)
    change q ^ 2 / 2 ≤ Real.log 2 * C at hh
    have hm := mul_le_mul_of_nonneg_right hL hC
    nlinarith only [hh, hm]
  have hphysical : E + C ≤ 1 := by
    have hs := mul_nonneg hq.le (show 0 ≤ 1 / 8 - q by linarith)
    nlinarith only [hCup, hs, hratio, hqu]
  have hgain := eta_increment_ge_linear_log hE hC hphysical
  have hlogratio : Real.log (1 + 5 * q * x / 7) ≤ Real.log (1 + C / E) := by
    apply Real.log_le_log (by dsimp [x]; positivity)
    have hh := div_le_div_of_nonneg_right hClow hE.le
    dsimp [x]
    convert! add_le_add_left hh 1 using 1 <;> ring
  have hscale := logarithmic_bias_scale hq.le hqu (show 0 ≤ x by linarith)
  have hpoly := logarithmic_eight_comparison hx
  have hF : F q E < eta E - eta (E + C) := by
    calc
      F q E ≤ 2 * q * Real.log x / Real.log 2 :=
        PsiParentDominance.F_le_logarithmic_ratio8 hq hE hratio
      _ < 8 * q * Real.log (1 + 5 * x / 56) / Real.log 2 := by
        apply div_lt_div_of_pos_right _ log_two_pos
        have hh := mul_lt_mul_of_pos_left hpoly (show 0 < 2 * q by positivity)
        nlinarith only [hh]
      _ ≤ Real.log (1 + 5 * q * x / 7) / Real.log 2 :=
        div_le_div_of_nonneg_right hscale log_two_pos.le
      _ ≤ Real.log (1 + C / E) / Real.log 2 :=
        div_le_div_of_nonneg_right hlogratio log_two_pos.le
      _ ≤ eta E - eta (E + C) := by linarith only [hgain, hC]
  unfold phi psi
  rw [show |1 - 2 * ((1 - q) / 2)| = q by
    rw [show 1 - 2 * ((1 - q) / 2) = q by ring, abs_of_pos hq]]
  have he : E + 1 - H ((1 - q) / 2) = E + C := by dsimp [C]; ring
  rw [he]
  linarith only [hF]

/-- Entropy and logit bounds require only an upper logarithm witness. -/
theorem entropy_logit_upper {p n : ℝ} (hp : 0 < p) (hpu : p < 1)
    (hlog : Real.log p⁻¹ ≤ n * Real.log 2) :
    H p ≤ (n + 3 / 2) * p ∧ J p ≤ n := by
  have hL : (2 / 3 : ℝ) ≤ Real.log 2 := by
    have hh := Certificates.PilotData.log_two.1
    norm_num at hh
    linarith
  have hc : 0 < 1 - p := by linarith
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hc)
  have hm := mul_le_mul_of_nonneg_left hl hc.le
  rw [show (1 - p) * ((1 - p)⁻¹ - 1) = p by field_simp; ring] at hm
  have hb : H p * Real.log 2 ≤ p * Real.log p⁻¹ + p := by
    rw [H, div_mul_cancel₀ _ log_two_pos.ne', Real.binEntropy]
    linarith only [hm]
  constructor
  · apply (mul_le_mul_iff_right₀ log_two_pos).mp
    have hh := mul_le_mul_of_nonneg_left hlog hp.le
    have hs := mul_nonneg hp.le (show 0 ≤ (3 / 2) * Real.log 2 - 1 by linarith)
    nlinarith only [hb, hh, hs]
  · have hr : (1 - p) / p ≤ p⁻¹ := by
      rw [div_le_iff₀ hp, inv_mul_cancel₀ hp.ne']
      linarith
    exact (div_le_iff₀ log_two_pos).mpr
      ((Real.log_le_log (div_pos hc hp) hr).trans hlog)

/-- A uniform rational anchor cap, valid at every entropy in the enlarged
outer range. The constant 18/25 comes from the checked bound log(2)≤25/36. -/
theorem psi_anchor_cap {q E p n l : ℝ}
    (hl : 0 ≤ l) (hlq : l ≤ q) (hq : q ≤ 1 / 2)
    (hE : 0 < E) (hEu : E ≤ 1 / 2048)
    (hp : 0 < p) (hph : p ≤ 1 / 2) (hn : 0 ≤ n)
    (hlog : Real.log p⁻¹ ≤ n * Real.log 2)
    (hsmall : (n + 3 / 2) * p ≤ (18 / 25) * l ^ 2) :
    psi ((1 - q) / 2) E ≤ (1 - 2 * p) * n := by
  let C := 1 - H ((1 - q) / 2)
  have hq0 : 0 ≤ q := hl.trans hlq
  have hC : 0 ≤ C := sub_nonneg.mpr (H_le_one _)
  have hL : Real.log 2 ≤ (25 / 36 : ℝ) := by
    have hh := Certificates.PilotData.log_two.2
    norm_num at hh
    linarith
  have hClow : (18 / 25) * l ^ 2 ≤ C := by
    have hh := SmallMean.Cn_ge_half_sq hq0 (by linarith : q ≤ 1)
    change q ^ 2 / 2 ≤ Real.log 2 * C at hh
    have hm := mul_le_mul_of_nonneg_right hL hC
    have hs := mul_nonneg (sub_nonneg.mpr hlq) (show 0 ≤ q + l by linarith)
    nlinarith only [hh, hm, hs]
  have hphys : E + C ≤ 1 := by
    have hh := PsiParentPhiFloor.entropy_chord
      (show 0 ≤ (1 - q) / 2 by linarith) (show (1 - q) / 2 ≤ 1 / 2 by linarith)
    dsimp [C]
    linarith
  obtain ⟨hentropy, hlogit⟩ := entropy_logit_upper hp (by linarith) hlog
  have hh := LowEntropyLeaf.eta_le_of_witness (E + C) p n (by linarith) hphys hp hph
    (hentropy.trans (hsmall.trans (by linarith))) hlogit hn
  convert! hh using 1
  unfold psi C
  congr 1
  ring

theorem log_floor {E : ℝ} (hE : 0 < E) (hEu : E ≤ 1 / 2048) :
    47 / 4 ≤ Real.log ((2 - E) / E) / Real.log 2 := by
  have hr : (4095 : ℝ) ≤ (2 - E) / E := by
    apply (le_div_iff₀ hE).mpr
    linarith
  have h₁ := Real.log_le_log (by norm_num : (0 : ℝ) < 4095) hr
  have h₂ := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ (47 : ℕ))
    (by norm_num : (2 : ℝ) ^ (47 : ℕ) ≤ (4095 : ℝ) ^ (4 : ℕ))
  rw [Real.log_pow, Real.log_pow] at h₂
  norm_num at h₂
  apply (le_div_iff₀ log_two_pos).mpr
  nlinarith only [h₁, h₂]

/-- The high-bias portion is impossible for an active parent. All six
subintervals and their endpoint equalities are included. -/
theorem parent_dominance_high_bias {q E : ℝ}
    (hql : 1 / 8 ≤ q) (hqu : q ≤ 1 / 2) (hE : 0 < E) (hEu : E ≤ 1 / 2048) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  have hf := PsiParentPhiFloor.phi_lower (by linarith : 0 < q) hE (by linarith)
  have hg := mul_le_mul_of_nonneg_left (log_floor hE hEu)
    (show 0 ≤ 1 - q - E by linarith)
  by_cases hq15 : q ≤ 3 / 20
  · have hp := psi_anchor_cap (l := 1 / 8) (p := 1 / 1024) (n := 10)
      (by norm_num) hql hqu hE hEu (by norm_num) (by norm_num) (by norm_num)
      (by norm_num; rw [show (1024 : ℝ) = 2 ^ (10 : ℕ) by norm_num, Real.log_pow]; norm_num)
      (by norm_num)
    nlinarith only [hp, hf, hg, hq15, hEu]
  · by_cases hq17 : q ≤ 17 / 100
    · have hl : Real.log ((1 / 704 : ℝ)⁻¹) ≤ (19 / 2) * Real.log 2 := by
        have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 704 ^ (2 : ℕ))
          (by norm_num : (704 : ℝ) ^ (2 : ℕ) ≤ (2 : ℝ) ^ (19 : ℕ))
        rw [Real.log_pow, Real.log_pow] at hh
        norm_num at hh ⊢
        linarith
      have hp := psi_anchor_cap (l := 3 / 20) (p := 1 / 704) (n := 19 / 2)
        (by norm_num) (lt_of_not_ge hq15).le hqu hE hEu
        (by norm_num) (by norm_num) (by norm_num) hl (by norm_num)
      nlinarith only [hp, hf, hg, hq17, hEu]
    · by_cases hq23 : q ≤ 23 / 100
      · have hp := psi_anchor_cap (l := 17 / 100) (p := 1 / 512) (n := 9)
          (by norm_num) (lt_of_not_ge hq17).le hqu hE hEu
          (by norm_num) (by norm_num) (by norm_num)
          (by norm_num; rw [show (512 : ℝ) = 2 ^ (9 : ℕ) by norm_num, Real.log_pow]; norm_num)
          (by norm_num)
        nlinarith only [hp, hf, hg, hq23, hEu]
      · by_cases hq31 : q ≤ 31 / 100
        · have hp := psi_anchor_cap (l := 23 / 100) (p := 1 / 256) (n := 8)
            (by norm_num) (lt_of_not_ge hq23).le hqu hE hEu
            (by norm_num) (by norm_num) (by norm_num)
            (by norm_num; rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow]; norm_num)
            (by norm_num)
          nlinarith only [hp, hf, hg, hq31, hEu]
        · by_cases hq41 : q ≤ 41 / 100
          · have hp := psi_anchor_cap (l := 31 / 100) (p := 1 / 128) (n := 7)
              (by norm_num) (lt_of_not_ge hq31).le hqu hE hEu
              (by norm_num) (by norm_num) (by norm_num)
              (by norm_num; rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.log_pow]; norm_num)
              (by norm_num)
            nlinarith only [hp, hf, hg, hq41, hEu]
          · have hp := psi_anchor_cap (l := 41 / 100) (p := 1 / 64) (n := 6)
              (by norm_num) (lt_of_not_ge hq41).le hqu hE hEu
              (by norm_num) (by norm_num) (by norm_num)
              (by norm_num; rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]; norm_num)
              (by norm_num)
            nlinarith only [hp, hf, hg, hqu, hEu]

theorem active_bias_lt_eight_entropy {q E : ℝ}
    (_hq : 0 ≤ q) (hqu : q ≤ 1 / 2) (hE : 0 < E) (hEu : E ≤ 1 / 2048)
    (hactive : phi ((1 - q) / 2) E ≤ psi ((1 - q) / 2) E) : q < 8 * E := by
  have hql : q < 1 / 8 := by
    by_contra hn
    exact (not_lt_of_ge hactive) (parent_dominance_high_bias (le_of_not_gt hn) hqu hE hEu)
  by_contra hn
  have hr : 8 * E ≤ q := le_of_not_gt hn
  exact (not_lt_of_ge hactive) (parent_dominance_ratio8 hE (by linarith) hql.le hr)

/-- Actual laws on the entire outer opposite domain through E=1/2048.
No analytic owner, certificate, or entropy-allocation premise remains. -/
theorem law_gap_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (ha : μ.a ≤ 1 / 10) (hb : 1 / 2 ≤ μ.b)
    (hEu : μ.meanEntropy ≤ 1 / 2048)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have heq : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  have hq := active_bias_lt_eight_entropy
    (q := 1 - μ.a - μ.b) (by linarith)
    (by linarith [μ.a_interior.1]) hE hEu (by rwa [heq])
  exact PsiModerateEntropy.law_gap_le_cost_ceiling μ hsum (by linarith)
    (by linarith) (by linarith) hactive

end GeneralCK.PsiOuterEntropy2048

#print axioms GeneralCK.PsiOuterEntropy2048.logarithmic_eight_comparison
#print axioms GeneralCK.PsiOuterEntropy2048.logarithmic_bias_scale
#print axioms GeneralCK.PsiOuterEntropy2048.parent_dominance_ratio8
#print axioms GeneralCK.PsiOuterEntropy2048.entropy_logit_upper
#print axioms GeneralCK.PsiOuterEntropy2048.psi_anchor_cap
#print axioms GeneralCK.PsiOuterEntropy2048.log_floor
#print axioms GeneralCK.PsiOuterEntropy2048.parent_dominance_high_bias
#print axioms GeneralCK.PsiOuterEntropy2048.active_bias_lt_eight_entropy
#print axioms GeneralCK.PsiOuterEntropy2048.law_gap_le_cost

end


