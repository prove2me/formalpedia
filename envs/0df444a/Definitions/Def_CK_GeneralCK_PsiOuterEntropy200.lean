-- Prove2me | Definitions.Def_CK_GeneralCK_PsiOuterEntropy200
-- name    : CK_GeneralCK_PsiOuterEntropy200
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:25:27.032346+00:00
-- url     : https://prove2.me/theorems/841ee23f-5cba-4203-bdd5-5c69d17058d6
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiOuterEntropy200` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiOuterEntropy200` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiOuterEntropy200` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiOuterEntropy200 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiOuterEntropy200.lean)

import Definitions.Def_CK_GeneralCK_PsiParentContactEnvelope
import Definitions.Def_CK_GeneralCK_PsiParentPolynomialBounds

-- ===== source module GeneralCK.PsiOuterEntropy200 =====
section

/-!
# A larger analytic outer owner through entropy 1/200

Sharper radial-contact envelopes prove parent dominance on three larger
bias ranges. The remaining active parents satisfy q<8E, allowing the proved
retained-child endpoint theorem to close all separated opposite laws.
-/

namespace GeneralCK.PsiOuterEntropy200
open Set

theorem logarithmic_bias_scale {q Q x : ℝ}
    (hq : 0 ≤ q) (hQ : 0 < Q) (hqu : q ≤ Q) (hx : 0 ≤ x) :
    (q / Q) * Real.log (1 + (5 / 7) * Q * x) ≤
      Real.log (1 + (5 / 7) * q * x) := by
  have hh := strictConcaveOn_log_Ioi.concaveOn.2
    (show 0 < 1 + (5 / 7) * Q * x by positivity)
    (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show 0 ≤ q / Q by positivity)
    (show 0 ≤ 1 - q / Q from sub_nonneg.mpr ((div_le_one hQ).mpr hqu))
    (show q / Q + (1 - q / Q) = 1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hh
  convert! hh using 1
  congr 1
  field_simp
  ring

/-- The linear part of the integrated parent gain contributes q² after
conversion to natural logarithms. The displayed cost criterion retains it. -/
theorem parent_dominance_of_cost_bound {q E : ℝ}
    (hq : 0 < q) (hqu : q ≤ 1 / 2) (hE : 0 < E) (hEu : E ≤ 1 / 2)
    (hbound : F q E * Real.log 2 < q ^ 2 + Real.log (1 + 5 * q ^ 2 / (7 * E))) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  let C := 1 - H ((1 - q) / 2)
  have hC : 0 ≤ C := sub_nonneg.mpr (H_le_one _)
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have hh := Certificates.PilotData.log_two.2
    norm_num at hh
    linarith
  have hClower := SmallMean.Cn_ge_half_sq hq.le (show q ≤ 1 by linarith)
  change q ^ 2 / 2 ≤ Real.log 2 * C at hClower
  have hCrational : 5 * q ^ 2 / 7 ≤ C := by
    have hh := mul_le_mul_of_nonneg_right hL hC
    nlinarith only [hh, hClower]
  have hphys : E + C ≤ 1 := by
    have hh := PsiParentPhiFloor.entropy_chord
      (show 0 ≤ (1 - q) / 2 by linarith) (show (1 - q) / 2 ≤ 1 / 2 by linarith)
    dsimp [C]
    linarith
  have hg := eta_increment_ge_linear_log hE hC hphys
  have hl : Real.log (1 + 5 * q ^ 2 / (7 * E)) ≤ Real.log (1 + C / E) := by
    apply Real.log_le_log (by positivity)
    have hh := div_le_div_of_nonneg_right hCrational hE.le
    convert! add_le_add_left hh 1 using 1 <;> ring
  have hgm := mul_le_mul_of_nonneg_right hg log_two_pos.le
  have hid : (2 * C + Real.log (1 + C / E) / Real.log 2) * Real.log 2 =
      2 * C * Real.log 2 + Real.log (1 + C / E) := by field_simp
  rw [hid] at hgm
  have hF : F q E < eta E - eta (E + C) := by
    apply (mul_lt_mul_iff_left₀ log_two_pos).mp
    nlinarith only [hbound, hl, hgm, hClower]
  unfold phi psi
  rw [show |1 - 2 * ((1 - q) / 2)| = q by
    rw [show 1 - 2 * ((1 - q) / 2) = q by ring, abs_of_pos hq]]
  have he : E + 1 - H ((1 - q) / 2) = E + C := by dsimp [C]; ring
  rw [he]
  linarith only [hF]

/-- Uniform parent dominance to bias 1/4 at separation-to-entropy ratio 16. -/
theorem parent_dominance_quarter {q E : ℝ}
    (hq : 0 < q) (hqu : q ≤ 1 / 4) (hE : 0 < E) (hr : 16 * E ≤ q) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  let x := q / E
  have hx : 16 ≤ x := (le_div_iff₀ hE).mpr hr
  have hF := (le_div_iff₀ log_two_pos).mp
    (PsiParentContactEnvelope.F_le_logarithmic_polynomial16 hq hE hr)
  have hp := mul_lt_mul_of_pos_left (PsiParentPolynomialBounds.log_P16_lt hx) hq
  have hs := logarithmic_bias_scale (Q := (1 / 4 : ℝ)) hq.le (by norm_num) hqu
    (show 0 ≤ x by linarith)
  have hs' : 4 * q * Real.log (1 + 5 * x / 28) ≤
      Real.log (1 + 5 * q ^ 2 / (7 * E)) := by
    convert! hs using 1 <;> dsimp [x] <;> congr 1 <;> ring
  change q * Real.log (1 + (837 / 128) * x + (3 / 16) * x ^ 2) <
    q * (4 * Real.log (1 + 5 * x / 28)) at hp
  apply parent_dominance_of_cost_bound hq (by linarith) hE (by linarith)
  change F q E * Real.log 2 ≤ q * Real.log (1 + (837 / 128) * x + (3 / 16) * x ^ 2) at hF
  nlinarith only [hF, hp, hs', sq_nonneg q]

/-- The whole medium-bias interval is handled by the ratio-forty tail. -/
theorem parent_dominance_two_fifths {q E : ℝ}
    (hq : 0 < q) (hqu : q ≤ 2 / 5) (hE : 0 < E) (hr : 40 * E ≤ q) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  let x := q / E
  have hx : 40 ≤ x := (le_div_iff₀ hE).mpr hr
  have hF := (le_div_iff₀ log_two_pos).mp
    (PsiParentContactEnvelope.F_le_logarithmic_polynomial64 hq hE (by linarith))
  have hp := mul_lt_mul_of_pos_left (PsiParentPolynomialBounds.log_P64_lt_five_halves hx) hq
  have hs := logarithmic_bias_scale (Q := (2 / 5 : ℝ)) hq.le (by norm_num) hqu
    (show 0 ≤ x by linarith)
  have hs' : (5 / 2) * q * Real.log (1 + 2 * x / 7) ≤
      Real.log (1 + 5 * q ^ 2 / (7 * E)) := by
    convert! hs using 1 <;> dsimp [x] <;> congr 1 <;> ring
  change q * Real.log (1 + (1347 / 128) * x + (3 / 64) * x ^ 2) <
    q * ((5 / 2) * Real.log (1 + 2 * x / 7)) at hp
  apply parent_dominance_of_cost_bound hq (by linarith) hE (by linarith)
  change F q E * Real.log 2 ≤ q * Real.log (1 + (1347 / 128) * x + (3 / 64) * x ^ 2) at hF
  nlinarith only [hF, hp, hs', sq_nonneg q]

/-- At larger parent bias the linear entropy gain pays for the additional
2q/5 term. This closes every ratio at least seventy-five. -/
theorem parent_dominance_half {q E : ℝ}
    (hql : 2 / 5 ≤ q) (hqu : q ≤ 1 / 2) (hE : 0 < E) (hr : 75 * E ≤ q) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  let x := q / E
  have hq : 0 < q := by linarith
  have hx : 75 ≤ x := (le_div_iff₀ hE).mpr hr
  have hF := (le_div_iff₀ log_two_pos).mp
    (PsiParentContactEnvelope.F_le_logarithmic_polynomial64 hq hE (by linarith))
  have hp := mul_lt_mul_of_pos_left
    (PsiParentPolynomialBounds.log_P64_lt_two_plus_two_fifths hx) hq
  have hs := logarithmic_bias_scale (Q := (1 / 2 : ℝ)) hq.le (by norm_num) hqu
    (show 0 ≤ x by linarith)
  have hs' : 2 * q * Real.log (1 + 5 * x / 14) ≤
      Real.log (1 + 5 * q ^ 2 / (7 * E)) := by
    convert! hs using 1 <;> dsimp [x] <;> congr 1 <;> ring
  change q * Real.log (1 + (1347 / 128) * x + (3 / 64) * x ^ 2) <
    q * (2 * Real.log (1 + 5 * x / 14) + 2 / 5) at hp
  apply parent_dominance_of_cost_bound hq hqu hE (by linarith)
  change F q E * Real.log 2 ≤ q * Real.log (1 + (1347 / 128) * x + (3 / 64) * x ^ 2) at hF
  nlinarith only [hF, hp, hs', mul_nonneg hq.le (sub_nonneg.mpr hql)]

/-- Every active opposite parent through E=1/200 has bias below 8E.
The result includes all three polynomial-tail transition equalities. -/
theorem active_bias_lt_eight_entropy {q E : ℝ}
    (hqu : q ≤ 1 / 2) (hE : 0 < E) (hEu : E ≤ 1 / 200)
    (hactive : phi ((1 - q) / 2) E ≤ psi ((1 - q) / 2) E) : q < 8 * E := by
  have hqs : q ≤ 1 / 8 := by
    by_contra hn
    have hq : 1 / 8 < q := lt_of_not_ge hn
    by_cases hquarter : q ≤ 1 / 4
    · exact (not_lt_of_ge hactive)
        (parent_dominance_quarter (by linarith) hquarter hE (by linarith))
    · by_cases htwo : q ≤ 2 / 5
      · exact (not_lt_of_ge hactive)
          (parent_dominance_two_fifths (by linarith) htwo hE (by linarith [lt_of_not_ge hquarter]))
      · exact (not_lt_of_ge hactive)
          (parent_dominance_half (lt_of_not_ge htwo).le hqu hE (by linarith [lt_of_not_ge htwo]))
  by_contra hn
  have hr : 8 * E ≤ q := le_of_not_gt hn
  exact (not_lt_of_ge hactive)
    (PsiOuterEntropy2048.parent_dominance_ratio8 hE (by linarith) hqs hr)

/-- Actual-law closure with the separation premise exposed for reuse in
the central chart. No child entropy-split condition is assumed. -/
theorem law_gap_le_cost_of_separation {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hb : 1 / 2 ≤ μ.b)
    (hEu : μ.meanEntropy ≤ 1 / 200) (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have heq : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  have hq := active_bias_lt_eight_entropy
    (q := 1 - μ.a - μ.b) (by linarith [μ.a_interior.1]) hE hEu (by rwa [heq])
  exact PsiModerateEntropy.law_gap_le_cost_ceiling μ hsum (by linarith) hd (by linarith) hactive

/-- The complete outer opposite owner through E=1/200. -/
theorem law_gap_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (ha : μ.a ≤ 1 / 10) (hb : 1 / 2 ≤ μ.b)
    (hEu : μ.meanEntropy ≤ 1 / 200)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost :=
  law_gap_le_cost_of_separation μ hsum hb hEu (by linarith) hactive

end GeneralCK.PsiOuterEntropy200

#print axioms GeneralCK.PsiOuterEntropy200.logarithmic_bias_scale
#print axioms GeneralCK.PsiOuterEntropy200.parent_dominance_of_cost_bound
#print axioms GeneralCK.PsiOuterEntropy200.parent_dominance_quarter
#print axioms GeneralCK.PsiOuterEntropy200.parent_dominance_two_fifths
#print axioms GeneralCK.PsiOuterEntropy200.parent_dominance_half
#print axioms GeneralCK.PsiOuterEntropy200.active_bias_lt_eight_entropy
#print axioms GeneralCK.PsiOuterEntropy200.law_gap_le_cost_of_separation
#print axioms GeneralCK.PsiOuterEntropy200.law_gap_le_cost

end


