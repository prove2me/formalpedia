-- Prove2me | Definitions.Def_CK_GeneralCK_PsiOuterEntropy28
-- name    : CK_GeneralCK_PsiOuterEntropy28
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:01:16.962128+00:00
-- url     : https://prove2.me/theorems/13ef234c-1474-4279-a885-2d2a14dbe987
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiOuterEntropy28` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiOuterEntropy28` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiOuterEntropy28` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiOuterEntropy28 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiOuterEntropy28.lean)

import Definitions.Def_CK_GeneralCK_PsiOuterEntropy37
import Definitions.Def_CK_GeneralCK_PsiThreeTenthsParentClosure

-- ===== source module GeneralCK.PsiOuterEntropy28 =====
section

/-!
# Parent exclusion at entropy ratio 28

A contact tangent at 32 and the retained quadratic parent gain improve the
medium-bias ratio-37 exclusion to ratio 28. All comparison coefficients are
exact rational numbers.
-/

namespace GeneralCK.PsiOuterEntropy28

noncomputable def P32 (x : ℝ) : ℝ :=
  1 + (1091 / 128) * x + (3 / 32) * x ^ 2

theorem F_le_logarithmic_polynomial32 {q E : ℝ} (hq : 0 < q) (hE : 0 < E)
    (hr : 16 * E ≤ q) :
    F q E ≤ q * Real.log (P32 (q / E)) / Real.log 2 := by
  have hx : 16 ≤ q / E := (le_div_iff₀ hE).mpr hr
  have hh := PsiParentContactEnvelope.contact_odds_polynomial
    (n := 5) (r := 32) hq hE hr (by norm_num)
    (by rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]; norm_num)
    (by linarith)
  have he : 1 + 2 * (5 : ℝ) * (q / E) +
      (3 / 2) * (q / E) * (2 * (q / E) / 32 - 63 / 64) = P32 (q / E) := by
    unfold P32
    ring
  rw [he] at hh
  have hv := radialContact_pos hq hE
  have hvh := radialContact_lt_half hq hE
  have hl := Real.log_le_log
    (div_pos (by linarith : 0 < 1 - radialContact q E) hv) hh
  unfold F
  rw [if_neg hq.ne']
  unfold J
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hl hq.le) log_two_pos.le
  convert! h using 1 <;> ring

theorem log_P32_lt_five_halves_add_three_tenths {x : ℝ} (hx : 28 ≤ x) :
    Real.log (P32 x) < (5 / 2) * Real.log (1 + 2 * x / 7) + 3 / 10 := by
  have hy : 0 ≤ x - 28 := by linarith
  have he : (13 / 10 : ℝ) ^ 2 * (1 + 2 * x / 7) ^ 5 - (P32 x) ^ 2 =
      1352 * (x - 28) ^ 5 / 420175 +
      6121971 * (x - 28) ^ 4 / 12293120 +
      103069653 * (x - 28) ^ 3 / 3512320 +
      3039855043 * (x - 28) ^ 2 / 4014080 +
      517074611 * (x - 28) / 71680 + 44184911 / 25600 := by
    unfold P32
    ring
  have hdiff : 0 < (13 / 10 : ℝ) ^ 2 * (1 + 2 * x / 7) ^ 5 - (P32 x) ^ 2 := by
    rw [he]
    positivity
  have hP : 0 < P32 x := by unfold P32; positivity
  have hh := Real.log_lt_log (pow_pos hP 2)
    (show (P32 x) ^ 2 < (13 / 10 : ℝ) ^ 2 * (1 + 2 * x / 7) ^ 5 by linarith)
  rw [Real.log_mul (by norm_num : (13 / 10 : ℝ) ^ 2 ≠ 0)
    (by positivity : (1 + 2 * x / 7) ^ 5 ≠ 0),
    Real.log_pow, Real.log_pow, Real.log_pow] at hh
  have hlog := Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 13 / 10) (by norm_num : (13 / 10 : ℝ) ≠ 1)
  nlinarith only [hh, hlog]

/-- On the medium-bias strip, the extra `3q/10` in the logarithm comparison
is paid by the previously retained `q²` parent gain. -/
theorem parent_dominance_medium28 {q E : ℝ}
    (hql : 3 / 10 ≤ q) (hqu : q ≤ 2 / 5) (hE : 0 < E)
    (hr : 28 * E ≤ q) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  have hq : 0 < q := by linarith
  let x := q / E
  have hx : 28 ≤ x := (le_div_iff₀ hE).mpr hr
  have hF := (le_div_iff₀ log_two_pos).mp
    (F_le_logarithmic_polynomial32 hq hE (by linarith))
  have hp := mul_lt_mul_of_pos_left
    (log_P32_lt_five_halves_add_three_tenths hx) hq
  have hs := PsiOuterEntropy200.logarithmic_bias_scale (Q := (2 / 5 : ℝ))
    hq.le (by norm_num) hqu (show 0 ≤ x by linarith)
  have hs' : (5 / 2) * q * Real.log (1 + 2 * x / 7) ≤
      Real.log (1 + 5 * q ^ 2 / (7 * E)) := by
    convert! hs using 1 <;> dsimp [x] <;> congr 1 <;> ring
  apply PsiOuterEntropy200.parent_dominance_of_cost_bound
    hq (by linarith) hE (by linarith)
  change F q E * Real.log 2 ≤ q * Real.log (P32 x) at hF
  nlinarith only [hF, hp, hs', mul_nonneg hq.le (sub_nonneg.mpr hql)]

/-- Uniform parent dominance through bias two fifths at ratio 28. -/
theorem parent_dominance_two_fifths28 {q E : ℝ}
    (hq : 0 < q) (hqu : q ≤ 2 / 5) (hE : 0 < E)
    (hr : 28 * E ≤ q) :
    psi ((1 - q) / 2) E < phi ((1 - q) / 2) E := by
  by_cases hlow : q ≤ 3 / 10
  · exact PsiThreeTenthsParent.parent_dominance_ratio8 hq hlow hE (by linarith)
  · exact parent_dominance_medium28 (le_of_not_ge hlow) hqu hE hr

/-- The closed excluded strip leaves a strict entropy-ratio constraint. -/
theorem active_bias_lt_twenty_eight_entropy {q E : ℝ}
    (hqu : q ≤ 2 / 5) (hE : 0 < E)
    (hactive : phi ((1 - q) / 2) E ≤ psi ((1 - q) / 2) E) : q < 28 * E := by
  by_contra hn
  have hr : 28 * E ≤ q := le_of_not_gt hn
  exact (not_lt_of_ge hactive)
    (parent_dominance_two_fifths28 (by linarith) hqu hE hr)

#print axioms F_le_logarithmic_polynomial32
#print axioms log_P32_lt_five_halves_add_three_tenths
#print axioms parent_dominance_medium28
#print axioms parent_dominance_two_fifths28
#print axioms active_bias_lt_twenty_eight_entropy

end GeneralCK.PsiOuterEntropy28

end


