-- Prove2me | solution 1 for ApspBound.apsp_feasibility
-- status  : ACCEPTED   (prove)
-- author  : @darkhipo
-- created : 2026-10-29T02:19:58.644665+00:00
-- url     : https://prove2.me/submissions/602103d4-a3a6-4814-8689-375755197484

/-
Copyright (c) 2026 Joshua Wharton, QFEX.
Author: Joshua Wharton <joshua@qfex.com>
Packaged for prove2.me by the BigO strike (2026-10-28).
Adapted from the finite affine certificate in shreshth-s/thin-matrix-results,
commit 8a21eaae81599913dba562727e03a9b48c36a5b9.
-/
import Definitions.Def_ApspBound_Model

namespace ApspBound.Analytic

theorem logFour : Real.log 4 = 2 * Real.log 2 := by
  convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num

theorem logTwoPositive : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem TEnclosure :
    (12059361352073940511273 / 10^21 : ℝ) < T ∧
    T < (12059361352073940511274 / 10^21 : ℝ) := by
  have h0 := logTwo
  have hc := entropyC
  have hp : 0 < 2 * Real.log 2 := mul_pos (by norm_num) logTwoPositive
  have hlo : ((12059361352073940511273 / 10^21 : ℝ) - c + 1) * (2 * Real.log 2)
      < c * entropy (1 / c) := by
    norm_num [c] at hc ⊢
    linarith [h0.1, h0.2, hc.1, hc.2]
  have hhi : c * entropy (1 / c)
      < ((12059361352073940511274 / 10^21 : ℝ) - c + 1) * (2 * Real.log 2) := by
    norm_num [c] at hc ⊢
    linarith [h0.1, h0.2, hc.1, hc.2]
  have hl := (lt_div_iff₀ hp).2 hlo
  have hh := (div_lt_iff₀ hp).2 hhi
  dsimp [T, CK]
  rw [logFour]
  constructor <;> linarith

theorem GEnclosure :
    (86576374110896937279 / 10^21 : ℝ) < G ∧
    G < (86576374110896937280 / 10^21 : ℝ) := by
  have h0 := logTwo
  have hc := entropyC
  have hd := entropyD
  dsimp [G]
  rw [logFour]
  constructor
  · apply (lt_div_iff₀ logTwoPositive).2
    norm_num [c, theta] at hc hd ⊢
    linarith [h0.1, h0.2, hc.1, hc.2, hd.1, hd.2]
  · apply (div_lt_iff₀ logTwoPositive).2
    norm_num [c, theta] at hc hd ⊢
    linarith [h0.1, h0.2, hc.1, hc.2, hd.1, hd.2]

theorem q1Enclosure :
    (348125802190376753494 / 10^21 : ℝ) < q1 ∧
    q1 < (348125802190376753495 / 10^21 : ℝ) := by
  have h0 := logTwo
  have ht := entropyTheta
  dsimp [q1]
  constructor
  · apply (lt_div_iff₀ logTwoPositive).2
    linarith [h0.1, h0.2, ht.1, ht.2]
  · apply (div_lt_iff₀ logTwoPositive).2
    linarith [h0.1, h0.2, ht.1, ht.2]

theorem signedLowerReal (coefficient lo hi : Rat) (x : ℝ)
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    (Numerical.signedLower coefficient lo hi : ℝ) ≤ (coefficient : ℝ) * x := by
  by_cases h : 0 ≤ coefficient
  · simp only [Numerical.signedLower, if_pos h, Rat.cast_mul]
    apply mul_le_mul_of_nonneg_left hlo
    exact_mod_cast h
  · simp only [Numerical.signedLower, if_neg h, Rat.cast_mul]
    apply mul_le_mul_of_nonpos_left hhi
    have hn : coefficient ≤ 0 := le_of_not_ge h
    exact_mod_cast hn

theorem actualParameterEnclosures :
    (Numerical.tLo : ℝ) ≤ T ∧ T ≤ (Numerical.tHi : ℝ) ∧
    (Numerical.gLo : ℝ) ≤ G ∧ G ≤ (Numerical.gHi : ℝ) ∧
    (Numerical.qLo : ℝ) ≤ q1 ∧ q1 ≤ (Numerical.qHi : ℝ) := by
  have ht := TEnclosure
  have hg := GEnclosure
  have hq := q1Enclosure
  norm_num [Numerical.tLo, Numerical.tHi, Numerical.gLo, Numerical.gHi,
    Numerical.qLo, Numerical.qHi]
  norm_num at ht hg hq
  exact ⟨ht.1.le, ht.2.le, hg.1.le, hg.2.le, hq.1.le, hq.2.le⟩

theorem lowerLeActual (a : Numerical.Affine) :
    (Numerical.lower a : ℝ) ≤ evalReal a := by
  rcases actualParameterEnclosures with ⟨ht0, ht1, hg0, hg1, hq0, hq1⟩
  have ht := signedLowerReal a.tCoeff _ _ T ht0 ht1
  have hg := signedLowerReal a.gCoeff _ _ G hg0 hg1
  have hq := signedLowerReal a.qCoeff _ _ q1 hq0 hq1
  unfold Numerical.lower evalReal
  push_cast
  linarith

theorem allActualRealCostsWithSlack :
    ∀ check ∈ Numerical.checks,
      (check.target : ℝ) + uniformSlack < evalReal check.expression := by
  intro check hmember
  have hb : decide (check.target + Numerical.uniformSlack < Numerical.lower check.expression)
      = true :=
    (List.all_eq_true.mp Numerical.numericalMarginsWithSlack) check hmember
  have hr : check.target + Numerical.uniformSlack < Numerical.lower check.expression :=
    of_decide_eq_true hb
  have hm : (check.target : ℝ) + uniformSlack <
      (Numerical.lower check.expression : ℝ) := by
    have hcast : ((check.target + Numerical.uniformSlack : Rat) : ℝ) <
        (Numerical.lower check.expression : ℝ) := by exact_mod_cast hr
    norm_num [Numerical.uniformSlack, uniformSlack] at hcast ⊢
    exact hcast
  exact lt_of_lt_of_le hm (lowerLeActual check.expression)

end ApspBound.Analytic

theorem solution :
    ApspBound.Numerical.checks.length = 47 ∧
    ∀ check ∈ ApspBound.Numerical.checks,
      (check.target : ℝ) + ApspBound.Analytic.uniformSlack <
        ApspBound.Analytic.evalReal check.expression :=
  ⟨ApspBound.Numerical.checkCount, ApspBound.Analytic.allActualRealCostsWithSlack⟩
