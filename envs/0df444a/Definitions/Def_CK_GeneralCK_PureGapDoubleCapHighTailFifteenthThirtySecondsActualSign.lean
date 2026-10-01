-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailFifteenthThirtySecondsActualSign
-- name    : CK_GeneralCK_PureGapDoubleCapHighTailFifteenthThirtySecondsActualSign
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:53:08.455234+00:00
-- url     : https://prove2.me/theorems/1f8f64e9-4eac-4922-9285-66f66dbc2038
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsActualSign` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsActualSign` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsActualSign` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsActualSign (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapHighTailFifteenthThirtySecondsActualSign.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailFifteenthThirtySecondsContact
import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailFifteenthThirtySecondsRational

-- ===== source module GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsActualSign =====
section

/-! Wider true high-cap bias and slope sign on m≥15/32. Draft until Lean audit. -/

namespace GeneralCK
open Certificates.Reflection

private theorem highTail_log_bias_bound {x c : ℝ}
    (hx : 0 < x) (hx16 : x ≤ 1 / 16)
    (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hcHi : c ≤ (103 / 100 : ℝ) * x) :
    biasB c ≤ (7 / 10 : ℝ) + x ^ 2 := by
  have hu : x ^ 2 ≤ 1 / 256 := by
    have hsq := (sq_le_sq₀ hx.le
      (by norm_num : (0 : ℝ) ≤ 1 / 16)).2 hx16
    norm_num at hsq
    exact hsq
  have hcSq : c ^ 2 ≤ (10609 / 10000 : ℝ) * x ^ 2 := by
    nlinarith [hcHi, hx, hc0]
  have hcSqLim : c ^ 2 ≤ 1 / 200 := by nlinarith [hcSq, hu]
  have hgap : 0 < 1 - c ^ 2 := by nlinarith [hc0, hc1]
  have hfrac : c ^ 2 / (2 * (1 - c ^ 2)) ≤ x ^ 2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hgap)).2
    have hm := mul_le_mul_of_nonneg_left hcSqLim
      (show 0 ≤ 2 * x ^ 2 by positivity)
    nlinarith [hcSq, hm]
  have hlog : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have hp := Certificates.PilotData.log_two.2
    norm_num at hp
    linarith
  exact (doubleCap_biasB_le_log_add_over_gap hc0 hc1).trans
    (by linarith [hfrac, hlog])

/-- Sign of the actual cancellation-free expression at the implicit contact
and inverse-entropy bias on the explicit high cap tail. -/
theorem doubleCapHighTailFifteenth_bias_nonneg {x : ℝ}
    (hx : 0 < x) (hx16 : x ≤ 1 / 16) :
    0 ≤ doubleCapSlopeBiasExpression
      (doubleCapHighTailY x) (doubleCapHighTailC x) := by
  have hx1 : x < 1 / 2 := by linarith
  let y : ℝ := doubleCapHighTailY x
  let c : ℝ := doubleCapHighTailC x
  let u : ℝ := x ^ 2
  let t : ℝ := y ^ 2
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 / 256 := by
    dsimp [u]
    have hsq := (sq_le_sq₀ hx.le
      (by norm_num : (0 : ℝ) ≤ 1 / 16)).2 hx16
    norm_num at hsq
    exact hsq
  have hY := doubleCapHighTailFifteenthY_sq_le hx hx16
  have hy0 : 0 ≤ y := hY.1
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have htu : t ≤ (128 / 63 : ℝ) * u := hY.2.1
  have hh : 0 < doubleCapHighTailFloor x :=
    doubleCapHighTailFloor_pos hx hx1
  have hh1 : doubleCapHighTailFloor x < 1 := by
    have hfloor : (1 + H (2 * ((1 - x) / 2) - 1 / 2)) / 2 <
        H ((1 - x) / 2) :=
      doubleCapHighFloor_lt_entropyCap (by linarith) (by linarith)
    have hH1 := H_le_one ((1 - x) / 2)
    change doubleCapHighTailFloor x < 1
    unfold doubleCapHighTailFloor
    have heq : 2 * ((1 - x) / 2) - 1 / 2 = (1 - 2 * x) / 2 := by ring
    rw [heq] at hfloor
    linarith
  have hyPos : 0 < y := by
    dsimp [y, doubleCapHighTailY]
    linarith [entropyInverse_lt_half hh.le hh1]
  have hy1 : y < 1 := by
    dsimp [y, doubleCapHighTailY]
    linarith [entropyInverse_pos hh hh1.le]
  have hA : y * (1 + t / 3) ≤ SmallMean.A y := by
    have ha := SmallMean.A_ge_linear_cubic hy0 hy1
    dsimp [t]
    nlinarith [ha]
  have haLo : 0 < y * (1 + t / 3) := by
    exact mul_pos hyPos (by linarith [ht0])
  have hcBound := doubleCapHighTailFifteenthC_bounds hx hx16
  have hc0 : 0 ≤ c := hx.le.trans hcBound.1
  have hc1 : c < 1 := by
    have hmem := Reflection.regularContact_mem
      (x / (Real.log 2 * doubleCapHighTailFloor x))
    exact hmem.2
  have hb : 0 < biasB c := Reflection.biasB_pos_wide
    (by
      have hmem := Reflection.regularContact_mem
        (x / (Real.log 2 * doubleCapHighTailFloor x))
      exact hmem.1)
    hc1
  have hbHi : biasB c ≤ (7 / 10 : ℝ) + u := by
    simpa only [u] using highTail_log_bias_bound hx hx16 hc0 hc1 hcBound.2
  have hneg := doubleCapHighTailFifteenth_negative_rational_bound hu0 hu1 ht0 htu
  have hpos := doubleCapHighTailFifteenth_positive_rational_bound hu0 hu1
  have hcheck : 0 ≤
      2 - 2 * y / ((1 - y ^ 2) * (y * (1 + t / 3))) +
      2 * x ^ 2 / ((1 - x ^ 2) * ((7 / 10 : ℝ) + u)) := by
    have hgapY : 0 < 1 - t := by
      have htlim := hY.2.2
      linarith
    have hplus : 0 < 1 + t / 3 := by linarith [ht0]
    have hdenY : 0 < (1 - t) * (1 + t / 3) := mul_pos hgapY hplus
    have hcancel :
        2 - 2 * y / ((1 - y ^ 2) * (y * (1 + t / 3))) =
        2 - 2 / ((1 - t) * (1 + t / 3)) := by
      dsimp [t]
      field_simp [hyPos.ne', hgapY.ne', hplus.ne', hdenY.ne']
    have hmargin := doubleCapHighTailFifteenth_margin_pos
    rw [hcancel]
    dsimp only [u] at hpos ⊢
    linarith [hneg, hpos, mul_nonneg hmargin.le (sq_nonneg x)]
  have hresult := doubleCapSlopeBiasExpression_nonneg_of_bounds
    hy0 (le_refl y) hy1 haLo hA hx.le hcBound.1 hc1 hb hbHi hcheck
  simpa only [y, c] using hresult

#print axioms doubleCapHighTailFifteenth_bias_nonneg

/-- The checked true slope residual is nonnegative for the explicit final
high-cap interval `31/64 ≤ m < 1/2`. -/
theorem doubleCapHighSlopeResidual_nonneg_on_fifteenth_tail {m : ℝ}
    (hm31 : 15 / 32 ≤ m) (hmh : m < 1 / 2) :
    0 ≤ doubleCapHighSlopeResidual m := by
  have hm : 0 < m := by linarith
  let x : ℝ := 1 - 2 * m
  let h : ℝ := (1 + H (2 * m - 1 / 2)) / 2
  have hx : 0 < x := by dsimp [x]; linarith
  have hx16 : x ≤ 1 / 16 := by dsimp [x]; linarith
  have hx1 : x < 1 / 2 := by dsimp [x]; linarith
  have hfloorEq : h = doubleCapHighTailFloor x := by
    dsimp [h, x, doubleCapHighTailFloor]
    congr 1
    ring
  have hh : 0 < h := by
    rw [hfloorEq]
    exact doubleCapHighTailFloor_pos hx hx1
  have hhCap : h < H m := by
    dsimp [h]
    exact doubleCapHighFloor_lt_entropyCap (by linarith) hmh
  have hh1 : h < 1 := hhCap.trans_le (H_le_one m)
  have hYeq : 1 - 2 * entropyInverse h = doubleCapHighTailY x := by
    rw [hfloorEq]
    rfl
  have hCeq : Reflection.regularContact
      (((1 - 2 * m) / h) / Real.log 2) = doubleCapHighTailC x := by
    rw [hfloorEq]
    unfold doubleCapHighTailC
    congr 1
    dsimp [x]
    field_simp [log_two_pos.ne', (doubleCapHighTailFloor_pos hx hx1).ne']
  have hBias := doubleCapHighTailFifteenth_bias_nonneg hx hx16
  have hSlopeBias := four_add_deriv_phi_eq_slopeBias hm hmh hh hh1
  dsimp only at hSlopeBias
  rw [hYeq, hCeq] at hSlopeBias
  have hSlopeFormula := four_add_deriv_phi_eq_slopeFormula hm hmh hh hh1
  have hResidualEq : 4 + deriv (phi m) h = doubleCapHighSlopeResidual m := by
    simpa only [doubleCapHighSlopeResidual, h] using hSlopeFormula
  linarith

#print axioms doubleCapHighSlopeResidual_nonneg_on_fifteenth_tail

end GeneralCK

end


