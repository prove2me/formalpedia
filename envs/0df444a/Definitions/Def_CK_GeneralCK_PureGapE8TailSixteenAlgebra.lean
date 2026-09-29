-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8TailSixteenAlgebra
-- name    : CK_GeneralCK_PureGapE8TailSixteenAlgebra
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:53:31.892785+00:00
-- url     : https://prove2.me/theorems/c50a0395-ac19-4396-928c-70b9dbe9c865
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8TailSixteenAlgebra` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8TailSixteenAlgebra` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8TailSixteenAlgebra` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8TailSixteenAlgebra (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8TailSixteenAlgebra.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8TailAlgebra

-- ===== source module GeneralCK.PureGapE8TailSixteenAlgebra =====
section

namespace GeneralCK

set_option maxHeartbeats 400000

theorem e8Tail_scaled_profile_bounds_sixteen {v e w : ℝ}
    (hv0 : 0 ≤ v) (hvU : v ≤ 1 / 8192)
    (he0 : 1 ≤ e) (heU : e ≤ 8192 / 8191)
    (hw0 : 0 ≤ w) (hwU : w ≤ 101 / 1000) :
    999 / 1000 ≤ e8TailScaledProfile v e w ∧
      e8TailScaledProfile v e w ≤ 109 / 100 := by
  let r := 1 - 2*v
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  have hr2 : 9995 / 10000 ≤ r^2 := by dsimp [r]; nlinarith only [hv0, hvU, sq_nonneg v]
  have hr2U : r^2 ≤ 1 := by nlinarith only [hr0, hr1]
  have hc : 0 < (1-v)^2 := sq_pos_of_pos (by linarith)
  have hratio0 : (999 / 1000 : ℝ) ≤ r / (1-v)^2 := by
    apply (le_div_iff₀ hc).2
    have hv2 : v^2 ≤ (1/8192 : ℝ)^2 := by nlinarith only [hv0, hvU]
    dsimp [r]
    nlinarith only [hv2, hv0, hvU]
  have hratio1 : r / (1-v)^2 ≤ 1 := by
    apply (div_le_iff₀ hc).2
    dsimp [r]
    nlinarith only [sq_nonneg v]
  have hrw : 0 ≤ r*w := mul_nonneg hr0 hw0
  have hrew : r*w ≤ r*e*w := by nlinarith only [mul_nonneg hrw (sub_nonneg.mpr he0)]
  have hrewU : r*e*w ≤ 10003/10000*w := by
    have h := mul_le_mul_of_nonneg_right hr1 (by linarith : 0 ≤ e)
    nlinarith only [mul_nonneg hw0 (show 0 ≤ 10003/10000-r*e by linarith only [h, heU])]
  have hfac0 : 0 ≤ 1-r^2*w := by
    nlinarith only [hwU, mul_nonneg hw0 (sub_nonneg.mpr hr2U)]
  have hfacU : 1-r^2*w ≤ 1-(9995/10000)*w := by
    nlinarith only [mul_nonneg hw0 (sub_nonneg.mpr hr2)]
  have hbase0 : 1 ≤ (1+r*w)^2*(1-r^2*w) := by
    have hbr : 0 ≤ 2-r-2*r^2*w := by
      nlinarith only [hr1, hwU, mul_nonneg hw0 (sub_nonneg.mpr hr2U)]
    have ha := mul_nonneg hrw hbr
    have hb := mul_nonneg (sq_nonneg (r*w)) hfac0
    nlinarith only [ha, hb]
  have hlo : 1 ≤ (1+r*e*w)^2*(1-r^2*w) := by
    apply hbase0.trans
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by linarith only [hrw]) (by linarith only [hrew]) 2) hfac0
  have hupper : (1+r*e*w)^2*(1-r^2*w) ≤
      (1+(10003/10000)*w)^2*(1-(9995/10000)*w) := by
    apply mul_le_mul _ hfacU hfac0 (sq_nonneg _)
    exact pow_le_pow_left₀ (by linarith only [hrw, hrew]) (by linarith only [hrewU]) 2
  have hcubic : (1+(10003/10000)*w)^2*(1-(9995/10000)*w) ≤ 109/100 := by
    have hw2 : w^2 ≤ (101/1000 : ℝ)^2 := by nlinarith only [hw0, hwU]
    have hb : 0 ≤ (10011/10000 : ℝ) - (99899961/100000000)*(101/1000+w) -
        (1000099789955/1000000000000)*((101/1000)^2+(101/1000)*w+w^2) := by nlinarith only [hwU, hw2]
    have hp := mul_nonneg (sub_nonneg.mpr hwU) hb
    nlinarith only [hp]
  have hident : e8TailScaledProfile v e w =
      (r/(1-v)^2)*((1+r*e*w)^2*(1-r^2*w)) := by
    unfold e8TailScaledProfile
    dsimp [r]
    ring
  rw [hident]
  constructor
  · have h := mul_le_mul hratio0 hlo (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : 0 ≤ r/(1-v)^2)
    simpa using h
  · have h := mul_le_mul hratio1 (hupper.trans hcubic)
      (by linarith : 0 ≤ (1+r*e*w)^2*(1-r^2*w)) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h

theorem e8Tail_error_bounds_sixteen {v w : ℝ}
    (hv0 : 0 ≤ v) (hvU : v ≤ 1 / 8192) (hw0 : 0 ≤ w) (hwU : w ≤ 101 / 1000) :
    |e8TailErrorP v w| ≤ 1 / 3 ∧ |e8TailErrorT v w| ≤ 1 / 3 := by
  let p := fun v w : ℝ => 96*v^4*w^3 + 16*v^4*w^2 + 240*v^2*w^3 + 100*v^2*w^2 +
    28*v^2*w + 30*w^3 + 2*w^2 + 2*w
  let m := fun v w : ℝ => 240*v^3*w^3 + 88*v^3*w^2 + 8*v^3*w + 120*v*w^3 + 38*v*w^2 + 16*v*w + 2*v
  let a := fun v w : ℝ => 96*v^5*w^3 + 16*v^5*w^2 + 240*v^3*w^3 + 4*v^3*w^2 + 4*v^3*w +
    34*v^2*w^2 + 30*v*w^3 + 6*v*w + 4*w^2
  let b := fun v w : ℝ => 240*v^4*w^3 + 40*v^4*w^2 + 120*v^2*w^3 + 6*v^2*w + 22*v*w^2 + 3*w^3 + 2*w
  have hp0 : 0 ≤ p v w := by dsimp [p]; positivity
  have hm0 : 0 ≤ m v w := by dsimp [m]; positivity
  have ha0 : 0 ≤ a v w := by dsimp [a]; positivity
  have hb0 : 0 ≤ b v w := by dsimp [b]; positivity
  have hpU : p v w ≤ 1 / 3 := calc
    p v w ≤ p (1/8192) (101/1000) := by dsimp [p]; gcongr
    _ ≤ 1 / 3 := by norm_num [p]
  have hmU : m v w ≤ 1 / 3 := calc
    m v w ≤ m (1/8192) (101/1000) := by dsimp [m]; gcongr
    _ ≤ 1 / 3 := by norm_num [m]
  have haU : a v w ≤ 1 / 3 := calc
    a v w ≤ a (1/8192) (101/1000) := by dsimp [a]; gcongr
    _ ≤ 1 / 3 := by norm_num [a]
  have hbU : b v w ≤ 1 / 3 := calc
    b v w ≤ b (1/8192) (101/1000) := by dsimp [b]; gcongr
    _ ≤ 1 / 3 := by norm_num [b]
  change |p v w - m v w| ≤ 1/3 ∧ |a v w - b v w| ≤ 1/3
  constructor <;> rw [abs_le] <;> constructor <;> linarith

theorem e8Tail_beta_bounds_sixteen {v e w : ℝ}
    (hv0 : 0 ≤ v) (hvU : v ≤ 1 / 8192)
    (he0 : 1 ≤ e) (heU : e ≤ 8192 / 8191)
    (hw0 : 0 ≤ w) (hwU : w ≤ 101 / 1000) :
    -(1 / 1000) ≤ e8TailBeta v e w ∧ e8TailBeta v e w ≤ 1 / 100 := by
  obtain ⟨hP, hT⟩ := e8Tail_error_bounds_sixteen hv0 hvU hw0 hwU
  rw [abs_le] at hP hT
  have hvP0 := mul_le_mul_of_nonneg_left hP.1 hv0
  have hvP1 := mul_le_mul_of_nonneg_left hP.2 hv0
  have heT0 := mul_le_mul_of_nonneg_left hT.1 (sub_nonneg.mpr he0)
  have heT1 := mul_le_mul_of_nonneg_left hT.2 (sub_nonneg.mpr he0)
  have hbase0 : 0 ≤ w^2 - 3*w^3 := by
    nlinarith only [mul_nonneg (sq_nonneg w) (show 0 ≤ 1-3*w by linarith only [hwU])]
  have hbase1 : w^2 - 3*w^3 ≤ 3 / 400 := by
    have hbr : 0 ≤ 101/1000+w-3*((101/1000)^2+(101/1000)*w+w^2) := by
      nlinarith only [hw0, hwU, mul_nonneg hw0 (sub_nonneg.mpr hwU)]
    have hp := mul_nonneg (sub_nonneg.mpr hwU) hbr
    nlinarith only [hp]
  have hN0 : -(1/2000 : ℝ) ≤ w^2 - 3*w^3 + v*e8TailErrorP v w + (e-1)*e8TailErrorT v w := by
    nlinarith only [hvP0, heT0, hvU, heU, hbase0]
  have hN1 : w^2 - 3*w^3 + v*e8TailErrorP v w + (e-1)*e8TailErrorT v w ≤ 1/125 := by
    nlinarith only [hvP1, heT1, hvU, heU, hbase1]
  have hr2 : (1-2*v)^2 ≤ 1 := by nlinarith only [hv0, hvU]
  have hfac : 8989/10000 ≤ 1-(1-2*v)^2*w := by
    nlinarith only [mul_nonneg hw0 (sub_nonneg.mpr hr2), hwU]
  have hden : 89/100 ≤ (1-v)*(1-(1-2*v)^2*w) := by
    have h := mul_le_mul (show (8191/8192 : ℝ) ≤ 1-v by linarith only [hvU]) hfac
      (by norm_num : (0 : ℝ) ≤ 8989/10000) (by linarith only [hvU] : 0 ≤ 1-v)
    nlinarith only [h]
  have hden0 : 0 < (1-v)*(1-(1-2*v)^2*w) := by linarith only [hden]
  unfold e8TailBeta
  constructor
  · apply (le_div_iff₀ hden0).2
    nlinarith only [hN0, hden]
  · apply (div_le_iff₀ hden0).2
    nlinarith only [hN1, hden]

#print axioms e8Tail_scaled_profile_bounds_sixteen
#print axioms e8Tail_error_bounds_sixteen
#print axioms e8Tail_beta_bounds_sixteen

end GeneralCK

end


