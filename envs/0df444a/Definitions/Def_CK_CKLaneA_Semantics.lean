-- Prove2me | Definitions.Def_CK_CKLaneA_Semantics
-- name    : CK_CKLaneA_Semantics
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T15:55:40.686049+00:00
-- url     : https://prove2.me/theorems/35dda70d-1eb3-4fd7-beda-acc5b47e7617
-- title:
--   Courtade–Kumar proof module `CKLaneA.Semantics` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA.Semantics` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA.Semantics` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA.Semantics (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA/Semantics.lean)

import Definitions.Def_CK_CKLaneA_Prog
import Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerDetGapFactor
import Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerRegularContact

/-!
# Lane A: semantics of the generated program

For `0 < a < 1/2`, `0 < z < 1`, `w = a + z*(1/2-a)`:
`r147_D a z = HighU.actualDetGapCoefficient a w` and `r170_M a z = Natural.m11 a w`.
-/

namespace CKLaneA.Prog
open GeneralCK GeneralCK.Certificates CKLaneA Correction Real

theorem cst1 : ((1267650600228229401496703205376 : ℤ) : ℝ) / (DyadicInterval.scale 100 : ℝ) = 1 := by
  simp only [DyadicInterval.scale]; norm_num
theorem cst2 : ((2535301200456458802993406410752 : ℤ) : ℝ) / (DyadicInterval.scale 100 : ℝ) = 2 := by
  simp only [DyadicInterval.scale]; norm_num
theorem cst_half : ((633825300114114700748351602688 : ℤ) : ℝ) / (DyadicInterval.scale 100 : ℝ) = 1 / 2 := by
  simp only [DyadicInterval.scale]; norm_num
theorem cst8 : ((10141204801825835211973625643008 : ℤ) : ℝ) / (DyadicInterval.scale 100 : ℝ) = 8 := by
  simp only [DyadicInterval.scale]; norm_num

section Consts
variable (a z : ℝ)
theorem r2_eq : r2_one a z = 1 := by simp only [r2_one, cst1]
theorem r3_eq : r3_two a z = 2 := by simp only [r3_two, cst2]
theorem r4_eq : r4_half a z = 1 / 2 := by simp only [r4_half, cst_half]
theorem r5_eq : r5_eight a z = 8 := by simp only [r5_eight, cst8]
end Consts

/-! ## pure algebra over abstract atoms -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem dBlock_eq (d q h J j R W S : ℝ) :
    dBlock d q h J j R W S = HighU.detGapCoefficient d q h J j R W S := by
  simp only [dBlock, HighU.detGapCoefficient, cst1, cst2]
  simp only [div_eq_mul_inv, mul_inv]
  ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem mBlock_eq (d q h J Jw Fs W S : ℝ) :
    mBlock d q h J Jw Fs W S =
      (q * (J + Jw + 2 * Fs) + d * (J * h - 1)) / J - W * (-q - d * q * J / S) ^ 2 := by
  simp only [mBlock, cst1, cst2]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem W_alg (E B c S om : ℝ) (hom : om = 1 - c ^ 2) (hB : B ≠ 0) (hS : S ≠ 0) (hom0 : om ≠ 0) :
    8 * (E * E * E) * ((2 * B + -(c * c)) * (S⁻¹ * (om⁻¹ * om⁻¹ * (B⁻¹ * B⁻¹ * B⁻¹)))) =
      2 * (2 * E ^ 3 * (2 * B - c ^ 2) / (S * ((1 - c ^ 2) / 4) ^ 2 * (2 * B) ^ 3)) := by
  subst hom
  field_simp
  ring

theorem Fs_alg (c ps E B om : ℝ) (hom : om = 1 - c ^ 2) (hB : B ≠ 0) (hom0 : om ≠ 0) :
    c * (2 * ps + 2 * E * (om⁻¹ * B⁻¹)) =
      2 * (c * ps) + E * c / ((1 - c ^ 2) / 4 * (2 * B)) := by
  subst hom
  field_simp
  ring

/-- the logarithmic-ratio identity through `ψ` -/
theorem log_ratio {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    2 * ((x - y) / (x + y)) * psi ((x - y) / (x + y)) = Real.log x - Real.log y := by
  have hxy : 0 < x + y := by linarith
  have habs : |(x - y) / (x + y)| < 1 := by
    rw [abs_div, abs_of_pos hxy, div_lt_one hxy, abs_lt]; constructor <;> linarith
  rw [two_mul_psi habs]
  have h1 : 1 + (x - y) / (x + y) = 2 * x / (x + y) := by field_simp; ring
  have h2 : 1 - (x - y) / (x + y) = 2 * y / (x + y) := by field_simp; ring
  rw [h1, h2, Real.log_div (by positivity) hxy.ne', Real.log_div (by positivity) hxy.ne',
    Real.log_mul (by norm_num) hx.ne', Real.log_mul (by norm_num) hy.ne']
  ring

/-! ## registers -/

section Basic
variable (a z : ℝ)
theorem d_eq : r8_d a z = z * (1 / 2 - a) := by
  simp only [r8_d, r1_rho, r7_amu, r4_eq, r6, r0_u]; ring
theorem w_eq : r9_w a z = a + z * (1 / 2 - a) := by
  simp only [r9_w, r0_u, d_eq]
theorem omu_eq : r11_omu a z = 1 - a := by
  simp only [r11_omu, r2_eq, r10, r0_u]; ring
theorem omw_eq : r13_omw a z = 1 - (a + z * (1 / 2 - a)) := by
  simp only [r13_omw, r2_eq, r12, w_eq]; ring
theorem q_eq : r14_q a z = Natural.qp a := by
  simp only [r14_q, r0_u, omu_eq, Natural.qp]
theorem h_eq : r17_h a z = 1 - 2 * a := by
  simp only [r17_h, r2_eq, r16, r15, r0_u]; ring
theorem upw_eq : r34_upw a z = a + (a + z * (1 / 2 - a)) := by
  simp only [r34_upw, r0_u, w_eq]
theorem tmupw_eq : r36_tmupw a z = 2 - (a + (a + z * (1 / 2 - a))) := by
  simp only [r36_tmupw, r3_eq, r35, upw_eq]; ring
theorem omc2_eq : r54_omc2 a z = 1 - r51_c a z ^ 2 := by
  simp only [r54_omc2, r53, r52_c2, r2_eq]; ring
end Basic

section Main
variable {a z : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) (hz : 0 < z) (hz1 : z < 1)
include ha ha2 hz hz1

theorem geom : 0 < z * (1 / 2 - a) ∧ a < a + z * (1 / 2 - a) ∧ a + z * (1 / 2 - a) < 1 / 2 := by
  have h1 : 0 < z * (1 / 2 - a) := mul_pos hz (by linarith)
  have h2 : z * (1 / 2 - a) < 1 / 2 - a := by nlinarith
  exact ⟨h1, by linarith, by linarith⟩

theorem J_eq : r23_J a z = Natural.jn a := by
  simp only [r23_J, r19_L1u, r22, r18_Lu, omu_eq, r0_u]
  rw [Natural.jn_eq_log_sub ha (by linarith)]; ring

theorem Jw_eq : r149_Jw a z = Natural.jn (a + z * (1 / 2 - a)) := by
  obtain ⟨hd, haw, hw⟩ := geom ha ha2 hz hz1
  simp only [r149_Jw, r21_L1w, r148, r20_Lw, omw_eq, w_eq]
  rw [Natural.jn_eq_log_sub (by linarith) (by linarith)]; ring

theorem S_eq : r32_S a z = Natural.entropySum a (a + z * (1 / 2 - a)) := by
  simp only [r32_S, r27_hnu, r26, r24, r25, r31_hnw, r30, r28, r29, r18_Lu, r19_L1u, r20_Lw,
    r21_L1w, omu_eq, omw_eq, w_eq, r0_u, Natural.entropySum, Mixed.hn]
  ring

theorem S_pos : 0 < r32_S a z := by
  obtain ⟨hd, haw, hw⟩ := geom ha ha2 hz hz1
  rw [S_eq ha ha2 hz hz1]
  unfold Natural.entropySum
  rw [Mixed.hn_eq_H_mul_log, Mixed.hn_eq_H_mul_log]
  exact add_pos (mul_pos (H_pos ha (by linarith)) log_two_pos)
    (mul_pos (H_pos (by linarith) (by linarith)) log_two_pos)

theorem j_eq : r48_j a z = dslope Natural.jn a (a + z * (1 / 2 - a)) := by
  obtain ⟨hd, haw, hw⟩ := geom ha ha2 hz hz1
  have hdd : a + z * (1 / 2 - a) - a = r8_d a z := by rw [d_eq]; ring
  have hd' : r8_d a z ≠ 0 := by rw [d_eq]; exact hd.ne'
  have hy1 : r39_y1 a z = ((a + z * (1 / 2 - a)) - a) / ((a + z * (1 / 2 - a)) + a) := by
    simp only [r39_y1, r37_iupw, d_eq, upw_eq]; ring
  have hy2 : r40_y2 a z = ((1 - a) - (1 - (a + z * (1 / 2 - a)))) /
      ((1 - a) + (1 - (a + z * (1 / 2 - a)))) := by
    simp only [r40_y2, r38_itm, d_eq, tmupw_eq]; ring
  have k1 := log_ratio (x := a + z * (1 / 2 - a)) (y := a) (by linarith) ha
  have k2 := log_ratio (x := 1 - a) (y := 1 - (a + z * (1 / 2 - a))) (by linarith) (by linarith)
  rw [← hy1] at k1
  rw [← hy2] at k2
  have e1 : r44 a z = (Real.log (a + z * (1 / 2 - a)) - Real.log a) / r8_d a z := by
    rw [eq_div_iff hd', ← k1]; simp only [r44, r43, r41_p1, r39_y1, r3_eq]; ring
  have e2 : r46 a z = (Real.log (1 - a) - Real.log (1 - (a + z * (1 / 2 - a)))) / r8_d a z := by
    rw [eq_div_iff hd', ← k2]; simp only [r46, r45, r42_p2, r40_y2, r3_eq]; ring
  rw [dslope_of_ne _ (by linarith : a + z * (1 / 2 - a) ≠ a), slope_def_field,
    Natural.jn_eq_log_sub (by linarith) (by linarith), Natural.jn_eq_log_sub ha (by linarith), hdd]
  simp only [r48_j, r47]
  rw [e1, e2]
  field_simp
  ring

theorem c_eq : r51_c a z = HighU.regularBias a (a + z * (1 / 2 - a)) := by
  simp only [r51_c, HighU.regularBias]
  congr 1
  simp only [r50_t, r49, r33_iS, r3_eq, d_eq]
  rw [S_eq ha ha2 hz hz1]
  ring

theorem c_mem : |r51_c a z| < 1 := by
  have := Reflection.regularContact_mem (r50_t a z)
  simp only [r51_c]
  exact abs_lt.mpr ⟨this.1, this.2⟩

theorem B_eq : r59_B a z = Reflection.biasB (r51_c a z) := by
  simp only [r59_B, r55_L2, r58, r57, r56, r54_omc2, r53, r52_c2, r2_eq, r3_eq, r4_eq,
    Reflection.biasB]
  ring

theorem E_eq : r64_E a z = Reflection.biasE (r51_c a z) := by
  have hA : r61_A a z = SmallMean.A (r51_c a z) := by
    simp only [r61_A, r60_pc]; rw [A_eq_mul_psi (c_mem ha ha2 hz hz1)]
  simp only [r64_E, r63, r62]
  rw [hA, B_eq ha ha2 hz hz1, biasE_eq (c_mem ha ha2 hz hz1)]
  ring

theorem omc2_pos : 0 < r54_omc2 a z := by
  have := c_mem ha ha2 hz hz1
  rw [omc2_eq]
  have h1 : r51_c a z ^ 2 = |r51_c a z| ^ 2 := (sq_abs _).symm
  rw [h1]
  nlinarith [abs_nonneg (r51_c a z)]

theorem B_pos : 0 < r59_B a z := by
  rw [B_eq ha ha2 hz hz1]
  have := c_mem ha ha2 hz hz1
  exact Reflection.biasB_pos_wide (by linarith [neg_abs_le (r51_c a z)])
    (by linarith [le_abs_self (r51_c a z)])

theorem Fs_eq : r150_Fs a z = Natural.Fs (r51_c a z) := by
  have hB := (B_pos ha ha2 hz hz1).ne'
  have hg := (omc2_pos ha ha2 hz hz1).ne'
  have key := Fs_alg (r51_c a z) (r60_pc a z) (r64_E a z) (r59_B a z) (r54_omc2 a z)
    (omc2_eq a z) hB hg
  simp only [r150_Fs, r71_FsC, r66, r70, r67, r69, r68, r65_iB, r3_eq]
  rw [key, Natural.Fs, A_eq_mul_psi (c_mem ha ha2 hz hz1), E_eq ha ha2 hz hz1, B_eq ha ha2 hz hz1]
  simp only [r60_pc]

theorem R_eq : r74_R a z = HighU.regularFsGap a (a + z * (1 / 2 - a)) := by
  obtain ⟨hd, haw, hw⟩ := geom ha ha2 hz hz1
  have hS := (S_pos ha ha2 hz hz1).ne'
  have hd' : r8_d a z ≠ 0 := by rw [d_eq]; exact hd.ne'
  have hmul := HighU.regularFsGap_mul_gap a (a + z * (1 / 2 - a))
  rw [← c_eq ha ha2 hz hz1, ← Fs_eq ha ha2 hz hz1] at hmul
  have hwa : a + z * (1 / 2 - a) - a = r8_d a z := by rw [d_eq]; ring
  rw [hwa] at hmul
  have hreg : HighU.regularFsGap a (a + z * (1 / 2 - a)) = r150_Fs a z / r8_d a z := by
    rw [eq_div_iff hd', mul_comm]; exact hmul
  rw [hreg]
  have hc : r51_c a z = r50_t a z * r64_E a z := by
    rw [E_eq ha ha2 hz hz1]; exact Reflection.regularContact_equation (r50_t a z)
  simp only [r74_R, r73, r72, r150_Fs, r3_eq]
  rw [hc]
  simp only [r50_t, r49, r3_eq]
  field_simp

theorem W_eq : r88_W a z = HighU.regularWeight a (a + z * (1 / 2 - a)) := by
  have hB := (B_pos ha ha2 hz hz1).ne'
  have hg := (omc2_pos ha ha2 hz hz1).ne'
  have hS := (S_pos ha ha2 hz hz1).ne'
  have key := W_alg (r64_E a z) (r59_B a z) (r51_c a z) (r32_S a z) (r54_omc2 a z)
    (omc2_eq a z) hB hS hg
  simp only [HighU.regularWeight, Natural.Fss]
  rw [← c_eq ha ha2 hz hz1, ← S_eq ha ha2 hz hz1, ← E_eq ha ha2 hz hz1, ← B_eq ha ha2 hz hz1, ← key]
  simp only [r88_W, r78, r76_E3, r75, r87, r81, r79, r80, r86, r85, r82, r77_iomc2, r84, r83,
    r65_iB, r33_iS, r5_eq, r3_eq, r52_c2]

theorem D_eq : r147_D a z = HighU.actualDetGapCoefficient a (a + z * (1 / 2 - a)) := by
  rw [D_block, dBlock_eq]
  unfold HighU.actualDetGapCoefficient
  have hwa : a + z * (1 / 2 - a) - a = r8_d a z := by rw [d_eq]; ring
  rw [hwa, j_eq ha ha2 hz hz1, R_eq ha ha2 hz hz1, W_eq ha ha2 hz hz1, S_eq ha ha2 hz hz1,
    J_eq ha ha2 hz hz1, q_eq, h_eq]

theorem M_eq : r170_M a z = Natural.m11 a (a + z * (1 / 2 - a)) := by
  obtain ⟨hd, haw, hw⟩ := geom ha ha2 hz hz1
  rw [M_block, mBlock_eq]
  unfold Natural.m11 Natural.au Natural.zu Natural.weight
  rw [HighU.contact_eq_regularContact ha haw hw]
  have hbias : Reflection.regularContact (2 * (a + z * (1 / 2 - a) - a) /
      Natural.entropySum a (a + z * (1 / 2 - a))) = r51_c a z := by
    rw [c_eq ha ha2 hz hz1]; rfl
  have hW := W_eq ha ha2 hz hz1
  simp only [HighU.regularWeight] at hW
  rw [← c_eq ha ha2 hz hz1] at hW
  have hwa : a + z * (1 / 2 - a) - a = r8_d a z := by rw [d_eq]; ring
  rw [hbias, ← Fs_eq ha ha2 hz hz1, ← hW, ← S_eq ha ha2 hz hz1, ← J_eq ha ha2 hz hz1,
    ← Jw_eq ha ha2 hz hz1, ← q_eq, ← h_eq, hwa]

end Main

end CKLaneA.Prog


