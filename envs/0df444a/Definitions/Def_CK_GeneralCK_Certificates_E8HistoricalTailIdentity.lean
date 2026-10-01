-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8HistoricalTailIdentity
-- name    : CK_GeneralCK_Certificates_E8HistoricalTailIdentity
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T21:22:29.078984+00:00
-- url     : https://prove2.me/theorems/280c5c66-6604-49e2-84c4-8a8d92179468
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8HistoricalTailIdentity` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8HistoricalTailIdentity` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8HistoricalTailIdentity` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8HistoricalTailIdentity (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8HistoricalTailIdentity.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8HistoricalLogConvexityBridge

-- ===== source module GeneralCK.Certificates.E8HistoricalTailIdentity =====
section

namespace GeneralCK.Certificates.E8HistoricalLogConvexityBridge

open E8TAxisStableJet5 E8TAxisStableScalar

noncomputable def historicalE (a : ℝ) : ℝ :=
  -3 * a * q a / h a + 2 * r a ^ 3 / (2 * ell a - r a ^ 2) +
    4 * r a - 3 * r a / ell a

noncomputable def historicalX (a : ℝ) : ℝ :=
  r a / ell a - 2 * r a + 2 * a * q a / h a

noncomputable def historicalXPrime (a : ℝ) : ℝ :=
  Real.log 2 * q a * ell a / (2 * h a ^ 2)

noncomputable def historicalYPrime (a : ℝ) : ℝ :=
  (2 / Real.log 2) *
    (h a * (2 * ell a - r a ^ 2) / (q a * ell a ^ 2))

noncomputable def historicalEPrime (a : ℝ) : ℝ :=
  -3 * (q a / h a - 2 * a * r a * q a / h a +
    a ^ 2 * q a ^ 2 / h a ^ 2) +
  6 * r a ^ 2 * q a / (2 * ell a - r a ^ 2) -
  4 * r a ^ 6 / (2 * ell a - r a ^ 2) ^ 2 +
  4 * q a - 3 * (q a / ell a - r a ^ 2 / ell a ^ 2)

theorem h_add_a_mul_r (a : ℝ) : h a + a * r a = ell a := by
  simp only [h, ell, r, z, l1]
  field_simp [(one_add_z_pos a).ne']
  ring

theorem hasDerivAt_z (a : ℝ) : HasDerivAt z (-2 * z a) a := by
  unfold z
  have hi0 := (hasDerivAt_id a).const_mul (-2)
  have hi : HasDerivAt (fun t : ℝ => (-2) * t) (-2) a := by
    convert! hi0 using 1 <;> simp [id_eq]
  convert! (Real.hasDerivAt_exp (-2 * a)).comp a hi using 1 <;> ring

theorem hasDerivAt_r (a : ℝ) : HasDerivAt r (q a) a := by
  have hz := hasDerivAt_z a
  have hd := (hasDerivAt_const a 1).add hz
  have hn := (hasDerivAt_const a 1).sub hz
  have hder := hn.div hd (one_add_z_pos a).ne'
  convert! hder using 1 <;>
    simp only [Pi.sub_apply, Pi.add_apply, Pi.div_apply, r, q] <;>
    field_simp [(one_add_z_pos a).ne'] <;> ring

theorem hasDerivAt_q (a : ℝ) : HasDerivAt q (-2 * r a * q a) a := by
  have hz := hasDerivAt_z a
  have hd := (hasDerivAt_const a 1).add hz
  have hder := ((hasDerivAt_const a 4).mul hz).div (hd.pow 2)
    (pow_ne_zero 2 (one_add_z_pos a).ne')
  convert! hder using 1 <;>
    simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Pi.div_apply, q, r] <;>
    field_simp [(one_add_z_pos a).ne'] <;> ring

theorem hasDerivAt_l1 (a : ℝ) :
    HasDerivAt l1 (-2 * z a / (1 + z a)) a := by
  unfold l1
  convert! ((hasDerivAt_const a 1).add (hasDerivAt_z a)).log
    (one_add_z_pos a).ne' using 1 <;>
    simp only [Pi.add_apply] <;> ring

theorem hasDerivAt_ell (a : ℝ) : HasDerivAt ell (r a) a := by
  have hder := (hasDerivAt_id a).add (hasDerivAt_l1 a)
  convert! hder using 1 <;>
    simp only [Pi.add_apply, id_eq, r] <;>
    field_simp [(one_add_z_pos a).ne'] <;> ring

theorem hasDerivAt_h (a : ℝ) : HasDerivAt h (-a * q a) a := by
  have hz := hasDerivAt_z a
  have hd := (hasDerivAt_const a 1).add hz
  have hc := (((hasDerivAt_const a 2).mul (hasDerivAt_id a)).mul hz).div hd
    (one_add_z_pos a).ne'
  have hh := (hasDerivAt_l1 a).add hc
  convert! hh using 1 <;>
    simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply, id_eq, q] <;>
    field_simp [(one_add_z_pos a).ne'] <;> ring

theorem hasDerivAt_X (a : ℝ) (ha : 0 < a) :
    HasDerivAt X (historicalXPrime a) a := by
  have hr := hasDerivAt_r a
  have hh := hasDerivAt_h a
  have hd := (hasDerivAt_const a 2).mul hh
  have hx := ((hasDerivAt_const a (Real.log 2)).mul hr).div hd
    (mul_ne_zero (by norm_num) (h_pos ha).ne')
  convert! hx using 1 <;>
    simp only [Pi.mul_apply, Pi.div_apply, historicalXPrime] <;>
    rw [← h_add_a_mul_r] <;>
    field_simp [(h_pos ha).ne'] <;> ring

theorem hasDerivAt_historicalXPrime (a : ℝ) (ha : 0 < a) :
    HasDerivAt historicalXPrime (historicalXPrime a * historicalX a) a := by
  have hq := hasDerivAt_q a
  have hb := hasDerivAt_ell a
  have hh := hasDerivAt_h a
  have hnum := (((hasDerivAt_const a (Real.log 2)).mul hq).mul hb)
  have hden := (hasDerivAt_const a 2).mul (hh.pow 2)
  have hx := hnum.div hden
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 (h_pos ha).ne'))
  convert! hx using 1 <;>
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.div_apply, historicalXPrime,
      historicalX] <;>
    field_simp [(q_pos a).ne', (ell_pos ha).ne', (h_pos ha).ne'] <;> ring

theorem hasDerivAt_Y (a : ℝ) (ha : 0 < a) :
    HasDerivAt Y (historicalYPrime a) a := by
  have hr := hasDerivAt_r a
  have hh := hasDerivAt_h a
  have hq := hasDerivAt_q a
  have hb := hasDerivAt_ell a
  have hquot := (hr.mul hh).div (hq.mul hb)
    (mul_ne_zero (q_pos a).ne' (ell_pos ha).ne')
  have hsum := (hasDerivAt_id a).add hquot
  have hy := ((hasDerivAt_const a 2).div_const (Real.log 2)).mul hsum
  convert! hy using 1
  simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply, id_eq,
    historicalYPrime]
  field_simp [(q_pos a).ne', (ell_pos ha).ne', (h_pos ha).ne',
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  rw [← one_sub_r_sq, ← h_add_a_mul_r]
  ring

theorem hasDerivAt_historicalYPrime (a : ℝ) (ha : 1 ≤ a) :
    HasDerivAt historicalYPrime
      (historicalYPrime a * (historicalE a + historicalX a)) a := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hh := hasDerivAt_h a
  have hb := hasDerivAt_ell a
  have hr := hasDerivAt_r a
  have hq := hasDerivAt_q a
  have hD := ((hasDerivAt_const a 2).mul hb).sub (hr.pow 2)
  have hnum := hh.mul hD
  have hden := hq.mul (hb.pow 2)
  have hfrac := hnum.div hden
    (mul_ne_zero (q_pos a).ne' (pow_ne_zero 2 (ell_pos ha0).ne'))
  have hy := ((hasDerivAt_const a 2).div_const (Real.log 2)).mul hfrac
  have hD0 : 2 * ell a - r a ^ 2 ≠ 0 := by
    have hl1 : 0 < l1 a := Real.log_pos (by linarith [z_pos a])
    have hell : 1 < ell a := by
      simp only [ell]
      linarith
    have hr0 := r_pos (lt_of_lt_of_le zero_lt_one ha)
    have hr1 := r_lt_one a
    have hrsq : r a ^ 2 < 1 := by nlinarith
    nlinarith
  convert! hy using 1
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply,
    Pi.div_apply, historicalYPrime, historicalE, historicalX]
  field_simp [(q_pos a).ne', (ell_pos ha0).ne', (h_pos ha0).ne', hD0,
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  rw [← one_sub_r_sq]
  ring

theorem historicalXPrime_pos (a : ℝ) (ha : 0 < a) :
    0 < historicalXPrime a := by
  unfold historicalXPrime
  exact div_pos
    (mul_pos (mul_pos (Real.log_pos (by norm_num)) (q_pos a)) (ell_pos ha))
    (mul_pos (by norm_num) (sq_pos_of_pos (h_pos ha)))

theorem historicalYPrime_pos (a : ℝ) (ha : 1 ≤ a) :
    0 < historicalYPrime a := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hl1 : 0 < l1 a := Real.log_pos (by linarith [z_pos a])
  have hell : 1 < ell a := by
    simp only [ell]
    linarith
  have hr0 := r_pos ha0
  have hr1 := r_lt_one a
  have hrsq : r a ^ 2 < 1 := by nlinarith
  unfold historicalYPrime
  apply mul_pos
  · exact div_pos (by norm_num) (Real.log_pos (by norm_num))
  · apply div_pos
    · exact mul_pos (h_pos ha0) (by linarith)
    · exact mul_pos (q_pos a) (sq_pos_of_pos (ell_pos ha0))

theorem xJet_d1_eq_historicalXPrime (a : ℝ) (ha : 0 < a) :
    xJet.d1 a = historicalXPrime a := by
  have hj : HasDerivAt X (xJet.d1 a) a := by
    convert (xJet_soundAt ha).1 using 1
    funext b
    exact (xJet_d0 b).symm
  exact hj.unique (hasDerivAt_X a ha)

theorem xJet_d2_eq_historicalXPrime_mul (a : ℝ) (ha : 0 < a) :
    xJet.d2 a = historicalXPrime a * historicalX a := by
  have heq : xJet.d1 =ᶠ[nhds a] historicalXPrime := by
    filter_upwards [Ioi_mem_nhds ha] with b hb
    exact xJet_d1_eq_historicalXPrime b hb
  have hj : HasDerivAt historicalXPrime (xJet.d2 a) a :=
    (xJet_soundAt ha).2.1.congr_of_eventuallyEq heq.symm
  exact hj.unique (hasDerivAt_historicalXPrime a ha)

theorem yJet_d1_eq_historicalYPrime (a : ℝ) (ha : 0 < a) :
    yJet.d1 a = historicalYPrime a := by
  have hj : HasDerivAt Y (yJet.d1 a) a := by
    convert (yJet_soundAt ha).1 using 1
    funext b
    exact (yJet_d0 b).symm
  exact hj.unique (hasDerivAt_Y a ha)

theorem yJet_d2_eq_historicalYPrime_mul (a : ℝ) (ha : 1 < a) :
    yJet.d2 a = historicalYPrime a * (historicalE a + historicalX a) := by
  have heq : yJet.d1 =ᶠ[nhds a] historicalYPrime := by
    filter_upwards [Ioi_mem_nhds ha] with b hb
    exact yJet_d1_eq_historicalYPrime b (lt_trans zero_lt_one hb)
  have hj : HasDerivAt historicalYPrime (yJet.d2 a) a :=
    (yJet_soundAt (lt_trans zero_lt_one ha)).2.1.congr_of_eventuallyEq heq.symm
  exact hj.unique (hasDerivAt_historicalYPrime a ha.le)

theorem stableX0_eq_historicalX (a : ℝ) (ha : 0 < a) :
    stableX0 a = historicalX a := by
  rw [stableX0, xJet_d1_eq_historicalXPrime a ha,
    xJet_d2_eq_historicalXPrime_mul a ha]
  exact mul_div_cancel_left₀ _ (historicalXPrime_pos a ha).ne'

theorem stableE_eq_historicalE (a : ℝ) (ha : 1 < a) :
    stableE a = historicalE a := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  rw [stableE, xJet_d1_eq_historicalXPrime a ha0,
    xJet_d2_eq_historicalXPrime_mul a ha0,
    yJet_d1_eq_historicalYPrime a ha0,
    yJet_d2_eq_historicalYPrime_mul a ha]
  field_simp [(historicalXPrime_pos a ha0).ne',
    (historicalYPrime_pos a ha.le).ne']
  ring

theorem hasDerivAt_historicalE (a : ℝ) (ha : 1 ≤ a) :
    HasDerivAt historicalE (historicalEPrime a) a := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hr := hasDerivAt_r a
  have hq := hasDerivAt_q a
  have hh := hasDerivAt_h a
  have hb := hasDerivAt_ell a
  have hD := ((hasDerivAt_const a 2).mul hb).sub (hr.pow 2)
  have hD0 : 2 * ell a - r a ^ 2 ≠ 0 := by
    have hl1 : 0 < l1 a := Real.log_pos (by linarith [z_pos a])
    have hell : 1 < ell a := by simp only [ell]; linarith
    have hr0 := r_pos ha0
    have hr1 := r_lt_one a
    have hrsq : r a ^ 2 < 1 := by nlinarith
    nlinarith
  have hterm1 := (((hasDerivAt_const a (-3)).mul (hasDerivAt_id a)).mul hq).div hh
    (h_pos ha0).ne'
  have hterm2 := (((hasDerivAt_const a 2).mul (hr.pow 3))).div hD hD0
  have hterm3 := (hasDerivAt_const a 4).mul hr
  have hterm4 := ((hasDerivAt_const a 3).mul hr).div hb (ell_pos ha0).ne'
  have hder := ((hterm1.add hterm2).add hterm3).sub hterm4
  convert! hder using 1
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply,
    Pi.div_apply, id_eq, historicalE, historicalEPrime]
  field_simp [(h_pos ha0).ne', (ell_pos ha0).ne', hD0]
  rw [← one_sub_r_sq]
  ring

theorem hasDerivAt_stableE (a : ℝ) (ha : 0 < a)
    (hx : xJet.d1 a ≠ 0) (hy : yJet.d1 a ≠ 0) :
    HasDerivAt stableE (stableEPrime a) a := by
  have xs := xJet_soundAt ha
  have ys := yJet_soundAt ha
  have hyq := ys.2.2.1.div ys.2.1 hy
  have hxq := xs.2.2.1.div xs.2.1 hx
  have hder := hyq.sub hxq
  convert! hder using 1 <;>
    simp only [Pi.sub_apply, Pi.div_apply, stableE, stableEPrime] <;> ring

theorem stableEPrime_eq_historicalEPrime (a : ℝ) (ha : 1 < a) :
    stableEPrime a = historicalEPrime a := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hx : xJet.d1 a ≠ 0 := by
    rw [xJet_d1_eq_historicalXPrime a ha0]
    exact (historicalXPrime_pos a ha0).ne'
  have hy : yJet.d1 a ≠ 0 := by
    rw [yJet_d1_eq_historicalYPrime a ha0]
    exact (historicalYPrime_pos a ha.le).ne'
  have heq : historicalE =ᶠ[nhds a] stableE := by
    filter_upwards [Ioi_mem_nhds ha] with b hb
    exact (stableE_eq_historicalE b hb).symm
  have hs : HasDerivAt historicalE (stableEPrime a) a :=
    (hasDerivAt_stableE a ha0 hx hy).congr_of_eventuallyEq heq
  exact hs.unique (hasDerivAt_historicalE a ha.le)

theorem regLog1p_z (a : ℝ) :
    E8RegularizedLog1p.regLog1p (z a) = l1 a / z a := by
  rw [E8RegularizedLog1p.regLog1p_eq (z_pos a).ne']
  rfl

theorem regLog1pPrime_z (a : ℝ) :
    E8RegularizedLog1p.regLog1pPrime (z a) =
      (1 / (1 + z a) - l1 a / z a) / z a := by
  rw [E8RegularizedLog1p.regLog1pPrime_eq (z_pos a).ne']
  simp only [l1]
  field_simp [(z_pos a).ne', (one_add_z_pos a).ne']

theorem z_eq_one_sub_r_div (a : ℝ) :
    z a = (1 - r a) / (1 + r a) := by
  unfold r
  field_simp [(one_add_z_pos a).ne']
  ring

theorem l1_eq_h_sub (a : ℝ) :
    l1 a = h a - a * (1 - r a) := by
  rw [one_sub_r]
  unfold h
  ring

theorem tail_r_z (a : ℝ) :
    E8HistoricalTailFormula.r (z a) = r a := rfl

theorem tail_B_z (a : ℝ) (ha : 0 < a) :
    E8HistoricalTailFormula.B (1 / a) (z a) = ell a / a := by
  simp only [E8HistoricalTailFormula.B, regLog1p_z, ell]
  field_simp [ha.ne', (z_pos a).ne']

theorem tail_G_z (a : ℝ) (ha : 0 < a) :
    E8HistoricalTailFormula.G (1 / a) (z a) = h a / (a * z a) := by
  simp only [E8HistoricalTailFormula.G, regLog1p_z, h]
  field_simp [ha.ne', (z_pos a).ne', (one_add_z_pos a).ne']

theorem tail_qh_z (a : ℝ) (ha : 0 < a) :
    E8HistoricalTailFormula.qh (1 / a) (z a) = a * q a / h a := by
  simp only [E8HistoricalTailFormula.qh, E8HistoricalTailFormula.qhDen,
    tail_G_z a ha, q]
  field_simp [ha.ne', (z_pos a).ne', (one_add_z_pos a).ne', (h_pos ha).ne']

theorem tail_C_z (a : ℝ) (ha : 0 < a) :
    E8HistoricalTailFormula.C (1 / a) (z a) =
      (2 * ell a - r a ^ 2) / a := by
  simp only [E8HistoricalTailFormula.C, tail_B_z a ha, tail_r_z]
  field_simp [ha.ne']

theorem tail_X_eq_historicalX (a : ℝ) (ha : 0 < a) :
    E8HistoricalTailFormula.X (1 / a) (z a) = historicalX a := by
  simp only [E8HistoricalTailFormula.X, tail_r_z, tail_B_z a ha,
    tail_qh_z a ha, historicalX]
  field_simp [ha.ne', (ell_pos ha).ne', (h_pos ha).ne']

theorem tail_E_eq_historicalE (a : ℝ) (ha : 1 ≤ a) :
    E8HistoricalTailFormula.E (1 / a) (z a) = historicalE a := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hD0 : 2 * ell a - r a ^ 2 ≠ 0 := by
    have hl1 : 0 < l1 a := Real.log_pos (by linarith [z_pos a])
    have hell : 1 < ell a := by simp only [ell]; linarith
    have hr0 := r_pos ha0
    have hr1 := r_lt_one a
    have hrsq : r a ^ 2 < 1 := by nlinarith
    nlinarith
  simp only [E8HistoricalTailFormula.E, tail_qh_z a ha0, tail_r_z,
    tail_C_z a ha0, tail_B_z a ha0, historicalE]
  field_simp [ha0.ne', (ell_pos ha0).ne', (h_pos ha0).ne', hD0]

set_option maxRecDepth 100000 in
theorem tail_Ealpha_eq_historicalEPrime (a : ℝ) (ha : 1 ≤ a) :
    E8HistoricalTailFormula.Ealpha (1 / a) (z a) = historicalEPrime a := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hD0 : 2 * ell a - r a ^ 2 ≠ 0 := by
    have hl1 : 0 < l1 a := Real.log_pos (by linarith [z_pos a])
    have hell : 1 < ell a := by simp only [ell]; linarith
    have hr0 := r_pos ha0
    have hr1 := r_lt_one a
    have hrsq : r a ^ 2 < 1 := by nlinarith
    nlinarith
  simp only [E8HistoricalTailFormula.Ealpha,
    E8HistoricalTailFormula.Ev, E8HistoricalTailFormula.Eu,
    E8HistoricalTailFormula.qhV, E8HistoricalTailFormula.qhU,
    E8HistoricalTailFormula.Cv, E8HistoricalTailFormula.Cu,
    E8HistoricalTailFormula.Bv, E8HistoricalTailFormula.Bu,
    E8HistoricalTailFormula.Gv, E8HistoricalTailFormula.Gu,
    E8HistoricalTailFormula.rPrime, tail_r_z,
    tail_B_z a ha0, tail_G_z a ha0, tail_C_z a ha0,
    E8HistoricalTailFormula.qhDen, regLog1p_z, regLog1pPrime_z,
    historicalEPrime]
  rw [z_eq_one_sub_r_div, l1_eq_h_sub]
  field_simp [ha0.ne', (z_pos a).ne', (one_add_z_pos a).ne',
    (one_add_r_pos a).ne', (one_sub_r_pos a).ne',
    (ell_pos ha0).ne', (h_pos ha0).ne', hD0]
  rw [← one_sub_r_sq, ← h_add_a_mul_r]
  ring

/-- Exact symbolic identification of the historical two-variable scalar with
the stable-parameter logarithmic-convexity scalar.  The mild `1 < a`
hypothesis is far weaker than the production tail cut `a ≥ 20`; it is used
only to discharge the visibly positive denominator `2β-r²`. -/
theorem historicalTailFormula_L_eq_stableL (a : ℝ) (ha : 1 < a) :
    E8HistoricalTailFormula.L (1 / a) (Real.exp (-2 * a)) = stableL a := by
  change E8HistoricalTailFormula.L (1 / a) (z a) = stableL a
  simp only [E8HistoricalTailFormula.L, stableL,
    tail_E_eq_historicalE a ha.le,
    tail_Ealpha_eq_historicalEPrime a ha.le,
    tail_X_eq_historicalX a (lt_trans zero_lt_one ha),
    stableE_eq_historicalE a ha,
    stableEPrime_eq_historicalEPrime a ha,
    stableX0_eq_historicalX a (lt_trans zero_lt_one ha)]

set_option maxRecDepth 100000 in
theorem historicalTailFormula_L_zero (v : ℝ)
    (hm : v ≠ -2) (hp : v ≠ 2) :
    E8HistoricalTailFormula.L v 0 =
      v ^ 2 *
        ((3 * v ^ 4 - 4 * v ^ 3 + 48 * v ^ 2 - 48 * v + 16) /
          (v ^ 2 - 4) ^ 2) := by
  have hp' : 2 - v ≠ 0 := by
    intro hz
    apply hp
    linarith
  have hm' : 2 + v ≠ 0 := by
    intro hz
    apply hm
    linarith
  have hpp : 4 - v * 4 + v ^ 2 ≠ 0 := by
    have : 4 - v * 4 + v ^ 2 = (2 - v) ^ 2 := by ring
    rw [this]
    exact pow_ne_zero 2 hp'
  have hmm : 4 + v * 4 + v ^ 2 ≠ 0 := by
    have : 4 + v * 4 + v ^ 2 = (2 + v) ^ 2 := by ring
    rw [this]
    exact pow_ne_zero 2 hm'
  have hbig : 16 - v ^ 2 * 8 + v ^ 4 ≠ 0 := by
    have : 16 - v ^ 2 * 8 + v ^ 4 = (v ^ 2 - 4) ^ 2 := by ring
    rw [this]
    apply pow_ne_zero
    intro hz
    have hf : (v - 2) * (v + 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hf | hf
    · apply hp; linarith
    · apply hm; linarith
  have hvp : v + 2 ≠ 0 := by
    intro hz
    apply hm
    linarith
  have hvm : v - 2 ≠ 0 := by
    intro hz
    apply hp
    linarith
  have hquad : v ^ 2 - 4 ≠ 0 := by
    intro hz
    have hf : (v - 2) * (v + 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hf | hf
    · exact hvm hf
    · exact hvp hf
  simp only [E8HistoricalTailFormula.L, E8HistoricalTailFormula.E,
    E8HistoricalTailFormula.Ealpha, E8HistoricalTailFormula.Ev,
    E8HistoricalTailFormula.Eu, E8HistoricalTailFormula.X,
    E8HistoricalTailFormula.qh, E8HistoricalTailFormula.qhDen,
    E8HistoricalTailFormula.qhV, E8HistoricalTailFormula.qhU,
    E8HistoricalTailFormula.C, E8HistoricalTailFormula.Cv,
    E8HistoricalTailFormula.Cu, E8HistoricalTailFormula.B,
    E8HistoricalTailFormula.Bv, E8HistoricalTailFormula.Bu,
    E8HistoricalTailFormula.G, E8HistoricalTailFormula.Gv,
    E8HistoricalTailFormula.Gu, E8HistoricalTailFormula.r,
    E8HistoricalTailFormula.rPrime,
    E8RegularizedLog1p.regLog1p_zero,
    E8RegularizedLog1p.regLog1pPrime_zero]
  norm_num
  field_simp [hvp, hvm, hquad, hm', hp']
  ring

theorem historicalTailFormula_L_zero_scaled_lower {v : ℝ}
    (hv0 : 0 ≤ v) (hv : v ≤ 1 / 20) :
    (27 / 32 : ℝ) * v ^ 2 ≤ E8HistoricalTailFormula.L v 0 := by
  have hm : v ≠ -2 := by linarith
  have hp : v ≠ 2 := by linarith
  rw [historicalTailFormula_L_zero v hm hp]
  have hv2 : v ^ 2 ≤ 1 / 400 := by nlinarith
  have hv3 : v ^ 3 ≤ 1 / 8000 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hv) (sq_nonneg v)]
  have hv4 : 0 ≤ v ^ 4 := by positivity
  have hnum : (27 / 2 : ℝ) ≤
      3 * v ^ 4 - 4 * v ^ 3 + 48 * v ^ 2 - 48 * v + 16 := by
    nlinarith
  have hden0 : 0 < (v ^ 2 - 4) ^ 2 := sq_pos_of_ne_zero (by nlinarith)
  have hden : (v ^ 2 - 4) ^ 2 ≤ 16 := by nlinarith [sq_nonneg (v ^ 2)]
  have hrat : (27 / 32 : ℝ) ≤
      (3 * v ^ 4 - 4 * v ^ 3 + 48 * v ^ 2 - 48 * v + 16) /
        (v ^ 2 - 4) ^ 2 := by
    apply (le_div_iff₀ hden0).2
    nlinarith
  simpa [mul_comm] using mul_le_mul_of_nonneg_right hrat (sq_nonneg v)

#print axioms historicalTailFormula_L_eq_stableL
#print axioms historicalTailFormula_L_zero_scaled_lower

end GeneralCK.Certificates.E8HistoricalLogConvexityBridge

end


