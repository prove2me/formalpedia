-- Prove2me | solution 1 for AdvSellUpgrade.Online.cutoff_order
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:17:50.968053+00:00
-- url     : https://prove2.me/submissions/c78404bd-610b-4274-aa46-fc6c72a07181

import Mathlib
import Definitions.Def_AdvSellUpgrade_Online_Setting
set_option autoImplicit false
open AdvSellUpgrade.Online

theorem gg_cform (mu cbar lam : ℝ) (hl : 0 < lam) (hlm : lam < mu) :
    cFn mu cbar lam = cbar * (Real.sqrt (mu - lam) / (Real.sqrt mu + Real.sqrt (mu - lam))) := by
  have hmu : 0 < mu := by linarith
  have hx : 0 < mu - lam := by linarith
  set m := Real.sqrt mu with hm
  set r := Real.sqrt (mu - lam) with hr
  have hm0 : 0 < m := Real.sqrt_pos.mpr hmu
  have hr0 : 0 < r := Real.sqrt_pos.mpr hx
  have hm2 : m ^ 2 = mu := Real.sq_sqrt hmu.le
  have hr2 : r ^ 2 = mu - lam := Real.sq_sqrt hx.le
  have hprod : Real.sqrt (mu * (mu - lam)) = m * r := by
    rw [Real.sqrt_mul hmu.le]
  have hmr : r < m := by nlinarith
  have hlam : lam = (m - r) * (m + r) := by nlinarith
  unfold cFn
  rw [hprod]
  have h1 : m - r ≠ 0 := by linarith
  have h2 : m + r ≠ 0 := by linarith
  have h3 : mu - lam = r ^ 2 := hr2.symm
  rw [h3, hlam]
  field_simp

theorem gg_frac_lt (mu lam : ℝ) (hl : 0 < lam) (hlm : lam < mu) :
    0 < Real.sqrt (mu - lam) / (Real.sqrt mu + Real.sqrt (mu - lam)) ∧
    Real.sqrt (mu - lam) / (Real.sqrt mu + Real.sqrt (mu - lam)) < 1 := by
  have hmu : 0 < mu := by linarith
  have hx : 0 < mu - lam := by linarith
  have hm0 : 0 < Real.sqrt mu := Real.sqrt_pos.mpr hmu
  have hr0 : 0 < Real.sqrt (mu - lam) := Real.sqrt_pos.mpr hx
  constructor
  · positivity
  · rw [div_lt_one (by positivity)]; linarith

theorem solution (P : Params) (hP : P.Standing) :
    0 < cFn P.mu P.cbar P.lamH ∧ cFn P.mu P.cbar P.lamH < cFn P.mu P.cbar P.lamL ∧
      cFn P.mu P.cbar P.lamL < P.cbar := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := hP
  have hH : 0 < P.lamH := by linarith
  rw [gg_cform _ _ _ hH h3, gg_cform _ _ _ h1 (by linarith)]
  obtain ⟨a1, a2⟩ := gg_frac_lt P.mu P.lamH hH h3
  obtain ⟨b1, b2⟩ := gg_frac_lt P.mu P.lamL h1 (by linarith)
  have hmu : 0 < P.mu := by linarith
  have hm0 : 0 < Real.sqrt P.mu := Real.sqrt_pos.mpr hmu
  have hxH : 0 < P.mu - P.lamH := by linarith
  have hxL : 0 < P.mu - P.lamL := by linarith
  have hrH : 0 < Real.sqrt (P.mu - P.lamH) := Real.sqrt_pos.mpr hxH
  have hrL : 0 < Real.sqrt (P.mu - P.lamL) := Real.sqrt_pos.mpr hxL
  have hlt : Real.sqrt (P.mu - P.lamH) < Real.sqrt (P.mu - P.lamL) :=
    Real.sqrt_lt_sqrt hxH.le (by linarith)
  refine ⟨by positivity, ?_, by nlinarith⟩
  have : Real.sqrt (P.mu - P.lamH) / (Real.sqrt P.mu + Real.sqrt (P.mu - P.lamH)) <
      Real.sqrt (P.mu - P.lamL) / (Real.sqrt P.mu + Real.sqrt (P.mu - P.lamL)) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hm0 (sub_pos.mpr hlt)]
  exact mul_lt_mul_of_pos_left this h4
