-- Prove2me | solution 1 for AuditWhistle.Intensity.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T21:26:43.485896+00:00
-- url     : https://prove2.me/submissions/11e2c832-ce98-4ccf-91a1-36c84abae5f7

import Mathlib
import Definitions.Def_AuditWhistle_Intensity_Setting

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace AWPf

open AuditWhistle.Intensity

def q1f (p β x : ℝ) : ℝ := (1-p)*(1-x)*β / ((1-p)*(1-x)*β + p*(1-β))

def q0f (p β τ x : ℝ) : ℝ :=
  (1-p)*(1-x)*(1-β*τ) / ((1-p)*(1-x)*(1-β*τ) + p*(1-(1-β)*τ))

def Pf (p β r τ x : ℝ) : ℝ := β*τ*min 1 (r*q1f p β x) + (1-β*τ)*(r*q0f p β τ x)

def G0 (p β τ x : ℝ) : ℝ :=
  (1-p)*(1-x)*(1-β*τ)*(-β*((1-p)*(1-x))*(1-β*τ) - 2*β*p*(1-(1-β)*τ) + p*(1-β)*(1-β*τ)) /
    ((1-p)*(1-x)*(1-β*τ) + p*(1-(1-β)*τ))^2

def Ptau (p β r τ x : ℝ) : ℝ := β * min 1 (r*q1f p β x) + r * G0 p β τ x

def H (p β r τ U : ℝ) : ℝ :=
  β*(U*(1-β*τ)+p*(1-(1-β)*τ))^2 +
    r*U*(1-β*τ)*(-β*U*(1-β*τ) - 2*β*p*(1-(1-β)*τ) + p*(1-β)*(1-β*τ))

theorem hasDerivAt_Pf {p β r τ x : ℝ}
    (hden : (1-p)*(1-x)*(1-β*τ) + p*(1-(1-β)*τ) ≠ 0) :
    HasDerivAt (fun t => Pf p β r t x) (Ptau p β r τ x) τ := by
  have h1 : HasDerivAt (fun t : ℝ => β*t) β τ := by
    simpa using (hasDerivAt_id τ).const_mul β
  have hs : HasDerivAt (fun t : ℝ => 1 - β*t) (-β) τ := h1.const_sub 1
  have hw : HasDerivAt (fun t : ℝ => 1 - (1-β)*t) (-(1-β)) τ := by
    simpa using ((hasDerivAt_id τ).const_mul (1-β)).const_sub 1
  have hN : HasDerivAt (fun t : ℝ => (1-p)*(1-x)*(1-β*t)) ((1-p)*(1-x)*(-β)) τ :=
    hs.const_mul _
  have hD : HasDerivAt (fun t : ℝ => (1-p)*(1-x)*(1-β*t) + p*(1-(1-β)*t))
      ((1-p)*(1-x)*(-β) + p*(-(1-β))) τ := hN.add (hw.const_mul p)
  have hq : HasDerivAt (fun t : ℝ => (1-p)*(1-x)*(1-β*t) / ((1-p)*(1-x)*(1-β*t) + p*(1-(1-β)*t)))
      (((1-p)*(1-x)*(-β) * ((1-p)*(1-x)*(1-β*τ) + p*(1-(1-β)*τ)) -
        (1-p)*(1-x)*(1-β*τ) * ((1-p)*(1-x)*(-β) + p*(-(1-β)))) /
        ((1-p)*(1-x)*(1-β*τ) + p*(1-(1-β)*τ))^2) τ := hN.div hD hden
  have hall : HasDerivAt (fun t => Pf p β r t x)
      (β * min 1 (r*q1f p β x) + ((-β) * (r * ((1-p)*(1-x)*(1-β*τ) /
          ((1-p)*(1-x)*(1-β*τ) + p*(1-(1-β)*τ)))) + (1-β*τ) * (r *
        (((1-p)*(1-x)*(-β) * ((1-p)*(1-x)*(1-β*τ) + p*(1-(1-β)*τ)) -
        (1-p)*(1-x)*(1-β*τ) * ((1-p)*(1-x)*(-β) + p*(-(1-β)))) /
        ((1-p)*(1-x)*(1-β*τ) + p*(1-(1-β)*τ))^2)))) τ :=
    (h1.mul_const (min 1 (r*q1f p β x))).add (hs.mul (hq.const_mul r))
  refine hall.congr_deriv ?_
  unfold Ptau G0
  field_simp
  ring

section pos
variable {p β r τ x : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 1/2 < β) (hβ1 : β < 1)
  (hτ0 : 0 < τ) (hτ1 : τ < 1)
include hp0 hp1 hβ0 hβ1 hτ0 hτ1

theorem s_pos : 0 < 1 - β*τ := by nlinarith
theorem w_pos : 0 < 1 - (1-β)*τ := by nlinarith

theorem den0_pos (hx : x < 1) : 0 < (1-p)*(1-x)*(1-β*τ) + p*(1-(1-β)*τ) := by
  have := s_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1
  have := w_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1
  have : 0 < (1-p)*(1-x) := mul_pos (by linarith) (by linarith)
  positivity

theorem den1_pos (hx : x < 1) : 0 < (1-p)*(1-x)*β + p*(1-β) := by
  have : 0 < (1-p)*(1-x) := mul_pos (by linarith) (by linarith)
  have : 0 < 1 - β := by linarith
  have : 0 < β := by linarith
  positivity

theorem interior_pos (hx : x < 1) : 0 < β * q1f p β x + G0 p β τ x := by
  have hs := s_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1
  have hw := w_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1
  have hd0 := den0_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 hx
  have hd1 := den1_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 hx
  have hU : 0 < (1-p)*(1-x) := mul_pos (by linarith) (by linarith)
  have key : β * q1f p β x + G0 p β τ x =
      p^2*((1-p)*(1-x))*(2*β-1)^2 / (((1-p)*(1-x)*β + p*(1-β)) *
        ((1-p)*(1-x)*(1-β*τ) + p*(1-(1-β)*τ))^2) := by
    have h0 := hd0.ne'
    have h1 := hd1.ne'
    have hq : q1f p β x * ((1-p)*(1-x)*β + p*(1-β)) = (1-p)*(1-x)*β := by
      unfold q1f; exact div_mul_cancel₀ _ h1
    have hG : G0 p β τ x * ((1-p)*(1-x)*(1-β*τ) + p*(1-(1-β)*τ))^2 =
        (1-p)*(1-x)*(1-β*τ)*(-β*((1-p)*(1-x))*(1-β*τ) - 2*β*p*(1-(1-β)*τ) + p*(1-β)*(1-β*τ)) := by
      unfold G0; exact div_mul_cancel₀ _ (pow_ne_zero 2 h0)
    rw [eq_div_iff (mul_ne_zero h1 (pow_ne_zero 2 h0))]
    have expand : (β * q1f p β x + G0 p β τ x) * (((1-p)*(1-x)*β + p*(1-β)) *
        ((1-p)*(1-x)*(1-β*τ) + p*(1-(1-β)*τ))^2)
        = β * (q1f p β x * ((1-p)*(1-x)*β + p*(1-β))) * ((1-p)*(1-x)*(1-β*τ) + p*(1-(1-β)*τ))^2
          + (G0 p β τ x * ((1-p)*(1-x)*(1-β*τ) + p*(1-(1-β)*τ))^2) * ((1-p)*(1-x)*β + p*(1-β)) := by
      ring
    rw [expand, hq, hG]
    ring
  rw [key]
  have : 0 < 2*β - 1 := by linarith
  positivity

theorem betaG_eq (hx : x < 1) : β + r * G0 p β τ x =
    H p β r τ ((1-p)*(1-x)) / ((1-p)*(1-x)*(1-β*τ) + p*(1-(1-β)*τ))^2 := by
  have hd0 := den0_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 hx
  have h0 := pow_ne_zero 2 hd0.ne'
  have hG : G0 p β τ x * ((1-p)*(1-x)*(1-β*τ) + p*(1-(1-β)*τ))^2 =
      (1-p)*(1-x)*(1-β*τ)*(-β*((1-p)*(1-x))*(1-β*τ) - 2*β*p*(1-(1-β)*τ) + p*(1-β)*(1-β*τ)) := by
    unfold G0; exact div_mul_cancel₀ _ h0
  rw [eq_div_iff h0, add_mul, mul_assoc r, hG]
  unfold H
  ring

theorem q1f_lt_one (hx : x < 1) : q1f p β x < 1 := by
  have hd1 := den1_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 hx
  unfold q1f
  rw [div_lt_one hd1]
  nlinarith

theorem q1f_nonneg (hx : x < 1) : 0 ≤ q1f p β x := by
  have hd1 := den1_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 hx
  have : 0 < (1-p)*(1-x) := mul_pos (by linarith) (by linarith)
  unfold q1f
  apply div_nonneg _ hd1.le
  nlinarith

theorem q0f_pos (hx : x < 1) : 0 < q0f p β τ x := by
  have hd0 := den0_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 hx
  have hs := s_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1
  have : 0 < (1-p)*(1-x) := mul_pos (by linarith) (by linarith)
  unfold q0f
  apply div_pos _ hd0
  positivity

theorem q0f_lt (hx0 : 0 ≤ x) (hx : x < 1) : q0f p β τ x < 1 - p := by
  have hd0 := den0_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 hx
  have hs := s_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1
  have hw := w_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1
  unfold q0f
  rw [div_lt_iff₀ hd0]
  have h1 : (1-x)*(1-β*τ) < 1-(1-β)*τ := by nlinarith
  have h2 : 0 < p*(1-p) := mul_pos hp0 (by linarith)
  nlinarith [mul_lt_mul_of_pos_left h1 h2]

theorem r_q0f_lt_one (hr0 : 0 < r) (hr : r < 1/(1-p)) (hx0 : 0 ≤ x) (hx : x < 1) :
    r * q0f p β τ x < 1 := by
  have h := q0f_lt hp0 hp1 hβ0 hβ1 hτ0 hτ1 hx0 hx
  have h1 : r * (1-p) < 1 := by
    rw [lt_div_iff₀ (by linarith)] at hr
    linarith
  have h2 : r * q0f p β τ x < r * (1-p) := mul_lt_mul_of_pos_left h hr0
  linarith

theorem Ptau_neg_imp (hr0 : 0 < r) (hx : x < 1) (h : Ptau p β r τ x < 0) :
    1 < r * q1f p β x := by
  by_contra hc
  push_neg at hc
  have hip := interior_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 (x := x) hx
  have hm : min 1 (r * q1f p β x) = r * q1f p β x := min_eq_right hc
  unfold Ptau at h
  rw [hm] at h
  nlinarith [mul_pos hr0 hip]

theorem Ptau_neg_iff (hr0 : 0 < r) (hx : x < 1) :
    Ptau p β r τ x < 0 ↔ H p β r τ ((1-p)*(1-x)) < 0 := by
  have hd0 := den0_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 hx
  have hD2 : 0 < ((1-p)*(1-x)*(1-β*τ) + p*(1-(1-β)*τ))^2 := by positivity
  have he := betaG_eq hp0 hp1 hβ0 hβ1 hτ0 hτ1 (r := r) hx
  have hip := interior_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 (x := x) hx
  have hbg : β + r * G0 p β τ x < 0 ↔ H p β r τ ((1-p)*(1-x)) < 0 := by
    rw [he, div_lt_iff₀ hD2, zero_mul]
  rcases le_or_gt 1 (r * q1f p β x) with hc | hc
  · have hm : min 1 (r * q1f p β x) = 1 := min_eq_left hc
    unfold Ptau
    rw [hm, mul_one]
    exact hbg
  · have hm : min 1 (r * q1f p β x) = r * q1f p β x := min_eq_right hc.le
    have hpos : 0 < Ptau p β r τ x := by
      unfold Ptau; rw [hm]; nlinarith [mul_pos hr0 hip]
    have hβp : 0 < β := by linarith
    have hpos2 : 0 < β + r * G0 p β τ x := by
      have : β * (r * q1f p β x) < β := by nlinarith
      nlinarith [mul_pos hr0 hip]
    constructor
    · intro h; linarith
    · intro h; exact absurd (hbg.mpr h) (by linarith)

theorem H_neg_r_gt_one (hr0 : 0 < r) {U : ℝ} (hU : 0 < U) (h : H p β r τ U < 0) : 1 < r := by
  have hs := s_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1
  have hw := w_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1
  by_contra hc
  push_neg at hc
  have e : H p β r τ U = β*U^2*(1-β*τ)^2*(1-r) + 2*β*U*(1-β*τ)*p*(1-(1-β)*τ)*(1-r)
      + β*p^2*(1-(1-β)*τ)^2 + r*p*(1-β)*U*(1-β*τ)^2 := by unfold H; ring
  have h1r : 0 ≤ 1 - r := by linarith
  have hβp : 0 < β := by linarith
  have h1b : 0 < 1 - β := by linarith
  have t1 : 0 ≤ β*U^2*(1-β*τ)^2*(1-r) := by positivity
  have t2 : 0 ≤ 2*β*U*(1-β*τ)*p*(1-(1-β)*τ)*(1-r) := by positivity
  have t3 : 0 < β*p^2*(1-(1-β)*τ)^2 := by positivity
  have t4 : 0 ≤ r*p*(1-β)*U*(1-β*τ)^2 := by positivity
  linarith

theorem H_mono (hr0 : 0 < r) {U U' : ℝ} (hU : 0 < U) (hUU : U ≤ U') (h : H p β r τ U < 0) :
    H p β r τ U' < 0 := by
  have hr1 := H_neg_r_gt_one hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0 hU h
  have hs := s_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1
  have hw := w_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1
  have hβp : 0 < β := by linarith
  have e : H p β r τ U' * U - H p β r τ U * U' =
      (U' - U) * (β*(1-β*τ)^2*(1-r)*U*U' - β*p^2*(1-(1-β)*τ)^2) := by unfold H; ring
  have hα : β*(1-β*τ)^2*(1-r)*U*U' ≤ 0 := by
    have : 0 ≤ β*(1-β*τ)^2*(r-1)*U*U' := by
      have : 0 ≤ r - 1 := by linarith
      have : 0 ≤ U' := by linarith
      positivity
    nlinarith
  have hc : 0 < β*p^2*(1-(1-β)*τ)^2 := by positivity
  have hprod : (U' - U) * (β*(1-β*τ)^2*(1-r)*U*U' - β*p^2*(1-(1-β)*τ)^2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hU' : 0 < U' := by linarith
  have : H p β r τ U' * U < 0 := by nlinarith
  by_contra hc2
  push_neg at hc2
  nlinarith

theorem H_rstar : H p β r τ (1-p) < 0 ↔ rStar p β τ < r := by
  have hs := s_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1
  have hβp : 0 < β := by linarith
  have hQ : 0 < β - β^2*τ + (2*β-1)*p*(β*τ+1) := by
    have : 0 < β*(1-β*τ) := by positivity
    have : 0 < (2*β-1)*p*(β*τ+1) := by
      have : 0 < 2*β-1 := by linarith
      positivity
    nlinarith
  have hden : 0 < (p-1)*(β*τ-1)*(β - β^2*τ + (2*β-1)*p*(β*τ+1)) := by
    have : 0 < (p-1)*(β*τ-1) := by nlinarith
    positivity
  have e : H p β r τ (1-p) = β*(τ*(β-2*β*p+p)-1)^2 -
      r * ((p-1)*(β*τ-1)*(β - β^2*τ + (2*β-1)*p*(β*τ+1))) := by unfold H; ring
  unfold rStar
  rw [div_lt_iff₀ hden, e]
  constructor <;> intro h <;> linarith

theorem q1f_anti {x y : ℝ} (hxy : x ≤ y) (hy : y < 1) : q1f p β y ≤ q1f p β x := by
  have hx : x < 1 := by linarith
  have h1 := den1_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 hx
  have h2 := den1_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 hy
  unfold q1f
  rw [div_le_div_iff₀ h2 h1]
  have : 0 < p*(1-β)*β*(1-p) := by
    have : 0 < 1-β := by linarith
    have : 0 < β := by linarith
    have : 0 < 1-p := by linarith
    positivity
  nlinarith

theorem q0f_anti {x y : ℝ} (hxy : x ≤ y) (hy : y < 1) : q0f p β τ y ≤ q0f p β τ x := by
  have hx : x < 1 := by linarith
  have h1 := den0_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 hx
  have h2 := den0_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 hy
  have hs := s_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1
  have hw := w_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1
  unfold q0f
  rw [div_le_div_iff₀ h2 h1]
  have : 0 < p*(1-(1-β)*τ)*(1-β*τ)*(1-p) := by
    have : 0 < 1-p := by linarith
    positivity
  nlinarith

theorem Pf_anti (hr0 : 0 < r) {x y : ℝ} (hxy : x ≤ y) (hy : y < 1) :
    Pf p β r τ y ≤ Pf p β r τ x := by
  have h1 := q1f_anti hp0 hp1 hβ0 hβ1 hτ0 hτ1 hxy hy
  have h0 := q0f_anti hp0 hp1 hβ0 hβ1 hτ0 hτ1 hxy hy
  have hs := s_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1
  have hβp : 0 < β := by linarith
  unfold Pf
  have hm : min 1 (r * q1f p β y) ≤ min 1 (r * q1f p β x) :=
    min_le_min_left _ (mul_le_mul_of_nonneg_left h1 hr0.le)
  have a1 : β*τ*min 1 (r * q1f p β y) ≤ β*τ*min 1 (r * q1f p β x) :=
    mul_le_mul_of_nonneg_left hm (by positivity)
  have a2 : (1-β*τ)*(r*q0f p β τ y) ≤ (1-β*τ)*(r*q0f p β τ x) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h0 hr0.le) hs.le
  linarith

theorem Pf_pos (hr0 : 0 < r) (hx : x < 1) : 0 < Pf p β r τ x := by
  have hq0 := q0f_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 hx
  have hq1 := q1f_nonneg hp0 hp1 hβ0 hβ1 hτ0 hτ1 hx
  have hs := s_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1
  have hβp : 0 < β := by linarith
  unfold Pf
  have : 0 ≤ min 1 (r * q1f p β x) := le_min zero_le_one (by positivity)
  have : 0 ≤ β*τ*min 1 (r * q1f p β x) := by positivity
  have : 0 < (1-β*τ)*(r*q0f p β τ x) := by positivity
  linarith

end pos

end AWPf




namespace AWPg

open Filter Topology

/-- pure real fact: X = Y + N with X*Y ≤ 0 -/
theorem bound_basic {X Y N : ℝ} (hXY : X = Y + N) (hm : X * Y ≤ 0) :
    |X| ≤ |N| ∧ min 0 N ≤ X := by
  constructor
  · have e : X * X = X * Y + X * N := by
      calc X * X = X * (Y + N) := by rw [← hXY]
        _ = X * Y + X * N := by ring
    have h1 : X^2 ≤ X*N := by nlinarith
    have h2 : X*N ≤ |X| * |N| := by
      rw [← abs_mul]; exact le_abs_self _
    have h3 : |X|^2 ≤ |X| * |N| := by rw [sq_abs]; linarith
    rcases (abs_nonneg X).lt_or_eq with h | h
    · nlinarith
    · rw [← h]; exact abs_nonneg _
  · rcases le_or_gt 0 X with h | h
    · exact le_trans (min_le_left _ _) h
    · have : 0 ≤ Y := by
        by_contra hc; push_neg at hc; nlinarith
      exact le_trans (min_le_right _ _) (by linarith)

/-- one-sided slope bound gives a nonnegative derivative -/
theorem deriv_nonneg_of_lower {A G : ℝ → ℝ} {τ v Gτ c : ℝ} (hc : 0 < c)
    (hA : HasDerivAt A v τ) (hG : HasDerivAt G Gτ τ) (hGτ : 0 ≤ Gτ)
    (hlow : ∀ᶠ t in 𝓝 τ, min 0 (c * (G t - G τ)) ≤ A t - A τ) : 0 ≤ v := by
  have hsA : Tendsto (slope A τ) (𝓝[>] τ) (𝓝 v) :=
    (hasDerivAt_iff_tendsto_slope.mp hA).mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))
  have hsG : Tendsto (slope G τ) (𝓝[>] τ) (𝓝 Gτ) :=
    (hasDerivAt_iff_tendsto_slope.mp hG).mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))
  have hL : Tendsto (fun t => min 0 (c * slope G τ t)) (𝓝[>] τ) (𝓝 (min 0 (c * Gτ))) :=
    tendsto_const_nhds.min (tendsto_const_nhds.mul hsG)
  have hmin : min 0 (c * Gτ) = 0 := min_eq_left (by positivity)
  rw [hmin] at hL
  apply le_of_tendsto_of_tendsto hL hsA
  have hev : ∀ᶠ t in 𝓝[>] τ, min 0 (c * (G t - G τ)) ≤ A t - A τ :=
    nhdsWithin_le_nhds hlow
  filter_upwards [hev, self_mem_nhdsWithin] with t ht htpos
  have hpos : 0 < t - τ := sub_pos.mpr htpos
  rw [slope_def_field, slope_def_field]
  rw [le_div_iff₀ hpos]
  rcases le_or_gt 0 (c * ((G t - G τ) / (t - τ))) with h | h
  · rw [min_eq_left h, zero_mul]
    have : 0 ≤ c * (G t - G τ) := by
      have := mul_nonneg h hpos.le
      rwa [mul_assoc, div_mul_cancel₀ _ hpos.ne'] at this
    rw [min_eq_left this] at ht
    exact ht
  · rw [min_eq_right h.le]
    have e : c * ((G t - G τ) / (t - τ)) * (t - τ) = c * (G t - G τ) := by
      field_simp
    have hneg : c * (G t - G τ) < 0 := by rw [← e]; exact mul_neg_of_neg_of_pos h hpos
    rw [e]
    rw [min_eq_right hneg.le] at ht
    exact ht

/-- continuity from the squeeze bound -/
theorem tendsto_of_bound {A G : ℝ → ℝ} {τ c : ℝ} (hG : ContinuousAt G τ)
    (hb : ∀ᶠ t in 𝓝 τ, |A t - A τ| ≤ |c * (G t - G τ)|) : Tendsto A (𝓝 τ) (𝓝 (A τ)) := by
  have h0 : Tendsto (fun t => |c * (G t - G τ)|) (𝓝 τ) (𝓝 0) := by
    have : Tendsto (fun t => c * (G t - G τ)) (𝓝 τ) (𝓝 (c * (G τ - G τ))) :=
      tendsto_const_nhds.mul (hG.tendsto.sub tendsto_const_nhds)
    simpa using this.abs
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _)) ?_ h0
  filter_upwards [hb] with t ht
  simpa [Real.norm_eq_abs] using ht

/-- derivative from the exact difference identity -/
theorem hasDerivAt_of_identity {A G K : ℝ → ℝ} {τ c Gτ K0 : ℝ}
    (hG : HasDerivAt G Gτ τ) (hK : Tendsto K (𝓝 τ) (𝓝 K0)) (hK0 : K0 ≠ 0)
    (hid : ∀ᶠ t in 𝓝 τ, (A t - A τ) * K t = c * (G t - G τ)) :
    HasDerivAt A (c * Gτ / K0) τ := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hsG : Tendsto (slope G τ) (𝓝[≠] τ) (𝓝 Gτ) := hasDerivAt_iff_tendsto_slope.mp hG
  have hK' : Tendsto K (𝓝[≠] τ) (𝓝 K0) := hK.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun t => c * slope G τ t / K t) (𝓝[≠] τ) (𝓝 (c * Gτ / K0)) :=
    (tendsto_const_nhds.mul hsG).div hK' hK0
  apply hlim.congr'
  have hKne : ∀ᶠ t in 𝓝 τ, K t ≠ 0 := hK.eventually_ne hK0
  filter_upwards [nhdsWithin_le_nhds hid, nhdsWithin_le_nhds hKne, self_mem_nhdsWithin]
    with t ht hKt htne
  have hne : t - τ ≠ 0 := sub_ne_zero.mpr htne
  rw [slope_def_field, slope_def_field]
  field_simp
  linear_combination (-1:ℝ) * ht

end AWPg

namespace AWPf

open AuditWhistle.Intensity Filter Topology

theorem enforcer_eq (M : Model) {q e : ℝ} (hq : 0 ≤ q) (h : IsEnforcerBR M q e) :
    e = min 1 (M.R / M.γ * q) := by
  obtain ⟨⟨he0, he1⟩, hmax⟩ := h
  have hγ := M.hγ
  have hR0 := M.hR
  set r := M.R / M.γ with hr
  have hR : M.R = r * M.γ := by rw [hr]; field_simp
  have hr0 : 0 ≤ r := div_nonneg hR0.le hγ.le
  have hmem : min 1 (r*q) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨le_min zero_le_one (mul_nonneg hr0 hq), min_le_left _ _⟩
  have hle := hmax _ hmem
  unfold enforcerObj at hle
  rw [hR] at hle
  have key0 : M.γ * ((e - r*q)^2 - (min 1 (r*q) - r*q)^2) ≤ 0 := by nlinarith
  have key : (e - r*q)^2 ≤ (min 1 (r*q) - r*q)^2 := by
    by_contra hc
    push_neg at hc
    have : 0 < M.γ * ((e - r*q)^2 - (min 1 (r*q) - r*q)^2) := mul_pos hγ (by linarith)
    linarith
  rcases le_or_gt (r*q) 1 with hc | hc
  · rw [min_eq_right hc] at key ⊢
    have h0 : (e - r*q)^2 = 0 := le_antisymm (by simpa using key) (sq_nonneg _)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
    linarith
  · rw [min_eq_left hc.le] at key ⊢
    apply le_antisymm he1
    nlinarith

theorem auditor_eq (M : Model) {P a : ℝ} (h : IsAuditorBR M P a)
    (h0 : 0 < (1-M.p)*P*(M.D/M.k)) (h1 : (1-M.p)*P*(M.D/M.k) < 1) :
    a = (1-M.p)*P*(M.D/M.k) := by
  obtain ⟨⟨ha0, ha1⟩, hmin⟩ := h
  have hk := M.hk
  set d := M.D / M.k with hd
  have hD : M.D = d * M.k := by rw [hd]; field_simp
  have hle := hmin ((a + (1-M.p)*P*d)/2) ⟨by linarith, by linarith⟩
  unfold auditorLoss at hle
  rw [hD] at hle
  have key : M.k * (3/4 * (a - (1-M.p)*P*d)^2) ≤ 0 := by nlinarith
  have hsq : (a - (1-M.p)*P*d)^2 ≤ 0 := by
    by_contra hc
    push_neg at hc
    have : 0 < M.k * (3/4 * (a - (1-M.p)*P*d)^2) := by positivity
    linarith
  have h0' : (a - (1-M.p)*P*d)^2 = 0 := le_antisymm hsq (sq_nonneg _)
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0'
  linarith

theorem eq_extract (M : Model) {τ a e1 e0 : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (h : IsEquilibrium M τ a e1 e0) :
    0 < a ∧ a < 1 ∧ a = (1-M.p)*(M.D/M.k) * Pf M.p M.β (M.R/M.γ) τ a := by
  obtain ⟨hA, hE1, hE0⟩ := h
  obtain ⟨ha0, ha1⟩ := hA.1
  have hp0 := M.hp0
  have hp1 := M.hp1
  have hβ0 := M.hβ0
  have hβ1 := M.hβ1
  have hr0 : 0 < M.R/M.γ := div_pos M.hR M.hγ
  have hd0 : 0 < M.D/M.k := div_pos M.hD M.hk
  have h1 := den1_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 ha1
  have hpw1 : postW1 M τ a = q1f M.p M.β a := by
    unfold postW1 jointBW1 jointGW1 q1f
    have h2 : 0 < (1 - M.p) * (1 - a) * (M.β * τ) + M.p * ((1 - M.β) * τ) := by
      have e : (1 - M.p) * (1 - a) * (M.β * τ) + M.p * ((1 - M.β) * τ) =
          ((1-M.p)*(1-a)*M.β + M.p*(1-M.β)) * τ := by ring
      rw [e]; exact mul_pos h1 hτ0
    rw [div_eq_div_iff h2.ne' h1.ne']
    ring
  have hpw0 : postW0 M τ a = q0f M.p M.β τ a := rfl
  have he1 := enforcer_eq M (by rw [hpw1]; exact q1f_nonneg hp0 hp1 hβ0 hβ1 hτ0 hτ1 ha1) hE1
  have he0 := enforcer_eq M (by rw [hpw0]; exact (q0f_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 ha1).le) hE0
  rw [hpw1] at he1
  rw [hpw0] at he0
  have hlt := r_q0f_lt_one hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0 M.hRγ ha0.le ha1
  rw [min_eq_right hlt.le] at he0
  have hP : detectProb M τ e1 e0 = Pf M.p M.β (M.R/M.γ) τ a := by
    unfold detectProb Pf
    rw [he1, he0]
  rw [hP] at hA
  have hPpos := Pf_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0 ha1
  have hs := s_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1
  have hPle : Pf M.p M.β (M.R/M.γ) τ a ≤ 1 := by
    unfold Pf
    have hm : min 1 (M.R/M.γ * q1f M.p M.β a) ≤ 1 := min_le_left _ _
    have hb : 0 < M.β * τ := by nlinarith
    have t1 : M.β * τ * min 1 (M.R/M.γ * q1f M.p M.β a) ≤ M.β * τ :=
      by nlinarith
    have t2 : (1 - M.β*τ) * (M.R/M.γ * q0f M.p M.β τ a) ≤ 1 - M.β*τ := by nlinarith
    linarith
  have hdk : (1-M.p)*(M.D/M.k) < 1 := by
    have := M.hDk
    rw [lt_div_iff₀ (by linarith)] at this
    linarith
  have h1p : 0 < 1 - M.p := by linarith
  have hc0 : 0 < (1-M.p)*Pf M.p M.β (M.R/M.γ) τ a*(M.D/M.k) := by positivity
  have hc1 : (1-M.p)*Pf M.p M.β (M.R/M.γ) τ a*(M.D/M.k) < 1 := by
    have : (1-M.p)*Pf M.p M.β (M.R/M.γ) τ a*(M.D/M.k) ≤ (1-M.p)*(M.D/M.k) := by
      have := mul_le_mul_of_nonneg_left hPle (mul_pos h1p hd0).le
      nlinarith
    linarith
  have := auditor_eq M hA hc0 hc1
  refine ⟨ha0, ha1, ?_⟩
  linarith

/-- path facts -/
theorem path_fix (M : Model) {A : ℝ → ℝ} (hA : IsEquilibriumPath M A) :
    ∀ t ∈ Set.Ioo (0:ℝ) 1,
    0 < A t ∧ A t < 1 ∧ A t = (1-M.p)*(M.D/M.k) * Pf M.p M.β (M.R/M.γ) t (A t) := by
  intro t ht
  obtain ⟨e1, e0, h⟩ := hA t ht
  exact eq_extract M ht.1 ht.2 h

theorem q0f_diff {p β τ y a : ℝ} (hDa : (1-p)*(1-a)*(1-β*τ) + p*(1-(1-β)*τ) ≠ 0)
    (hDy : (1-p)*(1-y)*(1-β*τ) + p*(1-(1-β)*τ) ≠ 0) :
    q0f p β τ y - q0f p β τ a = -((1-p)*p*(1-β*τ)*(1-(1-β)*τ)) * (y - a) /
      (((1-p)*(1-a)*(1-β*τ) + p*(1-(1-β)*τ)) * ((1-p)*(1-y)*(1-β*τ) + p*(1-(1-β)*τ))) := by
  unfold q0f
  rw [div_sub_div _ _ hDy hDa, div_eq_div_iff (mul_ne_zero hDy hDa) (mul_ne_zero hDa hDy)]
  ring

section gen
variable {p β r d : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 1/2 < β) (hβ1 : β < 1)
  (hr0 : 0 < r) (hd0 : 0 < d) {A : ℝ → ℝ}
  (hfix : ∀ t ∈ Set.Ioo (0:ℝ) 1, 0 < A t ∧ A t < 1 ∧ A t = (1-p)*d * Pf p β r t (A t))
include hp0 hp1 hβ0 hβ1 hr0 hd0 hfix

theorem path_bound {τ t : ℝ} (hτ : τ ∈ Set.Ioo (0:ℝ) 1) (ht : t ∈ Set.Ioo (0:ℝ) 1) :
    |A t - A τ| ≤ |(1-p)*d * (Pf p β r t (A τ) - Pf p β r τ (A τ))|
    ∧ min 0 ((1-p)*d * (Pf p β r t (A τ) - Pf p β r τ (A τ))) ≤ A t - A τ := by
  obtain ⟨a0, a1, af⟩ := hfix τ hτ
  obtain ⟨b0, b1, bf⟩ := hfix t ht
  have hc : 0 ≤ (1-p)*d := mul_nonneg (by linarith) hd0.le
  apply AWPg.bound_basic (Y := (1-p)*d * (Pf p β r t (A t) - Pf p β r t (A τ)))
  · linear_combination bf - af
  · rcases le_total (A t) (A τ) with h | h
    · have := Pf_anti hp0 hp1 hβ0 hβ1 ht.1 ht.2 hr0 h a1
      have : 0 ≤ (1-p)*d * (Pf p β r t (A t) - Pf p β r t (A τ)) :=
        mul_nonneg hc (by linarith)
      nlinarith
    · have := Pf_anti hp0 hp1 hβ0 hβ1 ht.1 ht.2 hr0 h b1
      have : (1-p)*d * (Pf p β r t (A t) - Pf p β r t (A τ)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hc (by linarith)
      nlinarith

/-- the derivative characterisation -/
theorem main_deriv {τ : ℝ} (hτ : τ ∈ Set.Ioo (0:ℝ) 1) :
    (∃ v : ℝ, HasDerivAt A v τ ∧ v < 0) ↔ H p β r τ ((1-p)*(1-A τ)) < 0 := by
  obtain ⟨hτ0, hτ1⟩ := hτ
  obtain ⟨a0, a1, af⟩ := hfix τ ⟨hτ0, hτ1⟩
  have hc : 0 < (1-p)*d := mul_pos (by linarith) hd0
  have hDa := den0_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 a1
  have hG : HasDerivAt (fun t => Pf p β r t (A τ)) (Ptau p β r τ (A τ)) τ :=
    hasDerivAt_Pf hDa.ne'
  have hnhds : Set.Ioo (0:ℝ) 1 ∈ 𝓝 τ := Ioo_mem_nhds hτ0 hτ1
  have hbnd : ∀ᶠ t in 𝓝 τ, |A t - A τ| ≤ |(1-p)*d * (Pf p β r t (A τ) - Pf p β r τ (A τ))| ∧
      min 0 ((1-p)*d * (Pf p β r t (A τ) - Pf p β r τ (A τ))) ≤ A t - A τ := by
    filter_upwards [hnhds] with t ht
    exact path_bound hp0 hp1 hβ0 hβ1 hr0 hd0 hfix ⟨hτ0, hτ1⟩ ht
  rw [← Ptau_neg_iff hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0 a1]
  constructor
  · rintro ⟨v, hv, hvneg⟩
    by_contra hc2
    push_neg at hc2
    have := AWPg.deriv_nonneg_of_lower (G := fun t => Pf p β r t (A τ)) hc hv hG hc2
      (hbnd.mono fun t ht => ht.2)
    linarith
  · intro hneg
    have hq1 := Ptau_neg_imp hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0 a1 hneg
    have hAt : Tendsto A (𝓝 τ) (𝓝 (A τ)) :=
      AWPg.tendsto_of_bound (G := fun t => Pf p β r t (A τ)) (c := (1-p)*d) hG.continuousAt
        (hbnd.mono fun t ht => ht.1)
    have hq1c : ContinuousAt (fun x => r * q1f p β x) (A τ) := by
      have h1 := den1_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 a1
      unfold q1f
      apply ContinuousAt.mul continuousAt_const
      exact ContinuousAt.div (by fun_prop) (by fun_prop) h1.ne'
    have hev1 : ∀ᶠ t in 𝓝 τ, 1 < r * q1f p β (A t) :=
      (hq1c.tendsto.comp hAt).eventually (lt_mem_nhds hq1)
    let g : ℝ × ℝ → ℝ := fun q => 1 + (1-p)*d*r*((1-p)*p*(1-β*q.1)^2*(1-(1-β)*q.1)) /
      (((1-p)*(1-A τ)*(1-β*q.1) + p*(1-(1-β)*q.1)) *
        ((1-p)*(1-q.2)*(1-β*q.1) + p*(1-(1-β)*q.1)))
    have hgc : ContinuousAt g (τ, A τ) := by
      apply ContinuousAt.add continuousAt_const
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      exact (mul_pos hDa hDa).ne'
    have hK : Tendsto (fun t => g (t, A t)) (𝓝 τ) (𝓝 (g (τ, A τ))) :=
      hgc.tendsto.comp (tendsto_id.prodMk_nhds hAt)
    have hs := s_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1
    have hw := w_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1
    have hK0 : 0 < g (τ, A τ) := by
      have hg0 : g (τ, A τ) = 1 + (1-p)*d*r*((1-p)*p*(1-β*τ)^2*(1-(1-β)*τ)) /
          (((1-p)*(1-A τ)*(1-β*τ) + p*(1-(1-β)*τ)) *
            ((1-p)*(1-A τ)*(1-β*τ) + p*(1-(1-β)*τ))) := rfl
      have hnum : 0 ≤ (1-p)*d*r*((1-p)*p*(1-β*τ)^2*(1-(1-β)*τ)) := by
        have : 0 < 1 - p := by linarith
        positivity
      have hfr := div_nonneg hnum (mul_pos hDa hDa).le
      rw [hg0]
      linarith
    have hid : ∀ᶠ t in 𝓝 τ, (A t - A τ) * g (t, A t) =
        (1-p)*d * (Pf p β r t (A τ) - Pf p β r τ (A τ)) := by
      filter_upwards [hnhds, hev1] with t ht h1t
      obtain ⟨b0, b1, bf⟩ := hfix t ht
      have hDa' := den0_pos hp0 hp1 hβ0 hβ1 ht.1 ht.2 a1
      have hDy' := den0_pos hp0 hp1 hβ0 hβ1 ht.1 ht.2 b1
      have hPd : Pf p β r t (A t) - Pf p β r t (A τ) =
          (1-β*t)*r*(q0f p β t (A t) - q0f p β t (A τ)) := by
        unfold Pf
        rw [min_eq_left h1t.le, min_eq_left hq1.le]
        ring
      rw [q0f_diff hDa'.ne' hDy'.ne'] at hPd
      have hgt : g (t, A t) = 1 + (1-p)*d*r*((1-p)*p*(1-β*t)^2*(1-(1-β)*t)) /
          (((1-p)*(1-A τ)*(1-β*t) + p*(1-(1-β)*t)) *
            ((1-p)*(1-A t)*(1-β*t) + p*(1-(1-β)*t))) := rfl
      rw [hgt]
      have e2 : A t - A τ = (1-p)*d*(Pf p β r t (A t) - Pf p β r t (A τ)) +
          (1-p)*d*(Pf p β r t (A τ) - Pf p β r τ (A τ)) := by
        linear_combination bf - af
      rw [hPd] at e2
      linear_combination e2
    have hder := AWPg.hasDerivAt_of_identity hG hK hK0.ne' hid
    exact ⟨_, hder, div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hc hneg) hK0⟩

end gen

end AWPf

namespace AWPf

open AuditWhistle.Intensity Filter Topology

def Tset (p β r τ : ℝ) : Set ℝ := {x | 0 < x ∧ x < 1 ∧ H p β r τ ((1-p)*(1-x)) < 0}

def Phi (p β r τ x : ℝ) : ℝ := x / ((1-p) * Pf p β r τ x)

def dS (p β r τ : ℝ) : ℝ := sSup (Phi p β r τ '' Tset p β r τ)

section dstar
variable {p β r τ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 1/2 < β) (hβ1 : β < 1)
  (hτ0 : 0 < τ) (hτ1 : τ < 1) (hr0 : 0 < r)
include hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0

theorem Phi_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    Phi p β r τ x < Phi p β r τ y := by
  have hPx := Pf_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0 (x := x) (by linarith)
  have hPy := Pf_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0 hy
  have hanti := Pf_anti hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0 hxy.le hy
  have h1p : 0 < 1 - p := by linarith
  unfold Phi
  rw [div_lt_div_iff₀ (mul_pos h1p hPx) (mul_pos h1p hPy)]
  have h1 : x * Pf p β r τ y < y * Pf p β r τ x := by
    nlinarith [mul_le_mul_of_nonneg_left hanti hx.le, mul_lt_mul_of_pos_right hxy hPx]
  nlinarith [mul_lt_mul_of_pos_left h1 h1p]

theorem T_ext {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (hH : H p β r τ ((1-p)*(1-x)) < 0) :
    ∃ y, x < y ∧ y ∈ Tset p β r τ := by
  have hc : Continuous (fun y : ℝ => H p β r τ ((1-p)*(1-y))) := by unfold H; fun_prop
  have e1 : ∀ᶠ y in 𝓝 x, H p β r τ ((1-p)*(1-y)) < 0 :=
    (hc.tendsto x).eventually (gt_mem_nhds hH)
  have e2 : ∀ᶠ y in 𝓝 x, y < 1 := gt_mem_nhds hx1
  have e4 : ∀ᶠ y in 𝓝[>] x, H p β r τ ((1-p)*(1-y)) < 0 ∧ y < 1 :=
    nhdsWithin_le_nhds (e1.and e2)
  have e3 : ∀ᶠ y in 𝓝[>] x, (H p β r τ ((1-p)*(1-y)) < 0 ∧ y < 1) ∧ x < y :=
    e4.and self_mem_nhdsWithin
  obtain ⟨y, ⟨h1, h2⟩, h3⟩ := e3.exists
  exact ⟨y, h3, by linarith, h2, h1⟩

theorem T_down {x y : ℝ} (hx : x ∈ Tset p β r τ) (hy0 : 0 < y) (hyx : y ≤ x) :
    y ∈ Tset p β r τ := by
  obtain ⟨h0, h1, hH⟩ := hx
  refine ⟨hy0, by linarith, ?_⟩
  have hU : 0 < (1-p)*(1-x) := mul_pos (by linarith) (by linarith)
  have hUU : (1-p)*(1-x) ≤ (1-p)*(1-y) := by nlinarith
  exact H_mono hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0 hU hUU hH

theorem Phi_bdd : BddAbove (Phi p β r τ '' Tset p β r τ) := by
  refine ⟨1 / ((1-p)*(β*τ)), ?_⟩
  rintro z ⟨x, ⟨hx0, hx1, hH⟩, rfl⟩
  have hneg := (Ptau_neg_iff hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0 hx1).mpr hH
  have hq := Ptau_neg_imp hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0 hx1 hneg
  have hq0 := q0f_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 (x := x) hx1
  have hs := s_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1
  have hPge : β*τ ≤ Pf p β r τ x := by
    unfold Pf
    rw [min_eq_left hq.le]
    have : 0 ≤ (1-β*τ)*(r*q0f p β τ x) := by positivity
    linarith
  have hbt : 0 < β*τ := by nlinarith
  have h1p : 0 < 1 - p := by linarith
  unfold Phi
  rw [div_le_div_iff₀ (mul_pos h1p (by linarith)) (mul_pos h1p hbt)]
  nlinarith [mul_le_mul_of_nonneg_left hPge h1p.le, mul_pos h1p hbt]

theorem d_iff {d a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hfix : a = (1-p)*d*Pf p β r τ a) :
    H p β r τ ((1-p)*(1-a)) < 0 ↔ d < dS p β r τ := by
  have hP := Pf_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0 ha1
  have h1p : 0 < 1 - p := by linarith
  have hPhi : Phi p β r τ a = d := by
    unfold Phi
    rw [div_eq_iff (mul_pos h1p hP).ne']
    linarith [hfix]
  constructor
  · intro hH
    obtain ⟨y, hay, hyT⟩ := T_ext hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0 ha0.le ha1 hH
    have := Phi_lt hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0 ha0 hay hyT.2.1
    rw [hPhi] at this
    exact lt_of_lt_of_le this (le_csSup (Phi_bdd hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0) ⟨y, hyT, rfl⟩)
  · intro hlt
    by_cases hne : (Phi p β r τ '' Tset p β r τ).Nonempty
    · obtain ⟨z, ⟨y, hyT, rfl⟩, hz⟩ := exists_lt_of_lt_csSup hne hlt
      have hay : a < y := by
        by_contra hc
        push_neg at hc
        rcases hc.lt_or_eq with h | h
        · have := Phi_lt hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0 hyT.1 h ha1
          linarith
        · rw [h] at hz
          linarith
      exact (T_down hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0 hyT ha0 hay.le).2.2
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      unfold dS at hlt
      rw [hne, Real.sSup_empty] at hlt
      have hd : 0 < d := by
        by_contra hc
        push_neg at hc
        have : (1-p)*d*Pf p β r τ a ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos h1p.le hc) hP.le
        linarith
      linarith

theorem H_to_rstar {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hH : H p β r τ ((1-p)*(1-a)) < 0) :
    rStar p β τ < r := by
  rw [← H_rstar hp0 hp1 hβ0 hβ1 hτ0 hτ1]
  exact H_mono hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0 (mul_pos (by linarith) (by linarith))
    (by nlinarith) hH

theorem dS_pos (hrs : rStar p β τ < r) : 0 < dS p β r τ := by
  have hH := (H_rstar hp0 hp1 hβ0 hβ1 hτ0 hτ1 (r := r)).mpr hrs
  have hH' : H p β r τ ((1-p)*(1-0)) < 0 := by
    rw [sub_zero, mul_one]
    exact hH
  obtain ⟨y, hy, hyT⟩ := T_ext hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0 le_rfl zero_lt_one hH'
  have hP := Pf_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0 hyT.2.1
  have h1p : 0 < 1 - p := by linarith
  have hpos : 0 < Phi p β r τ y := by
    unfold Phi
    exact div_pos hyT.1 (mul_pos h1p hP)
  exact lt_of_lt_of_le hpos (le_csSup (Phi_bdd hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0) ⟨y, hyT, rfl⟩)

end dstar

end AWPf

end

open AuditWhistle.Intensity in
theorem solution (p β r τ : ℝ) (hτ : τ ∈ Set.Ioo (0:ℝ) 1) :
    ∃ dStar : ℝ, (rStar p β τ < r → 0 < dStar) ∧
      ∀ M : Model, M.p = p → M.β = β → M.R / M.γ = r →
        ∀ A : ℝ → ℝ, IsEquilibriumPath M A →
          ((∃ v : ℝ, HasDerivAt A v τ ∧ v < 0) ↔ (rStar p β τ < r ∧ M.D / M.k < dStar)) := by
  obtain ⟨hτ0, hτ1⟩ := hτ
  by_cases V : 0 < p ∧ p < 1 ∧ 1/2 < β ∧ β < 1 ∧ 0 < r
  · obtain ⟨hp0, hp1, hβ0, hβ1, hr0⟩ := V
    refine ⟨AWPf.dS p β r τ, AWPf.dS_pos hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0, ?_⟩
    intro M hp hβ hr A hA
    have hd0 : 0 < M.D / M.k := div_pos M.hD M.hk
    have hfix : ∀ t ∈ Set.Ioo (0:ℝ) 1,
        0 < A t ∧ A t < 1 ∧ A t = (1-p)*(M.D/M.k) * AWPf.Pf p β r t (A t) := by
      intro t ht
      have := AWPf.path_fix M hA t ht
      rw [hp, hβ, hr] at this
      exact this
    rw [AWPf.main_deriv hp0 hp1 hβ0 hβ1 hr0 hd0 hfix ⟨hτ0, hτ1⟩]
    obtain ⟨a0, a1, af⟩ := hfix τ ⟨hτ0, hτ1⟩
    have hiff := AWPf.d_iff hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0 a0 a1 af
    constructor
    · intro hH
      exact ⟨AWPf.H_to_rstar hp0 hp1 hβ0 hβ1 hτ0 hτ1 hr0 a0 a1 hH, hiff.mp hH⟩
    · intro h
      exact hiff.mpr h.2
  · refine ⟨1, fun _ => one_pos, ?_⟩
    intro M hp hβ hr
    exfalso
    apply V
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← hp]; exact M.hp0
    · rw [← hp]; exact M.hp1
    · rw [← hβ]; exact M.hβ0
    · rw [← hβ]; exact M.hβ1
    · rw [← hr]; exact div_pos M.hR M.hγ
