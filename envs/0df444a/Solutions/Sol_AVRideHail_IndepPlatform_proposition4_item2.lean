-- Prove2me | solution 1 for AVRideHail.IndepPlatform.proposition4_item2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:23:07.203233+00:00
-- url     : https://prove2.me/submissions/3ceb8d68-b2bb-414f-85ca-cf7495daa93a

import Mathlib
import Definitions.Def_AVRideHail_IndepPlatform_Model

set_option autoImplicit false
open AVRideHail.PureHV AVRideHail.IndepPlatform

lemma aTilde_pos' (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r) : 0 < aTilde P := by
  unfold aTilde
  have h1 : 0 < P.r ^ (1 / (P.r + 1)) * P.a ^ (1 / (P.r + 1)) := by positivity
  have h2 : 0 < P.r ^ (-P.r / (P.r + 1)) * P.a ^ (1 / (P.r + 1)) := by positivity
  linarith

lemma nMin_hasDeriv' (P : MarketParams) (d : ℝ) (hd : 0 < d) :
    HasDerivAt (nMin P)
      (aTilde P * ((1 / (P.r + 1)) * d ^ (1 / (P.r + 1) - 1)) + P.t2) d := by
  have h1 := Real.hasDerivAt_rpow_const (x := d) (p := 1 / (P.r + 1)) (Or.inl hd.ne')
  have h2 := (h1.const_mul (aTilde P)).add ((hasDerivAt_id d).const_mul P.t2)
  exact h2.congr_deriv (by ring)

lemma nMin_pos' (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r) (ht2 : 0 < P.t2)
    (d : ℝ) (hd : 0 < d) : 0 < nMin P d := by
  unfold nMin
  have := aTilde_pos' P ha hr0
  have : 0 < d ^ (1 / (P.r + 1)) := Real.rpow_pos_of_pos hd _
  positivity

/-- the derivative of hvRatio, in the form of the proof -/
lemma hvRatio_hasDeriv' (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r) (ht2 : 0 < P.t2)
    (d : ℝ) (hd : 0 < d) :
    ∃ F : ℝ, HasDerivAt (hvRatio P) F d ∧
      (F < 0 ↔ P.alpha * nMin P d *
          ((aTilde P * (1 - P.r) / (P.t2 * (P.r + 1))) + d ^ (P.r / (P.r + 1))) <
        P.w0 * (aTilde P * P.r / (P.t2 * (P.r + 1)))) := by
  have hn := nMin_pos' P ha hr0 ht2 d hd
  have hA := aTilde_pos' P ha hr0
  have hnd := nMin_hasDeriv' P d hd
  have hf : HasDerivAt (fun x => wage P (nMin P x))
      (P.alpha * (aTilde P * ((1 / (P.r + 1)) * d ^ (1 / (P.r + 1) - 1)) + P.t2)) d :=
    (hnd.const_mul P.alpha).const_add P.w0
  have hg0 : HasDerivAt (fun x : ℝ => x * P.t2) P.t2 d := by
    simpa using (hasDerivAt_id d).mul_const P.t2
  have hg : HasDerivAt (fun x => uBar P x)
      ((P.t2 * nMin P d - d * P.t2 *
        (aTilde P * ((1 / (P.r + 1)) * d ^ (1 / (P.r + 1) - 1)) + P.t2)) / nMin P d ^ 2) d :=
    hg0.div hnd hn.ne'
  have hgpos : 0 < uBar P d := by unfold uBar; positivity
  refine ⟨_, hf.div hg hgpos.ne', ?_⟩
  rw [div_lt_iff₀ (pow_pos hgpos 2), zero_mul]
  have hu : 0 < d ^ (1 / (P.r + 1)) := Real.rpow_pos_of_pos hd _
  have hq : 0 < d ^ (P.r / (P.r + 1)) := Real.rpow_pos_of_pos hd _
  have hdu : d ^ (1 / (P.r + 1)) * d ^ (P.r / (P.r + 1)) = d := by
    rw [← Real.rpow_add hd]
    have : 1 / (P.r + 1) + P.r / (P.r + 1) = 1 := by field_simp; ring
    rw [this, Real.rpow_one]
  rw [Real.rpow_sub_one hd.ne']
  have hnexp : nMin P d = aTilde P * d ^ (1 / (P.r + 1)) + P.t2 * d := rfl
  have hgexp : uBar P d = d * P.t2 / nMin P d := rfl
  have hwexp : wage P (nMin P d) = P.w0 + P.alpha * nMin P d := rfl
  rw [hgexp, hwexp]
  rw [hnexp] at hn ⊢
  generalize d ^ (1 / (P.r + 1)) = u at *
  generalize d ^ (P.r / (P.r + 1)) = q at *
  subst hdu
  have hr1 : 0 < P.r + 1 := by linarith
  have hnum : (P.alpha * (aTilde P * (1 / (P.r + 1) * (u / (u * q))) + P.t2)) *
      (u * q * P.t2 / (aTilde P * u + P.t2 * (u * q))) -
      (P.w0 + P.alpha * (aTilde P * u + P.t2 * (u * q))) *
      ((P.t2 * (aTilde P * u + P.t2 * (u * q)) - u * q * P.t2 *
        (aTilde P * (1 / (P.r + 1) * (u / (u * q))) + P.t2)) /
        (aTilde P * u + P.t2 * (u * q)) ^ 2)
      = P.t2 * u / (aTilde P * u + P.t2 * (u * q)) ^ 2 *
        (P.alpha * (aTilde P * u + P.t2 * (u * q)) *
          (aTilde P * (1 - P.r) / (P.t2 * (P.r + 1)) + q) -
          P.w0 * (aTilde P * P.r / (P.t2 * (P.r + 1)))) * P.t2 := by
    have hu0 := hu.ne'
    have hq0 := hq.ne'
    have hr0' := hr1.ne'
    have ht0 := ht2.ne'
    have hn0 := hn.ne'
    field_simp
    ring
  rw [hnum]
  have hc : 0 < P.t2 * u / (aTilde P * u + P.t2 * (u * q)) ^ 2 * P.t2 := by positivity
  generalize hX : (P.alpha * (aTilde P * u + P.t2 * (u * q)) *
          (aTilde P * (1 - P.r) / (P.t2 * (P.r + 1)) + q) -
          P.w0 * (aTilde P * P.r / (P.t2 * (P.r + 1)))) = X
  generalize P.t2 * u / (aTilde P * u + P.t2 * (u * q)) ^ 2 = c0 at hc ⊢
  have e : c0 * X * P.t2 = (c0 * P.t2) * X := by ring
  rw [e]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have : 0 ≤ X := by rw [← hX]; linarith
    have := mul_nonneg hc.le this
    linarith
  · intro h
    have : X < 0 := by rw [← hX]; linarith
    exact mul_neg_of_pos_of_neg hc this

lemma eq243' (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hw0 : 0 < P.w0)
    (d : ℝ) (hd : 0 < d) :
    deriv (hvRatio P) d < 0 ↔ P.alpha < alphaBound P d := by
  obtain ⟨F, hF, hiff⟩ := hvRatio_hasDeriv' P ha hr0 ht2 d hd
  rw [hF.deriv, hiff]
  have hn := nMin_pos' P ha hr0 ht2 d hd
  have hA := aTilde_pos' P ha hr0
  have hq : 0 < d ^ (P.r / (P.r + 1)) := Real.rpow_pos_of_pos hd _
  have hL : 0 < aTilde P * (1 - P.r) / (P.t2 * (P.r + 1)) :=
    div_pos (mul_pos hA (sub_pos.2 hr1)) (mul_pos ht2 (by linarith))
  unfold alphaBound
  rw [div_mul_div_comm, lt_div_iff₀ (by positivity)]
  have e : P.alpha * nMin P d *
      (aTilde P * (1 - P.r) / (P.t2 * (P.r + 1)) + d ^ (P.r / (P.r + 1))) =
      P.alpha * (nMin P d *
      (aTilde P * (1 - P.r) / (P.t2 * (P.r + 1)) + d ^ (P.r / (P.r + 1)))) := by ring
  rw [e]

lemma alphaBound_anti' (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hw0 : 0 < P.w0) :
    StrictAntiOn (alphaBound P) (Set.Ioi 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ioi] at hx hy
  show alphaBound P y < alphaBound P x
  unfold alphaBound
  have hA := aTilde_pos' P ha hr0
  have hs : 0 < 1 / (P.r + 1) := by positivity
  have hrho : 0 < P.r / (P.r + 1) := by positivity
  have hnx := nMin_pos' P ha hr0 ht2 x hx
  have hny := nMin_pos' P ha hr0 ht2 y hy
  have hsxy : x ^ (1 / (P.r + 1)) < y ^ (1 / (P.r + 1)) := Real.rpow_lt_rpow hx.le hxy hs
  have hqxy : x ^ (P.r / (P.r + 1)) < y ^ (P.r / (P.r + 1)) := Real.rpow_lt_rpow hx.le hxy hrho
  have hnxy : nMin P x < nMin P y := by
    unfold nMin
    nlinarith [mul_lt_mul_of_pos_left hsxy hA, mul_lt_mul_of_pos_left hxy ht2]
  have hqx : 0 < x ^ (P.r / (P.r + 1)) := Real.rpow_pos_of_pos hx _
  have hL : 0 < aTilde P * (1 - P.r) / (P.t2 * (P.r + 1)) :=
    div_pos (mul_pos hA (sub_pos.2 hr1)) (mul_pos ht2 (by linarith))
  have hK : 0 < aTilde P * P.r / (P.t2 * (P.r + 1)) :=
    div_pos (mul_pos hA hr0) (mul_pos ht2 (by linarith))
  have hqy : 0 < y ^ (P.r / (P.r + 1)) := Real.rpow_pos_of_pos hy _
  apply mul_lt_mul''
  · exact div_lt_div_of_pos_left hw0 hnx hnxy
  · exact div_lt_div_of_pos_left hK (by positivity) (by linarith)
  · positivity
  · positivity

theorem solution (P : AVRideHail.PureHV.MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hV : 0 < P.V) (hw0 : 0 < P.w0) (halpha : 0 < P.alpha)
    (dstar : ℝ) (hd : 0 < dstar) :
    (∀ d ∈ Set.Ioc 0 dstar, deriv (hvRatio P) d < 0) ↔ P.alpha < alphaBound P dstar := by
  have hanti := alphaBound_anti' P ha hr0 hr1 ht2 hw0
  constructor
  · intro h
    have := h dstar ⟨hd, le_rfl⟩
    rwa [eq243' P ha hr0 hr1 ht2 hw0 dstar hd] at this
  · intro h d hdm
    rw [eq243' P ha hr0 hr1 ht2 hw0 d hdm.1]
    exact lt_of_lt_of_le h (hanti.antitoneOn hdm.1 hd hdm.2)
