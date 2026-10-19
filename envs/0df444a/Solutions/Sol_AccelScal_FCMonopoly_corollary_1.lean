-- Prove2me | solution 1 for AccelScal.FCMonopoly.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-17T17:19:33.672245+00:00
-- url     : https://prove2.me/submissions/c7b36db5-cb79-498e-91dd-539db0f0be0b

import Definitions.Def_AccelScal_FCMonopoly_Setting

section

set_option backward.isDefEq.respectTransparency false

open Set AccelScal.FCMonopoly

namespace RDProof

variable {T : Tech} {r μ σ X R : ℝ}

lemma lam_const (hγ : T.γ = 0) (x : ℝ) : T.lam x = T.η := by
  simp [Tech.lam, hγ]

lemma uc_formula (hγ : T.γ = 0) (x : ℝ) :
    ucValue T r x = (T.A * T.η * x ^ T.β - x) / (T.η + r) := by
  simp [ucValue, lam_const hγ, Tech.u, mul_right_comm]

lemma alpha_const (hγ : T.γ = 0) (x : ℝ) :
    alpha T r μ σ x = alpha T r μ σ 1 := by simp [alpha, lam_const hγ]

lemma alpha_neg (hT : T.Standing) (hr : 0 < r) (hσ : 0 < σ) (hγ : T.γ = 0) :
    alpha T r μ σ 1 < 0 := by
  have hη := hT.2.1
  have hp : 0 < 2 * (T.η + r) / σ ^ 2 := by positivity
  have hq : 0 ≤ (1 / 2 - μ / σ ^ 2) ^ 2 + 2 * (T.η + r) / σ ^ 2 := by positivity
  have hs := Real.sq_sqrt hq
  have hn := Real.sqrt_nonneg ((1 / 2 - μ / σ ^ 2) ^ 2 + 2 * (T.η + r) / σ ^ 2)
  simp only [alpha, lam_const hγ]
  nlinarith

lemma bar_gt (hT : T.Standing) (hγ : T.γ = 0) : 1 < T.Rbar := by
  apply Real.one_lt_rpow hT.2.2.2.2.2.2.2
  simp only [hγ, add_zero]
  exact one_div_pos.mpr (sub_pos.mpr hT.2.2.2.1)

lemma bar_power (hT : T.Standing) (hγ : T.γ = 0) :
    T.Rbar ^ (1 - T.β) = T.A * T.η := by
  have hK : 0 < T.A * T.η := mul_pos hT.1 hT.2.1
  have hβ : 1 - T.β ≠ 0 := ne_of_gt (sub_pos.mpr hT.2.2.2.1)
  simp only [Tech.Rbar, hγ, add_zero]
  rw [← Real.rpow_mul hK.le]
  simp [hβ]

lemma uc_pos (hT : T.Standing) (hr : 0 < r) (hγ : T.γ = 0)
    (hR : 0 < R) (hlt : R < T.Rbar) : 0 < ucValue T r R := by
  have hpow := Real.rpow_lt_rpow hR.le hlt (sub_pos.mpr hT.2.2.2.1)
  rw [bar_power hT hγ] at hpow
  have hp : 0 < R ^ T.β := Real.rpow_pos_of_pos hR _
  have hid : R ^ (1 - T.β) * R ^ T.β = R := by
    rw [← Real.rpow_add hR]
    simp
  have hn : R < T.A * T.η * R ^ T.β := by nlinarith [mul_lt_mul_of_pos_right hpow hp]
  rw [uc_formula hγ]
  exact div_pos (sub_pos.mpr hn) (add_pos hT.2.1 hr)

lemma uc_bar (hT : T.Standing) (hγ : T.γ = 0) : ucValue T r T.Rbar = 0 := by
  have hb := lt_trans zero_lt_one (bar_gt hT hγ)
  have hid : T.Rbar ^ (1 - T.β) * T.Rbar ^ T.β = T.Rbar := by
    rw [← Real.rpow_add hb]
    simp
  rw [bar_power hT hγ] at hid
  rw [uc_formula hγ, hid, sub_self, zero_div]

lemma uc_derivative (hγ : T.γ = 0) (hR : 0 < R) :
    HasDerivAt (ucValue T r)
      ((T.A * T.η * T.β * R ^ (T.β - 1) - 1) / (T.η + r)) R := by
  have hp := (Real.hasDerivAt_rpow_const (p := T.β) (Or.inl hR.ne')).const_mul (T.A * T.η)
  have hd := (hp.sub (hasDerivAt_id R)).div_const (T.η + r)
  have he : ucValue T r = fun x => (T.A * T.η * x ^ T.β - x) / (T.η + r) :=
    funext (uc_formula hγ)
  rw [he]
  change HasDerivAt (fun x => (T.A * T.η * x ^ T.β - x) / (T.η + r))
    ((T.A * T.η * (T.β * R ^ (T.β - 1)) - 1) / (T.η + r)) R at hd
  simpa only [mul_assoc] using hd

lemma u_derivative (hR : 0 < R) : deriv T.u R = T.A * T.β * R ^ (T.β - 1) := by
  have hp : HasDerivAt T.u (T.A * (T.β * R ^ (T.β - 1))) R :=
    (Real.hasDerivAt_rpow_const (p := T.β) (Or.inl hR.ne')).const_mul T.A
  rw [hp.deriv]
  ring

lemma fc_derivative (hγ : T.γ = 0) (hR : 0 < R) (hX : 0 < X) :
    HasDerivAt (fcValue T r μ σ X)
      (((T.A * T.η * T.β * R ^ (T.β - 1) - 1) / (T.η + r)) *
         (1 - (X / R) ^ alpha T r μ σ 1) +
       ucValue T r R * (alpha T r μ σ 1 * (X / R) ^ alpha T r μ σ 1 / R)) R := by
  have hdiv : HasDerivAt (fun x : ℝ => X / x) (-X / R ^ 2) R := by
    convert! (hasDerivAt_inv hR.ne').const_mul X using 1 <;>
      simp only [div_eq_mul_inv, mul_neg, neg_mul]
  have hd := hdiv.rpow_const (p := alpha T r μ σ 1)
    (Or.inl (div_pos hX hR).ne')
  have heq : -((-X / R ^ 2) * alpha T r μ σ 1 * (X / R) ^ (alpha T r μ σ 1 - 1)) =
      alpha T r μ σ 1 * (X / R) ^ alpha T r μ σ 1 / R := by
    rw [Real.rpow_sub_one (div_pos hX hR).ne']
    field_simp
    <;> ring
  have hf := (uc_derivative (r := r) hγ hR).mul (hd.const_sub 1)
  have he : fcValue T r μ σ X = fun x => ucValue T r x * (1 - (X / x) ^ alpha T r μ σ 1) := by
    funext x
    simp [fcValue, alpha_const hγ]
  rw [he]
  convert! hf using 1
  rw [heq]

lemma uc_continuous (hγ : T.γ = 0) : ContinuousOn (ucValue T r) (Ioi 0) := by
  intro x hx
  exact (uc_derivative hγ hx).continuousAt.continuousWithinAt

lemma fc_continuous (hγ : T.γ = 0) (hX : 0 < X) :
    ContinuousOn (fcValue T r μ σ X) (Ioi 0) := by
  intro x hx
  exact (fc_derivative hγ hx hX).continuousAt.continuousWithinAt

lemma max_interior {f : ℝ → ℝ} {a b x d : ℝ} (hm : IsMaxOn f (Icc a b) x)
    (hx : a < x) (hxb : x < b) (hd : HasDerivAt f d x) : d = 0 := by
  exact (hm.isLocalMax (Icc_mem_nhds hx hxb)).hasDerivAt_eq_zero hd

lemma left_max_deriv_nonpos {f : ℝ → ℝ} {a b d : ℝ} (hm : IsMaxOn f (Icc a b) a)
    (hab : a < b) (hd : HasDerivAt f d a) : d ≤ 0 := by
  have hseg : segment ℝ a b ⊆ Icc a b := (convex_Icc a b).segment_subset ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩
  have hv := hm.localize.hasFDerivWithinAt_nonpos hd.hasFDerivAt.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset hseg)
  change (b - a) * d ≤ 0 at hv
  nlinarith

end RDProof

end

section

set_option backward.isDefEq.respectTransparency false

open Set AccelScal.FCMonopoly

namespace RDProof

lemma uc_interior (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r)
    (hγ : T.γ = 0) (hint : 1 < T.A * T.β * T.η)
    (R : ℝ) (hm : R ∈ RstarUC T r) : 1 < R ∧ R < T.Rbar := by
  change R ∈ Icc 1 T.Rbar ∧ IsMaxOn (ucValue T r) (Icc 1 T.Rbar) R at hm
  have hb := bar_gt hT hγ
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hm.1.1
  constructor
  · by_contra h
    have heq : R = 1 := le_antisymm (not_lt.mp h) hm.1.1
    subst R
    have hn := left_max_deriv_nonpos hm.2 hb (uc_derivative hγ zero_lt_one)
    simp only [Real.one_rpow, mul_one] at hn
    have hp : 0 < (T.A * T.η * T.β - 1) / (T.η + r) :=
      div_pos (by nlinarith [hint]) (add_pos hT.2.1 hr)
    linarith
  · by_contra h
    have heq : R = T.Rbar := le_antisymm hm.1.2 (not_lt.mp h)
    have hv := hm.2 ⟨le_rfl, hb.le⟩
    rw [heq, uc_bar hT hγ] at hv
    change ucValue T r 1 ≤ 0 at hv
    have hp := uc_pos hT hr hγ zero_lt_one hb
    linarith

lemma uc_first (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r)
    (hγ : T.γ = 0) (hβ : 0 < T.β) (hint : 1 < T.A * T.β * T.η) :
    ∀ R ∈ RstarUC T r, deriv T.u R * T.lam R - 1 = 0 := by
  intro R hm
  have hi := uc_interior T hT r hr hγ hint R hm
  have hR := lt_trans zero_lt_one hi.1
  change R ∈ Icc 1 T.Rbar ∧ IsMaxOn (ucValue T r) (Icc 1 T.Rbar) R at hm
  have hd := max_interior hm.2 hi.1 hi.2 (uc_derivative hγ hR)
  have hn := (div_eq_zero_iff).mp hd
  have hd0 : T.η + r ≠ 0 := (add_pos hT.2.1 hr).ne'
  rw [u_derivative hR, lam_const hγ]
  rcases hn with hn | hn
  · nlinarith
  · exact (hd0 hn).elim

lemma fc_first (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) (μ σ X : ℝ)
    (hσ : 0 < σ) (hγ : T.γ = 0) (hβ : 0 < T.β) :
    ∀ R ∈ RstarFC T r μ σ X, 1 < R → R < min T.Rbar X →
      0 < deriv T.u R * T.lam R - 1 := by
  intro R hm hl hu
  have hR := lt_trans zero_lt_one hl
  have hRX := lt_of_lt_of_le hu (min_le_right _ _)
  have hX := lt_trans hR hRX
  have hRb := lt_of_lt_of_le hu (min_le_left _ _)
  change R ∈ Icc 1 (min T.Rbar X) ∧ IsMaxOn (fcValue T r μ σ X) (Icc 1 (min T.Rbar X)) R at hm
  have hd := max_interior hm.2 hl hu (fc_derivative hγ hR hX)
  have ha := alpha_neg (μ := μ) hT hr hσ hγ
  have hv := uc_pos hT hr hγ hR hRb
  have hpow := Real.rpow_pos_of_pos (div_pos hX hR) (alpha T r μ σ 1)
  have hs : 0 < 1 - (X / R) ^ alpha T r μ σ 1 := by
    exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg ((one_lt_div hR).mpr hRX) ha)
  have hn : ucValue T r R * (alpha T r μ σ 1 * (X / R) ^ alpha T r μ σ 1 / R) < 0 :=
    mul_neg_of_pos_of_neg hv (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos ha hpow) hR)
  have hdpos : 0 < (T.A * T.η * T.β * R ^ (T.β - 1) - 1) / (T.η + r) := by
    nlinarith
  have hnum := (div_pos_iff_of_pos_right (add_pos hT.2.1 hr)).mp hdpos
  rw [u_derivative hR, lam_const hγ]
  nlinarith

variable {T : Tech} {r μ σ X R : ℝ}

lemma fc_pos (hT : T.Standing) (hr : 0 < r) (hσ : 0 < σ) (hγ : T.γ = 0)
    (hR : 0 < R) (hRb : R < T.Rbar) (hRX : R < X) : 0 < fcValue T r μ σ X R := by
  rw [fcValue, alpha_const hγ]
  exact mul_pos (uc_pos hT hr hγ hR hRb)
    (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg ((one_lt_div hR).mpr hRX)
      (alpha_neg hT hr hσ hγ)))

lemma fc_upper_zero (hT : T.Standing) (hγ : T.γ = 0) (hX : 0 < X) :
    fcValue T r μ σ X (min T.Rbar X) = 0 := by
  rcases le_total T.Rbar X with h | h
  · simp [min_eq_left h, fcValue, uc_bar hT hγ]
  · simp [min_eq_right h, fcValue, div_self hX.ne']

lemma corollary (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) (μ σ X : ℝ)
    (hσ : 0 < σ) (hX : 1 ≤ X) (hγ : T.γ = 0) (hβ : 0 < T.β)
    (hint : 1 < T.A * T.β * T.η) :
    (RstarUC T r).Nonempty ∧ (RstarFC T r μ σ X).Nonempty ∧
    ∀ x ∈ RstarFC T r μ σ X, ∀ y ∈ RstarUC T r, x < y := by
  have hb := bar_gt hT hγ
  have hXp := lt_of_lt_of_le zero_lt_one hX
  have hne1 : (Icc (1 : ℝ) T.Rbar).Nonempty := ⟨1, le_rfl, hb.le⟩
  have hne2 : (Icc (1 : ℝ) (min T.Rbar X)).Nonempty := ⟨1, le_rfl, le_min hb.le hX⟩
  have hc1 : ContinuousOn (ucValue T r) (Icc 1 T.Rbar) := (uc_continuous hγ).mono
    (fun _ hx => lt_of_lt_of_le zero_lt_one hx.1)
  have hc2 : ContinuousOn (fcValue T r μ σ X) (Icc 1 (min T.Rbar X)) :=
    (fc_continuous hγ hXp).mono (fun _ hx => lt_of_lt_of_le zero_lt_one hx.1)
  obtain ⟨u, hu, hmu⟩ := isCompact_Icc.exists_isMaxOn hne1 hc1
  obtain ⟨v, hv, hmv⟩ := isCompact_Icc.exists_isMaxOn hne2 hc2
  refine ⟨⟨u, hu, hmu⟩, ⟨v, hv, hmv⟩, ?_⟩
  intro x hx y hy
  have hyi := uc_interior T hT r hr hγ hint y hy
  by_cases hx1 : x ≤ 1
  · exact lt_of_le_of_lt hx1 hyi.1
  have hxlo : 1 < x := lt_of_not_ge hx1
  have hxmem : x ∈ Icc 1 (min T.Rbar X) ∧
      IsMaxOn (fcValue T r μ σ X) (Icc 1 (min T.Rbar X)) x := hx
  have hX1 : 1 < X := lt_of_lt_of_le hxlo (hxmem.1.2.trans (min_le_right _ _))
  have hxhi : x < min T.Rbar X := by
    by_contra h
    have heq : x = min T.Rbar X := le_antisymm hxmem.1.2 (not_lt.mp h)
    have hm' := hxmem.2 (show 1 ∈ Icc 1 (min T.Rbar X) from ⟨le_rfl, le_min hb.le hX⟩)
    rw [heq, fc_upper_zero hT hγ hXp] at hm'
    change fcValue T r μ σ X 1 ≤ 0 at hm'
    have hp := fc_pos (μ := μ) hT hr hσ hγ zero_lt_one hb hX1
    linarith
  have hfx := fc_first T hT r hr μ σ X hσ hγ hβ x hx hxlo hxhi
  have hfy := uc_first T hT r hr hγ hβ hint y hy
  have hxp := lt_trans zero_lt_one hxlo
  have hyp := lt_trans zero_lt_one hyi.1
  rw [u_derivative hxp, lam_const hγ] at hfx
  rw [u_derivative hyp, lam_const hγ] at hfy
  by_contra h
  have hpow := Real.rpow_le_rpow_of_nonpos hyp (not_lt.mp h) (sub_nonpos.mpr hT.2.2.2.1.le)
  have hcoef : 0 ≤ T.A * T.β * T.η := (mul_pos (mul_pos hT.1 hβ) hT.2.1).le
  have hm := mul_le_mul_of_nonneg_left hpow hcoef
  nlinarith

end RDProof

end

open AccelScal.FCMonopoly

theorem solution (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) (μ σ X : ℝ) (hσ : 0 < σ)
    (hX : 1 ≤ X) (hγ : T.γ = 0) (hβ : 0 < T.β) (hint : 1 < T.A * T.β * T.η) :
    (RstarUC T r).Nonempty ∧ (RstarFC T r μ σ X).Nonempty ∧
    ∀ x ∈ RstarFC T r μ σ X, ∀ y ∈ RstarUC T r, x < y := by
  exact RDProof.corollary T hT r hr μ σ X hσ hX hγ hβ hint
