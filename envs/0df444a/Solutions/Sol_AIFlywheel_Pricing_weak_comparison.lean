-- Prove2me | solution 1 for AIFlywheel.Pricing.weak_comparison
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T04:09:04.945364+00:00
-- url     : https://prove2.me/submissions/6ea94a56-7e46-41dd-8aec-fbf2539895be

import Mathlib
import Definitions.Def_AIFlywheel_Pricing_Model

open Set

namespace AIFlywheelT1Aux
open AIFlywheel.Pricing

lemma revenue_eq (ν δ α : ℝ) : revenue ν δ α = α * (δ / ν) * (1 - δ / ν) := by
  simp [revenue, uniformQuantile]

lemma J2b_eq (ν α : ℝ) (hν : 0 < ν) (hα : 0 ≤ α) : J2b ν α = α / 4 := by
  unfold J2b
  apply IsGreatest.csSup_eq
  refine ⟨⟨ν / 2, ⟨by linarith, by linarith⟩, ?_⟩, ?_⟩
  · dsimp only; rw [revenue_eq]; field_simp; ring
  · rintro _ ⟨δ, _, rfl⟩
    dsimp only; rw [revenue_eq]
    have h1 : (δ / ν) * (1 - δ / ν) ≤ 1 / 4 := by nlinarith [sq_nonneg (δ / ν - 1 / 2)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hα]

/-- First-best reduced objective (with `J2b` kept symbolic). -/
noncomputable def Fr (P : Params) (δ : ℝ) : ℝ :=
  revenue P.ν δ P.αl + P.pw (P.d0 + δ) * (J2b P.ν P.αh - J2b P.ν P.αl)

/-- Agency cost term `κ / ρ(d0 + δ)`. -/
noncomputable def gg (P : Params) (δ : ℝ) : ℝ := P.κ * (1 / dataImpact P (P.d0 + δ))

/-- Moral-hazard reduced objective. -/
noncomputable def Mr (P : Params) (δ : ℝ) : ℝ := (1 - P.pw P.d0) * Fr P δ - gg P δ

/-- Part of the moral-hazard objective depending only on `δ1h`. -/
noncomputable def Bh (P : Params) (h : ℝ) : ℝ :=
  P.pw P.d0 * (revenue P.ν h P.αh + J2b P.ν P.αh) + (1 - P.pw P.d0) * J2b P.ν P.αl
    - P.pw P.d0 * (P.κ / (P.pw P.d0 - P.ps P.d0)) + P.pw P.d0 * P.κ

lemma mem_dom (P : Params) (hP : P.Standing) {δ : ℝ} (hδ : δ ∈ Icc 0 P.ν) :
    P.d0 + δ ∈ Icc P.dmin P.dmax := by
  obtain ⟨_, hd0, _, hdmax, _⟩ := hP
  exact ⟨by linarith [hδ.1], by linarith [hδ.2]⟩

lemma d0_mem (P : Params) (hP : P.Standing) : P.d0 ∈ Icc P.dmin P.dmax := by
  have := mem_dom P hP (δ := 0) ⟨le_refl _, hP.2.2.1.le⟩
  simpa using this

lemma gg_eq (P : Params) (hP : P.Standing) {δ : ℝ} (hδ : δ ∈ Icc 0 P.ν) :
    gg P δ = P.κ * P.pw (P.d0 + δ) / (P.pw (P.d0 + δ) - P.ps (P.d0 + δ)) := by
  have hm := (hP.2.2.2.2.2.2.2.1) _ (mem_dom P hP hδ)
  have hpos : 0 < P.pw (P.d0 + δ) := by linarith [hm.1, hm.2.1]
  have hd : 0 < P.pw (P.d0 + δ) - P.ps (P.d0 + δ) := by linarith [hm.2.1]
  unfold gg dataImpact
  field_simp

lemma gg_ge (P : Params) (hP : P.Standing) {δ : ℝ} (hδ : δ ∈ Icc 0 P.ν) :
    P.κ ≤ gg P δ := by
  have hm := (hP.2.2.2.2.2.2.2.1) _ (mem_dom P hP hδ)
  have hd : 0 < P.pw (P.d0 + δ) - P.ps (P.d0 + δ) := by linarith [hm.2.1]
  have hκ := hP.2.2.2.2.1
  rw [gg_eq P hP hδ, le_div_iff₀ hd]
  nlinarith [hm.1]

lemma J2b_diff (P : Params) (hP : P.Standing) :
    J2b P.ν P.αh - J2b P.ν P.αl = (P.αh - P.αl) / 4 := by
  obtain ⟨_, _, hν, _, _, hαl, hαlh, _⟩ := hP
  rw [J2b_eq _ _ hν (by linarith), J2b_eq _ _ hν hαl.le]; ring

/-- Upper bound on the objective of any feasible plan. -/
lemma feasible_le (P : Params) (hP : P.Standing) (s : Plan) (hs : s.Feasible P) :
    objective P s ≤ Bh P s.δ1h + Mr P s.δ1l := by
  obtain ⟨h1h, h1l, h2h, h2l, hδh, hδl, hIC1, hIC2⟩ := hs
  have hm := (hP.2.2.2.2.2.2.2.1) _ (mem_dom P hP hδl)
  have hm0 := (hP.2.2.2.2.2.2.2.1) _ (d0_mem P hP)
  have hκ := hP.2.2.2.2.1
  have hgg := gg_eq P hP hδl
  unfold providerCont at hIC1 hIC2
  unfold objective J2aLow Bh Mr Fr
  set p1 := P.pw (P.d0 + s.δ1l) with hp1
  set q1 := P.ps (P.d0 + s.δ1l) with hq1
  set c0 := P.pw P.d0 with hc0
  set q0 := P.ps P.d0 with hq0
  have hd1 : 0 < p1 - q1 := by linarith [hm.2.1]
  have hd0 : 0 < c0 - q0 := by linarith [hm0.2.1]
  have hK1 : gg P s.δ1l ≤ p1 * (s.x2h - s.x2l) := by
    rw [hgg, div_le_iff₀ hd1]
    nlinarith [hm.1]
  have hK0 : P.κ / (c0 - q0) ≤
      s.x1h - s.x1l - (p1 * s.x2h + (1 - p1) * s.x2l - P.κ) := by
    rw [div_le_iff₀ hd0]
    nlinarith
  have hc0nn : 0 ≤ c0 := by linarith [hm0.1, hm0.2.1]
  have hc01 : c0 < 1 := hm0.2.2
  have e1 := mul_le_mul_of_nonneg_left hK0 hc0nn
  have e2 := mul_nonneg (sub_nonneg.2 hc01.le) h1l
  have e3 := mul_nonneg (sub_nonneg.2 hc01.le) h2l
  have e4 := mul_le_mul_of_nonneg_left hK1 (sub_nonneg.2 hc01.le)
  nlinarith

/-- The payment scheme of Lemma 2 attains the bound. -/
lemma exists_plan (P : Params) (hP : P.Standing) (h δ : ℝ) (hh : h ∈ Icc 0 P.ν)
    (hδ : δ ∈ Icc 0 P.ν) :
    ∃ s : Plan, s.Feasible P ∧ s.δ1h = h ∧ s.δ1l = δ ∧ objective P s = Bh P h + Mr P δ := by
  have hm := (hP.2.2.2.2.2.2.2.1) _ (mem_dom P hP hδ)
  have hm0 := (hP.2.2.2.2.2.2.2.1) _ (d0_mem P hP)
  have hκ := hP.2.2.2.2.1
  set p1 := P.pw (P.d0 + δ) with hp1
  set q1 := P.ps (P.d0 + δ) with hq1
  set c0 := P.pw P.d0 with hc0
  set q0 := P.ps P.d0 with hq0
  have hd1 : 0 < p1 - q1 := by linarith [hm.2.1]
  have hd0 : 0 < c0 - q0 := by linarith [hm0.2.1]
  set A := P.κ / (c0 - q0) with hAdef
  set E := P.κ / (p1 - q1) with hEdef
  have hA : A * (c0 - q0) = P.κ := by rw [hAdef]; field_simp
  have hE : E * (p1 - q1) = P.κ := by rw [hEdef]; field_simp
  have hgg : gg P δ = p1 * E := by
    rw [gg_eq P hP hδ, hEdef]; ring
  have hgge := gg_ge P hP hδ
  have hApos : 0 < A := div_pos hκ hd0
  have hEpos : 0 < E := div_pos hκ hd1
  refine ⟨⟨A + (gg P δ - P.κ), 0, E, 0, h, δ⟩, ?_, rfl, rfl, ?_⟩
  · refine ⟨by simp only; linarith, le_refl _, hEpos.le, le_refl _, hh, hδ, ?_, ?_⟩
    · unfold providerCont
      simp only
      rw [← hp1, ← hc0, ← hq0, hgg]
      nlinarith
    · unfold providerCont
      simp only
      rw [← hp1, ← hq1]
      nlinarith
  · unfold objective J2aLow Bh Mr Fr
    simp only
    rw [← hp1, ← hc0, ← hq0, hgg]
    ring

lemma optimal_max (P : Params) (hP : P.Standing) (s : Plan) (hs : IsOptimal P s) :
    s.δ1l ∈ Icc 0 P.ν ∧ ∀ δ ∈ Icc 0 P.ν, Mr P δ ≤ Mr P s.δ1l := by
  refine ⟨hs.1.2.2.2.2.2.1, fun δ hδ => ?_⟩
  obtain ⟨s', hf', hh', hl', hobj⟩ := exists_plan P hP s.δ1h δ hs.1.2.2.2.2.1 hδ
  have h1 := hs.2 s' hf'
  have h2 := feasible_le P hP s hs.1
  linarith

lemma fb_max (P : Params) (hP : P.Standing) (fh fl : ℝ) (hf : IsFBOptimal P fh fl) :
    fl ∈ Icc 0 P.ν ∧ ∀ δ ∈ Icc 0 P.ν, Fr P δ ≤ Fr P fl := by
  refine ⟨hf.2.1, fun δ hδ => ?_⟩
  have h := hf.2.2 fh hf.1 δ hδ
  have hm0 := (hP.2.2.2.2.2.2.2.1) _ (d0_mem P hP)
  have key : fbObjective P fh δ - fbObjective P fh fl =
      (1 - P.pw P.d0) * (Fr P δ - Fr P fl) := by
    unfold fbObjective objective J2aLow Fr; ring
  have hc : 0 < 1 - P.pw P.d0 := by linarith [hm0.2.2]
  have : (1 - P.pw P.d0) * (Fr P δ - Fr P fl) ≤ 0 := by linarith
  have := (mul_nonpos_iff_pos_imp_nonpos.1 this).1 hc
  linarith

lemma Fr_unique (P : Params) (hP : P.Standing) {a b : ℝ} (ha : a ∈ Icc 0 P.ν)
    (hb : b ∈ Icc 0 P.ν) (hma : ∀ δ ∈ Icc 0 P.ν, Fr P δ ≤ Fr P a)
    (hmb : ∀ δ ∈ Icc 0 P.ν, Fr P δ ≤ Fr P b) : a = b := by
  by_contra hne
  have hν := hP.2.2.1
  have hαl := hP.2.2.2.2.2.1
  have hαlh := hP.2.2.2.2.2.2.1
  have hpwc := hP.2.2.2.2.2.2.2.2.2.1
  have hmid : (a + b) / 2 ∈ Icc 0 P.ν := ⟨by linarith [ha.1, hb.1], by linarith [ha.2, hb.2]⟩
  have h1 := hma _ hmid
  have hab := le_antisymm (hmb a ha) (hma b hb)
  have hc := hpwc.2 (mem_dom P hP ha) (mem_dom P hP hb) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at hc
  have hx : 1 / 2 * (P.d0 + a) + 1 / 2 * (P.d0 + b) = P.d0 + (a + b) / 2 := by ring
  rw [hx] at hc
  have hD : 0 ≤ J2b P.ν P.αh - J2b P.ν P.αl := by rw [J2b_diff P hP]; linarith
  have huv : a / P.ν ≠ b / P.ν := by
    intro h; apply hne; field_simp at h; exact h
  have hsq : 0 < (a / P.ν - b / P.ν) ^ 2 := by
    have : a / P.ν - b / P.ν ≠ 0 := sub_ne_zero.2 huv
    positivity
  unfold Fr at h1 hab
  rw [revenue_eq, revenue_eq] at h1
  rw [revenue_eq, revenue_eq] at hab
  have hm : (a + b) / 2 / P.ν = (a / P.ν + b / P.ν) / 2 := by ring
  rw [hm] at h1
  nlinarith [mul_le_mul_of_nonneg_left hc hD, mul_pos hαl hsq]

lemma gg_convex (P : Params) (hP : P.Standing) : ConvexOn ℝ (Icc 0 P.ν) (gg P) := by
  have hconv := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hκ := hP.2.2.2.2.1
  refine ⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => ?_⟩
  have h := hconv.2 (mem_dom P hP hx) (mem_dom P hP hy) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have he : a * (P.d0 + x) + b * (P.d0 + y) = P.d0 + (a * x + b * y) := by
    have : b = 1 - a := by linarith
    subst this; ring
  rw [he] at h
  unfold gg
  nlinarith [mul_le_mul_of_nonneg_left h hκ.le]

lemma rho_pos (P : Params) (hP : P.Standing) {d : ℝ} (hd : d ∈ Icc P.dmin P.dmax) :
    0 < dataImpact P d := by
  have hm := (hP.2.2.2.2.2.2.2.1) _ hd
  unfold dataImpact
  apply div_pos <;> linarith [hm.1, hm.2.1]

lemma gg_anti (P : Params) (hP : P.Standing)
    (hmono : StrictMonoOn (dataImpact P) (Icc P.dmin P.dmax)) :
    StrictAntiOn (gg P) (Icc 0 P.ν) := by
  intro x hx y hy hxy
  have h := hmono (mem_dom P hP hx) (mem_dom P hP hy) (by linarith)
  have hp := rho_pos P hP (mem_dom P hP hx)
  have hκ := hP.2.2.2.2.1
  unfold gg
  exact mul_lt_mul_of_pos_left (one_div_lt_one_div_of_lt hp h) hκ

lemma gg_mono (P : Params) (hP : P.Standing)
    (hanti : StrictAntiOn (dataImpact P) (Icc P.dmin P.dmax)) :
    StrictMonoOn (gg P) (Icc 0 P.ν) := by
  intro x hx y hy hxy
  have h := hanti (mem_dom P hP hx) (mem_dom P hP hy) (by linarith)
  have hp := rho_pos P hP (mem_dom P hP hy)
  have hκ := hP.2.2.2.2.1
  unfold gg
  exact mul_lt_mul_of_pos_left (one_div_lt_one_div_of_lt hp h) hκ

/-- Weak comparison: `g(a) ≤ g(b)` for `a` the second-best and `b` the first-best choice. -/
lemma gg_le (P : Params) (hP : P.Standing) (s : Plan) (hs : IsOptimal P s)
    (fh fl : ℝ) (hf : IsFBOptimal P fh fl) : gg P s.δ1l ≤ gg P fl := by
  obtain ⟨ha, hma⟩ := optimal_max P hP s hs
  obtain ⟨hb, hmb⟩ := fb_max P hP fh fl hf
  have h1 := hma fl hb
  have h2 := hmb s.δ1l ha
  have hm0 := (hP.2.2.2.2.2.2.2.1) _ (d0_mem P hP)
  have hc : 0 < 1 - P.pw P.d0 := by linarith [hm0.2.2]
  unfold Mr at h1
  nlinarith [mul_le_mul_of_nonneg_left h2 hc.le]

/-- Interior common maximizer forces a zero derivative of the convex agency cost. -/
lemma deriv_zero (P : Params) (hP : P.Standing) {a : ℝ} (ha : a ∈ Ioo 0 P.ν)
    (hma : ∀ δ ∈ Icc 0 P.ν, Mr P δ ≤ Mr P a) (hfa : ∀ δ ∈ Icc 0 P.ν, Fr P δ ≤ Fr P a) :
    HasDerivAt (gg P) 0 a := by
  have hd0 := hP.2.1
  have hdmax := hP.2.2.2.1
  have hx : P.d0 + a ∈ Ioo P.dmin P.dmax := ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hnhds : Icc P.dmin P.dmax ∈ nhds (P.d0 + a) := Icc_mem_nhds hx.1 hx.2
  have hpwd : DifferentiableAt ℝ P.pw (P.d0 + a) :=
    (hP.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (Ioo_subset_Icc_self hx)).differentiableAt hnhds
  have hpsd : DifferentiableAt ℝ P.ps (P.d0 + a) :=
    (hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (Ioo_subset_Icc_self hx)).differentiableAt hnhds
  have hm := (hP.2.2.2.2.2.2.2.1) _ (Ioo_subset_Icc_self hx)
  have hpw0 : P.pw (P.d0 + a) ≠ 0 := by linarith [hm.1, hm.2.1]
  have hrho0 : dataImpact P (P.d0 + a) ≠ 0 :=
    (rho_pos P hP (Ioo_subset_Icc_self hx)).ne'
  have hsh : DifferentiableAt ℝ (fun δ : ℝ => P.d0 + δ) a := by fun_prop
  have hpwc : DifferentiableAt ℝ (fun δ => P.pw (P.d0 + δ)) a := hpwd.comp a hsh
  have hpsc : DifferentiableAt ℝ (fun δ => P.ps (P.d0 + δ)) a := hpsd.comp a hsh
  have hrhod : DifferentiableAt ℝ (fun δ => dataImpact P (P.d0 + δ)) a := by
    unfold dataImpact
    exact (hpwc.sub hpsc).div hpwc hpw0
  have hgd : DifferentiableAt ℝ (gg P) a := by
    unfold gg
    exact (differentiableAt_const _).mul ((differentiableAt_const _).div hrhod hrho0)
  have hFd : DifferentiableAt ℝ (Fr P) a := by
    unfold Fr revenue uniformQuantile
    exact (by fun_prop : DifferentiableAt ℝ (fun δ : ℝ => P.αl * (δ / P.ν) * (1 - δ / P.ν)) a).add
      (hpwc.mul (differentiableAt_const _))
  have hIcc : Icc 0 P.ν ∈ nhds a := Icc_mem_nhds ha.1 ha.2
  have hFmax : IsLocalMax (Fr P) a := IsMaxOn.isLocalMax (fun δ hδ => hfa δ hδ) hIcc
  have hMmax : IsLocalMax (Mr P) a := IsMaxOn.isLocalMax (fun δ hδ => hma δ hδ) hIcc
  have hF0 := hFmax.hasDerivAt_eq_zero hFd.hasDerivAt
  have hMd : HasDerivAt (Mr P) ((1 - P.pw P.d0) * deriv (Fr P) a - deriv (gg P) a) a :=
    (hFd.hasDerivAt.const_mul _).sub hgd.hasDerivAt
  have hM0 := hMmax.hasDerivAt_eq_zero hMd
  rw [hF0] at hM0
  have : deriv (gg P) a = 0 := by linarith
  rw [← this]; exact hgd.hasDerivAt

lemma not_equal (P : Params) (hP : P.Standing) (s : Plan) (hs : IsOptimal P s)
    (fh fl : ℝ) (hf : IsFBOptimal P fh fl) (ha : s.δ1l ∈ Ioo 0 P.ν)
    (hmon : StrictMonoOn (dataImpact P) (Icc P.dmin P.dmax) ∨
      StrictAntiOn (dataImpact P) (Icc P.dmin P.dmax)) : s.δ1l ≠ fl := by
  intro heq
  obtain ⟨ha', hma⟩ := optimal_max P hP s hs
  obtain ⟨_, hmb⟩ := fb_max P hP fh fl hf
  rw [← heq] at hmb
  have hd := deriv_zero P hP ha hma hmb
  have hcv := gg_convex P hP
  set a := s.δ1l
  rcases hmon with hmono | hanti
  · -- g strictly decreasing: look to the right
    have hanti' := gg_anti P hP hmono
    have hy : (a + P.ν) / 2 ∈ Icc 0 P.ν := ⟨by linarith [ha.1, ha.2], by linarith [ha.2]⟩
    have hlt : a < (a + P.ν) / 2 := by linarith [ha.2]
    have h1 := hcv.le_slope_of_hasDerivAt ha' hy hlt hd
    have h2 := hanti' ha' hy hlt
    rw [slope_def_field] at h1
    have : (gg P ((a + P.ν) / 2) - gg P a) / ((a + P.ν) / 2 - a) < 0 :=
      div_neg_of_neg_of_pos (by linarith) (by linarith)
    linarith
  · have hmono' := gg_mono P hP hanti
    have hy : a / 2 ∈ Icc 0 P.ν := ⟨by linarith [ha.1], by linarith [ha.1, ha.2]⟩
    have hlt : a / 2 < a := by linarith [ha.1]
    have h1 := hcv.slope_le_of_hasDerivAt hy ha' hlt hd
    have h2 := hmono' hy ha' hlt
    rw [slope_def_field] at h1
    have : 0 < (gg P a - gg P (a / 2)) / (a - a / 2) :=
      div_pos (by linarith) (by linarith)
    linarith

end AIFlywheelT1Aux

open AIFlywheel.Pricing AIFlywheelT1Aux

theorem solution (P : Params) (hP : P.Standing)
    (s : Plan) (hs : IsOptimal P s)
    (fh fl : ℝ) (hf : IsFBOptimal P fh fl) :
    (StrictAntiOn (dataImpact P) (Set.Icc P.dmin P.dmax) → s.δ1l ≤ fl) ∧
    (StrictMonoOn (dataImpact P) (Set.Icc P.dmin P.dmax) → fl ≤ s.δ1l) := by
  obtain ⟨ha, _⟩ := optimal_max P hP s hs
  obtain ⟨hb, _⟩ := fb_max P hP fh fl hf
  have hle := gg_le P hP s hs fh fl hf
  refine ⟨fun hanti => ?_, fun hmono => ?_⟩
  · by_contra h
    push Not at h
    exact absurd (gg_mono P hP hanti hb ha h) (not_lt.2 hle)
  · by_contra h
    push Not at h
    exact absurd (gg_anti P hP hmono ha hb h) (not_lt.2 hle)
