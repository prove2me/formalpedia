-- Prove2me | solution 1 for AIFlywheel.Pricing.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T04:17:41.136524+00:00
-- url     : https://prove2.me/submissions/2b18b8ce-145b-4b30-a833-2e1d99edfd76

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


noncomputable def plan0 (P : Params) (h δ : ℝ) : Plan :=
  ⟨P.κ / (P.pw P.d0 - P.ps P.d0) + (gg P δ - P.κ), 0,
   P.κ / (P.pw (P.d0 + δ) - P.ps (P.d0 + δ)), 0, h, δ⟩

lemma plan0_spec (P : Params) (hP : P.Standing) (h δ : ℝ) (hh : h ∈ Icc 0 P.ν)
    (hδ : δ ∈ Icc 0 P.ν) :
    (plan0 P h δ).Feasible P ∧ objective P (plan0 P h δ) = Bh P h + Mr P δ := by
  unfold plan0
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
  refine ⟨?_, ?_⟩
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


lemma obj_identity (P : Params) (s : Plan) :
    objective P s = Bh P s.δ1h + Mr P s.δ1l -
      (P.pw P.d0 * (s.x1h - s.x1l - (P.pw (P.d0 + s.δ1l) * s.x2h +
          (1 - P.pw (P.d0 + s.δ1l)) * s.x2l - P.κ) - P.κ / (P.pw P.d0 - P.ps P.d0))
        + s.x1l + s.x2l + (P.pw (P.d0 + s.δ1l) * (s.x2h - s.x2l) - gg P s.δ1l)) := by
  unfold objective J2aLow Bh Mr Fr; ring

lemma slacks (P : Params) (hP : P.Standing) (s : Plan) (hs : s.Feasible P) :
    0 ≤ s.x1h - s.x1l - (P.pw (P.d0 + s.δ1l) * s.x2h +
          (1 - P.pw (P.d0 + s.δ1l)) * s.x2l - P.κ) - P.κ / (P.pw P.d0 - P.ps P.d0) ∧
    0 ≤ P.pw (P.d0 + s.δ1l) * (s.x2h - s.x2l) - gg P s.δ1l := by
  obtain ⟨h1h, h1l, h2h, h2l, hδh, hδl, hIC1, hIC2⟩ := hs
  have hm := (hP.2.2.2.2.2.2.2.1) _ (mem_dom P hP hδl)
  have hm0 := (hP.2.2.2.2.2.2.2.1) _ (d0_mem P hP)
  have hκ := hP.2.2.2.2.1
  have hgg := gg_eq P hP hδl
  unfold providerCont at hIC1 hIC2
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
  exact ⟨by linarith, by linarith⟩

lemma c0_pos (P : Params) (hP : P.Standing) : 0 < P.pw P.d0 := by
  have hm0 := (hP.2.2.2.2.2.2.2.1) _ (d0_mem P hP)
  linarith [hm0.1, hm0.2.1]

/-- Lemma 2 in terms of `plan0`. -/
lemma plan0_unique (P : Params) (hP : P.Standing) (s : Plan) (hs : s.Feasible P) :
    objective P s ≤ objective P (plan0 P s.δ1h s.δ1l) ∧
      (objective P s = objective P (plan0 P s.δ1h s.δ1l) → s = plan0 P s.δ1h s.δ1l) := by
  obtain ⟨_, hobj0⟩ := plan0_spec P hP s.δ1h s.δ1l hs.2.2.2.2.1 hs.2.2.2.2.2.1
  obtain ⟨k1, k2⟩ := slacks P hP s hs
  have hid := obj_identity P s
  have hc0 := c0_pos P hP
  have hx1l := hs.2.1
  have hx2l := hs.2.2.2.1
  rw [hobj0]
  have e1 := mul_nonneg hc0.le k1
  refine ⟨by linarith, fun heq => ?_⟩
  have z1l : s.x1l = 0 := by linarith
  have z2l : s.x2l = 0 := by linarith
  have z2 : P.pw (P.d0 + s.δ1l) * (s.x2h - s.x2l) - gg P s.δ1l = 0 := by linarith
  have z1' : P.pw P.d0 * (s.x1h - s.x1l - (P.pw (P.d0 + s.δ1l) * s.x2h +
          (1 - P.pw (P.d0 + s.δ1l)) * s.x2l - P.κ) - P.κ / (P.pw P.d0 - P.ps P.d0)) = 0 := by
    linarith
  have z1 := (mul_eq_zero.1 z1').resolve_left hc0.ne'
  have hδl := hs.2.2.2.2.2.1
  have hm := (hP.2.2.2.2.2.2.2.1) _ (mem_dom P hP hδl)
  have hp1 : P.pw (P.d0 + s.δ1l) ≠ 0 := by linarith [hm.1, hm.2.1]
  have hgg := gg_eq P hP hδl
  have hx2h : s.x2h = P.κ / (P.pw (P.d0 + s.δ1l) - P.ps (P.d0 + s.δ1l)) := by
    apply mul_left_cancel₀ hp1
    rw [z2l] at z2
    have : P.pw (P.d0 + s.δ1l) * s.x2h = gg P s.δ1l := by linarith
    rw [this, hgg]; ring
  have hx1h : s.x1h = P.κ / (P.pw P.d0 - P.ps P.d0) + (gg P s.δ1l - P.κ) := by
    rw [z1l, z2l] at z1; rw [z2l] at z2; linarith
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := s
  simp only at hx1h hx2h z1l z2l
  simp only [plan0, Plan.mk.injEq]
  exact ⟨hx1h, z1l, hx2h, z2l, trivial, trivial⟩

lemma rev_le (ν α : ℝ) (hα : 0 ≤ α) (δ : ℝ) : revenue ν δ α ≤ revenue ν (ν / 2) α ∨ ν = 0 := by
  rcases eq_or_ne ν 0 with h | h
  · exact Or.inr h
  left
  rw [revenue_eq, revenue_eq]
  have e : ν / 2 / ν = 1 / 2 := by field_simp
  rw [e]
  have h1 : (δ / ν) * (1 - δ / ν) ≤ 1 / 4 := by nlinarith [sq_nonneg (δ / ν - 1 / 2)]
  nlinarith [mul_le_mul_of_nonneg_left h1 hα]

lemma rev_le' (ν α : ℝ) (hν : 0 < ν) (hα : 0 ≤ α) (δ : ℝ) :
    revenue ν δ α ≤ revenue ν (ν / 2) α :=
  (rev_le ν α hα δ).resolve_right hν.ne'

lemma rev_eq (ν α : ℝ) (hν : 0 < ν) (hα : 0 < α) (δ : ℝ)
    (h : revenue ν δ α = revenue ν (ν / 2) α) : δ = ν / 2 := by
  rw [revenue_eq, revenue_eq] at h
  have e : ν / 2 / ν = 1 / 2 := by field_simp
  rw [e] at h
  have h2 : α * (δ / ν - 1 / 2) ^ 2 = 0 := by nlinarith
  have h3 : (δ / ν - 1 / 2) ^ 2 = 0 := (mul_eq_zero.1 h2).resolve_left hα.ne'
  have h4 : δ / ν = 1 / 2 := by
    have := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 h3
    linarith
  field_simp at h4
  linarith

lemma rev_lt (ν α : ℝ) (hν : 0 < ν) (hα : 0 < α) (δ : ℝ) (hne : δ ≠ ν / 2) :
    revenue ν δ α < revenue ν (ν / 2) α :=
  lt_of_le_of_ne (rev_le' ν α hν hα.le δ) (fun h => hne (rev_eq ν α hν hα δ h))

lemma Fr_mid (P : Params) (hP : P.Standing) {a b : ℝ} (ha : a ∈ Icc 0 P.ν)
    (hb : b ∈ Icc 0 P.ν) (hne : a ≠ b) : Fr P a + Fr P b < 2 * Fr P ((a + b) / 2) := by
  have hν := hP.2.2.1
  have hαl := hP.2.2.2.2.2.1
  have hpwc := hP.2.2.2.2.2.2.2.2.2.1
  have hc := hpwc.2 (mem_dom P hP ha) (mem_dom P hP hb) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at hc
  have hx : 1 / 2 * (P.d0 + a) + 1 / 2 * (P.d0 + b) = P.d0 + (a + b) / 2 := by ring
  rw [hx] at hc
  have hD : 0 ≤ J2b P.ν P.αh - J2b P.ν P.αl := by
    rw [J2b_diff P hP]; linarith [hP.2.2.2.2.2.2.1]
  have huv : a / P.ν ≠ b / P.ν := by
    intro h; apply hne; field_simp at h; exact h
  have hsq : 0 < (a / P.ν - b / P.ν) ^ 2 := by
    have : a / P.ν - b / P.ν ≠ 0 := sub_ne_zero.2 huv
    positivity
  unfold Fr
  rw [revenue_eq, revenue_eq, revenue_eq]
  have hm : (a + b) / 2 / P.ν = (a / P.ν + b / P.ν) / 2 := by ring
  rw [hm]
  nlinarith [mul_le_mul_of_nonneg_left hc hD, mul_pos hαl hsq]

lemma Mr_unique (P : Params) (hP : P.Standing) {a b : ℝ} (ha : a ∈ Icc 0 P.ν)
    (hb : b ∈ Icc 0 P.ν) (hma : ∀ δ ∈ Icc 0 P.ν, Mr P δ ≤ Mr P a)
    (hab : Mr P b = Mr P a) : b = a := by
  by_contra hne
  have hmid : (b + a) / 2 ∈ Icc 0 P.ν := ⟨by linarith [ha.1, hb.1], by linarith [ha.2, hb.2]⟩
  have h1 := hma _ hmid
  have hF := Fr_mid P hP hb ha hne
  have hg := (gg_convex P hP).2 hb ha (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at hg
  have hx : 1 / 2 * b + 1 / 2 * a = (b + a) / 2 := by ring
  rw [hx] at hg
  have hm0 := (hP.2.2.2.2.2.2.2.1) _ (d0_mem P hP)
  have hc : 0 < 1 - P.pw P.d0 := by linarith [hm0.2.2]
  unfold Mr at h1 hab
  nlinarith [mul_lt_mul_of_pos_left hF hc]

lemma shift_cont (P : Params) (hP : P.Standing) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc P.dmin P.dmax)) :
    ContinuousOn (fun δ => f (P.d0 + δ)) (Icc 0 P.ν) :=
  hf.comp (by fun_prop) (fun δ hδ => mem_dom P hP hδ)

lemma Fr_cont (P : Params) (hP : P.Standing) : ContinuousOn (Fr P) (Icc 0 P.ν) := by
  have hpw := shift_cont P hP (hP.2.2.2.2.2.2.2.2.2.2.2.2.1).continuousOn
  unfold Fr revenue uniformQuantile
  exact (by fun_prop : Continuous (fun δ : ℝ => P.αl * (δ / P.ν) * (1 - δ / P.ν))).continuousOn.add
    (hpw.mul continuousOn_const)

lemma gg_cont (P : Params) (hP : P.Standing) : ContinuousOn (gg P) (Icc 0 P.ν) := by
  have hpw := shift_cont P hP (hP.2.2.2.2.2.2.2.2.2.2.2.2.1).continuousOn
  have hps := shift_cont P hP (hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1).continuousOn
  have hpw0 : ∀ δ ∈ Icc 0 P.ν, P.pw (P.d0 + δ) ≠ 0 := by
    intro δ hδ
    have hm := (hP.2.2.2.2.2.2.2.1) _ (mem_dom P hP hδ)
    linarith [hm.1, hm.2.1]
  have hr0 : ∀ δ ∈ Icc 0 P.ν, dataImpact P (P.d0 + δ) ≠ 0 :=
    fun δ hδ => (rho_pos P hP (mem_dom P hP hδ)).ne'
  have hr : ContinuousOn (fun δ => dataImpact P (P.d0 + δ)) (Icc 0 P.ν) := by
    unfold dataImpact
    exact (hpw.sub hps).div hpw hpw0
  unfold gg
  exact continuousOn_const.mul (continuousOn_const.div hr hr0)

lemma Fr_eq_red (P : Params) (hP : P.Standing) (δ : ℝ) : reducedFBObjective P δ = Fr P δ := by
  unfold reducedFBObjective Fr
  rw [J2b_diff P hP]; unfold tau phiInvZero; ring

lemma Mr_eq_red (P : Params) (hP : P.Standing) (δ : ℝ) :
    reducedMoralObjective P δ = Mr P δ := by
  unfold reducedMoralObjective Mr gg
  rw [← Fr_eq_red P hP]; unfold reducedFBObjective; ring

lemma deltaM_eq (ν : ℝ) : deltaM ν = ν / 2 := by unfold deltaM phiInvZero; ring

lemma Bh_le (P : Params) (hP : P.Standing) (h : ℝ) : Bh P h ≤ Bh P (P.ν / 2) := by
  have := rev_le' P.ν P.αh hP.2.2.1 (by linarith [hP.2.2.2.2.2.1, hP.2.2.2.2.2.2.1]) h
  have hc := c0_pos P hP
  unfold Bh
  nlinarith [mul_le_mul_of_nonneg_left this hc.le]

lemma Bh_eq (P : Params) (hP : P.Standing) (h : ℝ) (heq : Bh P h = Bh P (P.ν / 2)) :
    h = P.ν / 2 := by
  have hc := c0_pos P hP
  apply rev_eq P.ν P.αh hP.2.2.1 (by linarith [hP.2.2.2.2.2.1, hP.2.2.2.2.2.2.1])
  unfold Bh at heq
  have : P.pw P.d0 * (revenue P.ν h P.αh - revenue P.ν (P.ν / 2) P.αh) = 0 := by linarith
  have := (mul_eq_zero.1 this).resolve_left hc.ne'
  linarith

lemma fb_split (P : Params) (e1 e2 : ℝ) :
    fbObjective P e1 e2 = P.pw P.d0 * revenue P.ν e1 P.αh + (1 - P.pw P.d0) * Fr P e2 +
      (P.pw P.d0 * (J2b P.ν P.αh - P.κ) + (1 - P.pw P.d0) * (J2b P.ν P.αl - 2 * P.κ)) := by
  unfold fbObjective objective J2aLow Fr; ring
end AIFlywheelT1Aux

open AIFlywheel.Pricing AIFlywheelT1Aux

theorem solution (P : Params) (hP : P.Standing) :
    ∃ δFB : ℝ,
      δFB ∈ Set.Icc 0 P.ν ∧
      (∀ δ ∈ Set.Icc 0 P.ν,
        reducedFBObjective P δ ≤ reducedFBObjective P δFB) ∧
      (∀ δ ∈ Set.Icc 0 P.ν,
        reducedFBObjective P δ = reducedFBObjective P δFB → δ = δFB) ∧
      deltaM P.ν < δFB ∧
      (∃! p : ℝ × ℝ, IsFBOptimal P p.1 p.2) ∧
      ∀ h l : ℝ, IsFBOptimal P h l →
        h = deltaM P.ν ∧ l = δFB := by
  have hν := hP.2.2.1
  obtain ⟨b, hb, hbmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hν.le) (Fr_cont P hP)
  have hmb : ∀ δ ∈ Icc 0 P.ν, Fr P δ ≤ Fr P b := fun δ hδ => hbmax hδ
  have huniq : ∀ δ ∈ Icc 0 P.ν, Fr P δ = Fr P b → δ = b := by
    intro δ hδ h
    exact Fr_unique P hP hδ hb (fun x hx => h ▸ hmb x hx) hmb
  have hc := c0_pos P hP
  have hm0 := (hP.2.2.2.2.2.2.2.1) _ (d0_mem P hP)
  have hc1 : 0 < 1 - P.pw P.d0 := by linarith [hm0.2.2]
  have hνh : P.ν / 2 ∈ Icc 0 P.ν := ⟨by linarith, by linarith⟩
  have hαl := hP.2.2.2.2.2.1
  have hαh : 0 < P.αh := by linarith [hP.2.2.2.2.2.1, hP.2.2.2.2.2.2.1]
  have hD : 0 < J2b P.ν P.αh - J2b P.ν P.αl := by
    rw [J2b_diff P hP]; linarith [hP.2.2.2.2.2.2.1]
  have hopt : IsFBOptimal P (P.ν / 2) b := by
    refine ⟨hνh, hb, fun e1 _ e2 he2 => ?_⟩
    rw [fb_split, fb_split]
    nlinarith [mul_le_mul_of_nonneg_left (rev_le' P.ν P.αh hν hαh.le e1) hc.le,
      mul_le_mul_of_nonneg_left (hmb e2 he2) hc1.le]
  have hall : ∀ h l : ℝ, IsFBOptimal P h l → h = P.ν / 2 ∧ l = b := by
    intro h l hf
    obtain ⟨hl, hml⟩ := fb_max P hP h l hf
    have hlb : l = b := Fr_unique P hP hl hb hml hmb
    refine ⟨?_, hlb⟩
    have h1 := hf.2.2 (P.ν / 2) hνh l hl
    rw [fb_split, fb_split] at h1
    have h2 := rev_le' P.ν P.αh hν hαh.le h
    have : revenue P.ν h P.αh = revenue P.ν (P.ν / 2) P.αh := by
      by_contra hne
      have hlt := lt_of_le_of_ne h2 hne
      nlinarith [mul_lt_mul_of_pos_left hlt hc]
    exact rev_eq P.ν P.αh hν hαh h this
  have gt_half : P.ν / 2 < b := by
    by_contra hle
    push Not at hle
    have hpwm := hP.2.2.2.2.2.2.2.2.1
    rcases hle.lt_or_eq with hlt | heq
    · have h1 := rev_lt P.ν P.αl hν hαl b hlt.ne
      have h2 := hpwm (mem_dom P hP hb) (mem_dom P hP hνh) (by linarith)
      have h3 := hmb _ hνh
      unfold Fr at h3
      nlinarith [mul_lt_mul_of_pos_right h2 hD]
    · -- first-order condition at ν/2
      set a := P.ν / 2 with ha_def
      have haI : a ∈ Ioo 0 P.ν := ⟨by linarith, by linarith⟩
      have hd0 := hP.2.1
      have hdmax := hP.2.2.2.1
      have hx : P.d0 + a ∈ Ioo P.dmin P.dmax := ⟨by linarith [haI.1], by linarith [haI.2]⟩
      have hnhds : Icc P.dmin P.dmax ∈ nhds (P.d0 + a) := Icc_mem_nhds hx.1 hx.2
      have hpwd : DifferentiableAt ℝ P.pw (P.d0 + a) :=
        (hP.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (Ioo_subset_Icc_self hx)).differentiableAt hnhds
      have hsh : HasDerivAt (fun δ : ℝ => P.d0 + δ) 1 a := (hasDerivAt_id a).const_add P.d0
      have hpwS : HasDerivAt (fun δ => P.pw (P.d0 + δ)) (deriv P.pw (P.d0 + a) * 1) a :=
        hpwd.hasDerivAt.comp a hsh
      have hRd : DifferentiableAt ℝ (fun δ => revenue P.ν δ P.αl) a := by
        unfold revenue uniformQuantile; fun_prop
      have hFd : HasDerivAt (Fr P) (deriv (fun δ => revenue P.ν δ P.αl) a +
          deriv P.pw (P.d0 + a) * 1 * (J2b P.ν P.αh - J2b P.ν P.αl)) a := by
        unfold Fr
        exact hRd.hasDerivAt.add (hpwS.mul_const _)
      have hIcc : Icc 0 P.ν ∈ nhds a := Icc_mem_nhds haI.1 haI.2
      have hFmax : IsLocalMax (Fr P) a :=
        IsMaxOn.isLocalMax (fun δ hδ => by rw [← heq]; exact hmb δ hδ) hIcc
      have hRmax : IsLocalMax (fun δ => revenue P.ν δ P.αl) a :=
        IsMaxOn.isLocalMax (s := univ) (fun δ _ => rev_le' P.ν P.αl hν hαl.le δ)
          Filter.univ_mem
      have e1 := hFmax.hasDerivAt_eq_zero hFd
      have e2 := hRmax.hasDerivAt_eq_zero hRd.hasDerivAt
      rw [e2] at e1
      have hpw0 : deriv P.pw (P.d0 + a) = 0 := by
        have : deriv P.pw (P.d0 + a) * (J2b P.ν P.αh - J2b P.ν P.αl) = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_right hD.ne'
      have hy : P.d0 + P.ν ∈ Icc P.dmin P.dmax := mem_dom P hP ⟨hν.le, le_refl _⟩
      have hxy : P.d0 + a < P.d0 + P.ν := by linarith [haI.2]
      have hs := (hP.2.2.2.2.2.2.2.2.2.1).slope_le_of_hasDerivAt
        (Ioo_subset_Icc_self hx) hy hxy hpwd.hasDerivAt
      rw [hpw0, slope_def_field] at hs
      have hlt := hpwm (Ioo_subset_Icc_self hx) hy hxy
      have : 0 < (P.pw (P.d0 + P.ν) - P.pw (P.d0 + a)) / (P.d0 + P.ν - (P.d0 + a)) :=
        div_pos (by linarith) (by linarith)
      linarith
  refine ⟨b, hb, fun δ hδ => by rw [Fr_eq_red P hP, Fr_eq_red P hP]; exact hmb δ hδ,
    fun δ hδ h => by rw [Fr_eq_red P hP, Fr_eq_red P hP] at h; exact huniq δ hδ h, ?_,
    ⟨(P.ν / 2, b), hopt, fun p hp => ?_⟩, fun h l hf => by rw [deltaM_eq]; exact hall h l hf⟩
  · rw [deltaM_eq]; exact gt_half
  · obtain ⟨e1, e2⟩ := hall p.1 p.2 hp; exact Prod.ext e1 e2
