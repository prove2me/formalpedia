-- Prove2me | solution 1 for AddictivePlatforms.Costly.lemma_D_3
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-22T09:35:39.020678+00:00
-- url     : https://prove2.me/submissions/e4ad6e76-bf3f-4a4d-b1a8-885b119e95eb

import Mathlib
import Definitions.Def_AddictivePlatforms_Costly_Model

open Set Filter Topology
open scoped ENNReal

namespace AddictivePlatforms.Costly.D3Counter

/-- The counterexample primitives. -/
noncomputable def vX : ℝ → ℝ := fun x => 2 - Real.exp (-x)
noncomputable def CX : ℝ → ℝ := fun a => (Real.exp a - 1) / 2
noncomputable def γX : ℝ → ℝ := fun d => d ^ 2
noncomputable def gX : ℝ → ℝ := fun y => -Real.log y

theorem uX_eq (a d : ℝ) : uOf vX a d = 2 - Real.exp (d - a) := by
  simp only [uOf, vX]; ring_nf

theorem hasDerivAt_vX (x : ℝ) : HasDerivAt vX (Real.exp (-x)) x := by
  have h : HasDerivAt (fun y : ℝ => 2 - Real.exp (-y)) (0 - Real.exp (-x) * (-1)) x :=
    (hasDerivAt_const x (2:ℝ)).sub (hasDerivAt_neg x).exp
  have e : (0:ℝ) - Real.exp (-x) * (-1) = Real.exp (-x) := by ring
  rw [e] at h
  exact h

theorem deriv_vX (x : ℝ) : deriv vX x = Real.exp (-x) := (hasDerivAt_vX x).deriv

theorem hasDerivAt_CX (x : ℝ) : HasDerivAt CX (Real.exp x / 2) x := by
  have h : HasDerivAt (fun y : ℝ => (Real.exp y - 1) / 2) (Real.exp x / 2) x :=
    ((Real.hasDerivAt_exp x).sub_const 1).div_const 2
  exact h

theorem Cderiv_CX (x : ℝ) (hx : 0 ≤ x) :
    AddictivePlatforms.Compete.Cderiv CX x = Real.exp x / 2 := by
  unfold AddictivePlatforms.Compete.Cderiv
  exact (hasDerivAt_CX x).hasDerivWithinAt.derivWithin ((uniqueDiffOn_Ici 0) x hx)

theorem Cderiv2_CX (x : ℝ) (hx : 0 ≤ x) : Cderiv2 CX x = Real.exp x / 2 := by
  unfold Cderiv2
  have heq : EqOn (AddictivePlatforms.Compete.Cderiv CX) (fun y => Real.exp y / 2) (Ici 0) :=
    fun y hy => Cderiv_CX y hy
  rw [derivWithin_congr heq (heq hx)]
  have h : HasDerivAt (fun y => Real.exp y / 2) (Real.exp x / 2) x :=
    (Real.hasDerivAt_exp x).div_const 2
  exact h.hasDerivWithinAt.derivWithin ((uniqueDiffOn_Ici 0) x hx)

theorem hasDerivAt_uX (a d : ℝ) : HasDerivAt (fun x => uOf vX x d) (Real.exp (d - a)) a := by
  have hf : (fun x => uOf vX x d) = (fun x : ℝ => 2 - Real.exp (d - x)) := by
    funext x; exact uX_eq x d
  rw [hf]
  have h : HasDerivAt (fun x : ℝ => 2 - Real.exp (d - x)) (0 - Real.exp (d - a) * (0 - 1)) a :=
    (hasDerivAt_const a (2:ℝ)).sub ((hasDerivAt_const a d).sub (hasDerivAt_id a)).exp
  have e : (0:ℝ) - Real.exp (d - a) * (0 - 1) = Real.exp (d - a) := by ring
  rw [e] at h
  exact h

theorem u1_X (a d : ℝ) (ha : 0 ≤ a) :
    AddictivePlatforms.Compete.u1 (uOf vX) a d = Real.exp (d - a) := by
  unfold AddictivePlatforms.Compete.u1
  exact (hasDerivAt_uX a d).hasDerivWithinAt.derivWithin ((uniqueDiffOn_Ici 0) a ha)

theorem strictConcave_uX (d : ℝ) : StrictConcaveOn ℝ (Ici 0) (fun a => uOf vX a d) := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0)
  · exact fun x _ => (hasDerivAt_uX x d).continuousAt.continuousWithinAt
  · intro x _ y _ hxy
    rw [(hasDerivAt_uX x d).deriv, (hasDerivAt_uX y d).deriv]
    exact Real.exp_lt_exp.2 (by linarith)

theorem uncurry_X : Function.uncurry (uOf vX) = fun p : ℝ × ℝ => 2 - Real.exp (p.2 - p.1) := by
  funext p; exact uX_eq p.1 p.2

theorem contDiff_uncurry_X : ContDiff ℝ 2 (Function.uncurry (uOf vX)) := by
  rw [uncurry_X]
  apply contDiff_const.sub
  exact Real.contDiff_exp.comp (contDiff_snd.sub contDiff_fst)

theorem assumption1_X : AddictivePlatforms.Compete.Assumption1 (uOf vX) CX where
  differentiableOn := (contDiff_uncurry_X.differentiable (by norm_num)).differentiableOn
  differentiableOn_fderivWithin := by
    have hU : UniqueDiffOn ℝ AddictivePlatforms.Compete.quadrant :=
      (uniqueDiffOn_Ici 0).prod (uniqueDiffOn_Ici 0)
    have := (contDiff_uncurry_X.contDiffOn (s := AddictivePlatforms.Compete.quadrant)).fderivWithin hU
      (m := 1) (by norm_num)
    exact this.differentiableOn (by norm_num)
  strictMonoOn_a := by
    intro d _ x _ y _ hxy
    simp only [uX_eq]
    have := Real.exp_lt_exp.2 (show d - y < d - x by linarith)
    linarith
  concaveOn_a := fun d _ => (strictConcave_uX d).concaveOn
  u_zero_zero_nonneg := by rw [uX_eq]; norm_num
  strictAntiOn_d := by
    intro a _ x _ y _ hxy
    simp only [uX_eq]
    have := Real.exp_lt_exp.2 (show x - a < y - a by linarith)
    linarith
  exists_neg := by
    refine ⟨3, by norm_num, ?_⟩
    intro a _
    rw [uX_eq]
    simp only [CX]
    have hE : 0 < Real.exp a := Real.exp_pos a
    have hprod : Real.exp (3 - a) * Real.exp a = Real.exp 3 := by
      rw [← Real.exp_add]; ring_nf
    have h3 : (4:ℝ) ≤ Real.exp 3 := by
      have := Real.add_one_le_exp (3:ℝ); linarith
    nlinarith [sq_nonneg (Real.exp a - 5/2), Real.exp_pos (3 - a)]
  strictMonoOn_u1 := by
    intro a ha x _ y _ hxy
    simp only [u1_X a x ha, u1_X a y ha]
    exact Real.exp_lt_exp.2 (by linarith)

theorem assumption2_X : AddictivePlatforms.Compete.Assumption2 (uOf vX) CX where
  nonneg := by
    intro a ha
    simp only [CX]
    have := Real.add_one_le_exp a
    linarith
  strictMonoOn := by
    intro x _ y _ hxy
    simp only [CX]
    have := Real.exp_lt_exp.2 hxy
    linarith
  convexOn := by
    apply MonotoneOn.convexOn_of_deriv (convex_Ici 0)
    · exact fun x _ => (hasDerivAt_CX x).continuousAt.continuousWithinAt
    · exact fun x _ => (hasDerivAt_CX x).differentiableAt.differentiableWithinAt
    · intro x _ y _ hxy
      rw [(hasDerivAt_CX x).deriv, (hasDerivAt_CX y).deriv]
      have := Real.exp_le_exp.2 hxy
      linarith
  differentiableOn := fun x _ => (hasDerivAt_CX x).differentiableAt.differentiableWithinAt
  differentiableOn_deriv := by
    have h : DifferentiableOn ℝ (fun y : ℝ => Real.exp y / 2) (Ici 0) :=
      fun x _ => ((Real.hasDerivAt_exp x).div_const 2).differentiableAt.differentiableWithinAt
    exact h.congr (fun y hy => Cderiv_CX y hy)
  limit_pos := by
    left
    refine ⟨1/2, by norm_num, ?_⟩
    have hc : Tendsto (fun a : ℝ => Real.exp (-a) - Real.exp a / 2) (𝓝[>] 0) (𝓝 (1/2)) := by
      have : Continuous (fun a : ℝ => Real.exp (-a) - Real.exp a / 2) := by fun_prop
      have h0 := this.tendsto 0
      simp only [neg_zero, Real.exp_zero] at h0
      have : (1:ℝ) - 1/2 = 1/2 := by norm_num
      rw [this] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    apply hc.congr'
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha' : (0:ℝ) ≤ a := le_of_lt ha
    rw [u1_X a 0 ha', Cderiv_CX a ha']
    simp

theorem derivWithin_γX (d : ℝ) (hd : 0 ≤ d) : derivWithin γX (Ici 0) d = 2 * d := by
  have h : HasDerivAt γX (2 * d) d := by
    show HasDerivAt (fun x : ℝ => x ^ 2) (2 * d) d
    simpa using hasDerivAt_pow 2 d
  exact h.hasDerivWithinAt.derivWithin ((uniqueDiffOn_Ici 0) d hd)

theorem assumption3_X : Assumption3 vX CX γX gX where
  γ_nonneg := fun d _ => sq_nonneg d
  γ_monotoneOn := by
    intro x hx y _ hxy
    simp only [γX]
    exact pow_le_pow_left₀ hx hxy 2
  γ_strictConvexOn := strictConvexOn_pow (le_refl 2)
  γ_differentiableOn := fun x _ =>
    (show DifferentiableAt ℝ (fun x : ℝ => x ^ 2) x by fun_prop).differentiableWithinAt
  γ_deriv_zero := by
    have hc : Tendsto (fun d : ℝ => 2 * d) (𝓝[>] 0) (𝓝 0) := by
      have : Continuous (fun d : ℝ => 2 * d) := by fun_prop
      have h0 := this.tendsto 0
      simp only [mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    apply hc.congr'
    filter_upwards [self_mem_nhdsWithin] with a ha
    rw [derivWithin_γX a (le_of_lt ha)]
  γ_deriv_atTop := by
    have hc : Tendsto (fun d : ℝ => 2 * d) atTop atTop :=
      tendsto_id.const_mul_atTop (by norm_num)
    apply hc.congr'
    filter_upwards [eventually_ge_atTop 0] with a ha
    rw [derivWithin_γX a ha]
  g_leftInv := by
    intro x
    simp only [gX, deriv_vX, Real.log_exp, neg_neg]
  g_rightInv := by
    intro x hx
    rw [Cderiv_CX x hx, deriv_vX]
    simp only [gX, neg_neg]
    exact Real.exp_log (by positivity)
  g_differentiableAt := by
    intro x hx
    rw [Cderiv_CX x hx]
    have : Real.exp x / 2 ≠ 0 := by positivity
    show DifferentiableAt ℝ (fun y : ℝ => -Real.log y) (Real.exp x / 2)
    exact (Real.differentiableAt_log this).neg
  antitoneOn := by
    intro x hx y hy _
    have key : ∀ z : ℝ, 0 ≤ z →
        deriv gX (AddictivePlatforms.Compete.Cderiv CX z) * Cderiv2 CX z = -1 := by
      intro z hz
      rw [Cderiv_CX z hz, Cderiv2_CX z hz]
      have hne : Real.exp z / 2 ≠ 0 := by positivity
      have hd : deriv gX (Real.exp z / 2) = -(Real.exp z / 2)⁻¹ := by
        show deriv (fun y : ℝ => -Real.log y) (Real.exp z / 2) = -(Real.exp z / 2)⁻¹
        exact ((Real.hasDerivAt_log hne).neg).deriv
      rw [hd]
      field_simp
    show deriv gX (AddictivePlatforms.Compete.Cderiv CX y) * Cderiv2 CX y ≤
      deriv gX (AddictivePlatforms.Compete.Cderiv CX x) * Cderiv2 CX x
    rw [key x hx, key y hy]

theorem uncOpt_X (K : ℕ) : AddictivePlatforms.Compete.UncOptExists (uOf vX) CX K := by
  intro d _ J hJ
  have hJne : J ≠ ∅ := Finset.nonempty_iff_ne_empty.1 hJ
  set P : (Fin K → ℝ) → ℝ := fun a => ∑ k ∈ J, (2 - Real.exp (d k - a k)) -
    (Real.exp (∑ k ∈ J, a k) - 1) / 2 with hP
  have hpay : ∀ a : Fin K → ℝ, AddictivePlatforms.Compete.payoff (uOf vX) CX d
      ((J, a) : AddictivePlatforms.Compete.Choice K) = P a := by
    intro a
    simp only [AddictivePlatforms.Compete.payoff, hJne, if_false, uX_eq, CX, hP]
  have hPcont : Continuous P := by
    simp only [hP]
    fun_prop
  set p0 := P (fun _ => 0) with hp0
  set R : ℝ := max 0 (2 * (2 * (J.card : ℝ) - p0)) with hR
  have hR0 : 0 ≤ R := le_max_left _ _
  have hbound : ∀ a : Fin K → ℝ, P a ≤ 2 * (J.card : ℝ) - (Real.exp (∑ k ∈ J, a k) - 1) / 2 := by
    intro a
    simp only [hP]
    have : ∑ k ∈ J, (2 - Real.exp (d k - a k)) ≤ ∑ k ∈ J, (2:ℝ) :=
      Finset.sum_le_sum (fun k _ => by have := Real.exp_pos (d k - a k); linarith)
    rw [Finset.sum_const, nsmul_eq_mul] at this
    linarith
  set B : Set (Fin K → ℝ) := Set.pi univ (fun _ => Icc (0:ℝ) R) with hB
  have hBc : IsCompact B := isCompact_univ_pi (fun _ => isCompact_Icc)
  have h0B : (fun _ => (0:ℝ)) ∈ B := fun k _ => ⟨le_refl _, hR0⟩
  obtain ⟨a, haB, hmax⟩ := hBc.exists_isMaxOn ⟨_, h0B⟩ hPcont.continuousOn
  refine ⟨a, fun k _ => (haB k (mem_univ k)).1, ?_⟩
  intro a' ha'
  rw [hpay, hpay]
  set a'' : Fin K → ℝ := fun k => if k ∈ J then a' k else 0 with ha''
  have hPeq : P a' = P a'' := by
    simp only [hP, ha'']
    congr 1
    · apply Finset.sum_congr rfl; intro k hk; simp [hk]
    · rw [Finset.sum_congr rfl (fun k hk => by simp [hk] : ∀ k ∈ J, (if k ∈ J then a' k else 0) = a' k)]
  by_cases hS : ∑ k ∈ J, a' k ≤ R
  · have ha''B : a'' ∈ B := by
      intro k _
      simp only [ha'']
      split_ifs with hk
      · refine ⟨ha' k hk, le_trans ?_ hS⟩
        exact Finset.single_le_sum (fun j hj => ha' j hj) hk
      · exact ⟨le_refl _, hR0⟩
    rw [hPeq]; exact hmax ha''B
  · push Not at hS
    have h1 := hbound a'
    have h2 : R + 1 ≤ Real.exp (∑ k ∈ J, a' k) := by
      have := Real.add_one_le_exp (∑ k ∈ J, a' k); linarith
    have h3 : 2 * (2 * (J.card : ℝ) - p0) ≤ R := le_max_right _ _
    have h4 : P a' ≤ p0 := by linarith
    exact le_trans h4 (hmax h0B)

theorem standing_X (K : ℕ) : Standing vX CX γX gX K where
  assumption1 := assumption1_X
  assumption2 := assumption2_X
  assumption3 := assumption3_X
  strictConcaveOn_a := fun d _ => strictConcave_uX d
  C_zero := by simp [CX]
  uncOptExists := uncOpt_X K

/-- `exp z ≥ exp w (1 + z − w)`, strictly if `z ≠ w`. -/
theorem exp_tangent (z w : ℝ) : Real.exp w * (1 + (z - w)) ≤ Real.exp z := by
  have h := Real.add_one_le_exp (z - w)
  have hw := Real.exp_pos w
  have : Real.exp z = Real.exp w * Real.exp (z - w) := by rw [← Real.exp_add]; ring_nf
  rw [this]; nlinarith

theorem exp_tangent_strict (z w : ℝ) (h : z ≠ w) : Real.exp w * (1 + (z - w)) < Real.exp z := by
  have h1 := Real.add_one_lt_exp (sub_ne_zero.2 h)
  have hw := Real.exp_pos w
  have : Real.exp z = Real.exp w * Real.exp (z - w) := by rw [← Real.exp_add]; ring_nf
  rw [this]; nlinarith

theorem payoff_univ2 (d a : Fin 2 → ℝ) :
    AddictivePlatforms.Compete.payoff (uOf vX) CX d ((Finset.univ, a) : AddictivePlatforms.Compete.Choice 2) =
      (2 - Real.exp (d 0 - a 0)) + (2 - Real.exp (d 1 - a 1)) - (Real.exp (a 0 + a 1) - 1) / 2 := by
  have hne : (Finset.univ : Finset (Fin 2)) ≠ ∅ := by
    rw [← Finset.nonempty_iff_ne_empty]; exact ⟨0, Finset.mem_univ _⟩
  simp only [AddictivePlatforms.Compete.payoff, hne, if_false, Fin.sum_univ_two, uX_eq, CX]

theorem payoff_empty2 (d a : Fin 2 → ℝ) :
    AddictivePlatforms.Compete.payoff (uOf vX) CX d ((∅, a) : AddictivePlatforms.Compete.Choice 2) = 0 := by
  simp [AddictivePlatforms.Compete.payoff]

theorem feasible_top (J : Finset (Fin 2)) (a : Fin 2 → ℝ) (ha : ∀ k ∈ J, 0 ≤ a k) :
    AddictivePlatforms.Compete.Feasible ⊤ ((J, a) : AddictivePlatforms.Compete.Choice 2) :=
  ⟨ha, le_top⟩

/-- Joint profit at a profile, when the consumer joins all or none. -/
theorem jointProfit2 (κ : ℝ) (d : Fin 2 → ℝ) (x : AddictivePlatforms.Compete.Choice 2) :
    jointProfit γX κ d x = ((if (0 : Fin 2) ∈ x.1 then x.2 0 else 0) - κ * d 0 ^ 2) +
      ((if (1 : Fin 2) ∈ x.1 then x.2 1 else 0) - κ * d 1 ^ 2) := by
  unfold jointProfit platformPayoff
  rw [Fin.sum_univ_two]
  rfl

/-- The asymmetric profile `(0, log(50/9))` earns joint profit at least `log(10/3) − κ y₀²`. -/
theorem asym_profit (κ : ℝ) (σ : AddictivePlatforms.Compete.ConsumerStrategy 2)
    (p0 : Fin 2 → ℝ) (hp00 : p0 0 = 0) (hp01 : p0 1 = Real.log (50/9))
    (hR : RestrictedOpt (uOf vX) CX ⊤ p0 (σ p0)) :
    Real.log (10/3) - κ * Real.log (50/9) ^ 2 ≤ jointProfit γX κ p0 (σ p0) := by
  set y0 := Real.log (50/9) with hy0
  set b1 := Real.log (10/3) with hb1
  have hb1e : Real.exp b1 = 10/3 := Real.exp_log (by norm_num)
  have hy0e : Real.exp y0 = 50/9 := Real.exp_log (by norm_num)
  have hyb : Real.exp (y0 - b1) = 5/3 := by
    rw [Real.exp_sub, hb1e, hy0e]; norm_num
  have hb10 : 0 ≤ b1 := Real.log_nonneg (by norm_num)
  set b : Fin 2 → ℝ := ![0, b1] with hb
  -- payoff of `b`
  have hPb : AddictivePlatforms.Compete.payoff (uOf vX) CX p0
      ((Finset.univ, b) : AddictivePlatforms.Compete.Choice 2) = 1/6 := by
    rw [payoff_univ2, hp00, hp01]
    simp only [hb, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero, Real.exp_zero, zero_add]
    rw [hyb, hb1e]; norm_num
  -- tangent bound
  have htan : ∀ a : Fin 2 → ℝ, 0 ≤ a 0 → 0 ≤ a 1 →
      AddictivePlatforms.Compete.payoff (uOf vX) CX p0
        ((Finset.univ, a) : AddictivePlatforms.Compete.Choice 2) ≤ 1/6 - (2/3) * a 0 := by
    intro a ha0 ha1
    rw [payoff_univ2, hp00, hp01]
    have t1 := exp_tangent (0 - a 0) 0
    have t2 := exp_tangent (y0 - a 1) (y0 - b1)
    have t3 := exp_tangent (a 0 + a 1) b1
    rw [Real.exp_zero] at t1
    rw [hyb] at t2
    rw [hb1e] at t3
    nlinarith
  have hRopt := hR.2
  rcases hR.1.2 with hJ | hJ
  · -- joins none: contradiction with `b`
    exfalso
    have h1 := hRopt _ ⟨feasible_top Finset.univ b (by
      intro k _; fin_cases k <;> simp [hb, hb10]), Or.inr rfl⟩
    rw [hPb] at h1
    have h2 : AddictivePlatforms.Compete.payoff (uOf vX) CX p0 (σ p0) = 0 := by
      have : σ p0 = ((∅, (σ p0).2) : AddictivePlatforms.Compete.Choice 2) := by
        rw [← hJ]
      rw [this, payoff_empty2]
    linarith
  · set a := (σ p0).2 with ha
    have hσ : σ p0 = ((Finset.univ, a) : AddictivePlatforms.Compete.Choice 2) := by
      rw [← hJ]
    have hfa := hR.1.1
    rw [hσ] at hfa
    have ha0 : 0 ≤ a 0 := hfa.1 0 (Finset.mem_univ _)
    have ha1 : 0 ≤ a 1 := hfa.1 1 (Finset.mem_univ _)
    have hge := hRopt _ ⟨feasible_top Finset.univ b (by
      intro k _; fin_cases k <;> simp [hb, hb10]), Or.inr rfl⟩
    rw [hPb, hσ] at hge
    have hle := htan a ha0 ha1
    have ha00 : a 0 = 0 := by linarith
    have ha11 : a 1 = b1 := by
      by_contra hne
      -- strict tangent bound
      have hP := hge
      rw [payoff_univ2, hp00, hp01] at hP
      have t1 := exp_tangent (0 - a 0) 0
      have t2 := exp_tangent_strict (y0 - a 1) (y0 - b1) (by intro h; apply hne; linarith)
      have t3 := exp_tangent (a 0 + a 1) b1
      rw [Real.exp_zero] at t1
      rw [hyb] at t2
      rw [hb1e] at t3
      nlinarith
    rw [jointProfit2, hσ, hp00, hp01]
    simp only [Finset.mem_univ, if_true]
    rw [ha00, ha11]
    ring_nf
    nlinarith

/-- At a symmetric profile the joint profit is at most `log 3`. -/
theorem sym_profit (κ : ℝ) (hκ : 0 ≤ κ) (σ : AddictivePlatforms.Compete.ConsumerStrategy 2)
    (x : ℝ) (hx : 0 ≤ x)
    (hR : RestrictedOpt (uOf vX) CX ⊤ (fun _ => x) (σ (fun _ => x))) :
    jointProfit γX κ (fun _ => x) (σ (fun _ => x)) ≤ Real.log 3 := by
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hRopt := hR.2
  rcases hR.1.2 with hJ | hJ
  · have hσ : σ (fun _ => x) = ((∅, (σ (fun _ => x)).2) : AddictivePlatforms.Compete.Choice 2) := by
      rw [← hJ]
    rw [jointProfit2, hσ]
    simp only [Finset.notMem_empty, if_false]
    nlinarith [sq_nonneg x]
  · set a := (σ (fun _ => x)).2 with ha
    have hσ : σ (fun _ => x) = ((Finset.univ, a) : AddictivePlatforms.Compete.Choice 2) := by
      rw [← hJ]
    have hfa := hR.1.1
    rw [hσ] at hfa
    have ha0 : 0 ≤ a 0 := hfa.1 0 (Finset.mem_univ _)
    have ha1 : 0 ≤ a 1 := hfa.1 1 (Finset.mem_univ _)
    set A := (2 * x + 2 * Real.log 2) / 3 with hA
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hA0 : 0 ≤ A / 2 := by positivity
    set E := Real.exp A with hE
    have hxA : x - A / 2 = A - Real.log 2 := by rw [hA]; ring
    have hexA : Real.exp (x - A / 2) = E / 2 := by
      rw [hxA, Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    set astar : Fin 2 → ℝ := fun _ => A / 2 with hastar
    have hPstar : AddictivePlatforms.Compete.payoff (uOf vX) CX (fun _ => x)
        ((Finset.univ, astar) : AddictivePlatforms.Compete.Choice 2) = 9/2 - 3/2 * E := by
      rw [payoff_univ2]
      simp only [hastar]
      rw [hexA, show A / 2 + A / 2 = A by ring]
      ring
    have hge := hRopt _ ⟨feasible_top Finset.univ astar (fun k _ => hA0), Or.inr rfl⟩
    rw [hPstar, hσ] at hge
    have hnn := hRopt _ ⟨feasible_top ∅ a (fun k hk => absurd hk (Finset.notMem_empty k)), Or.inl rfl⟩
    rw [payoff_empty2, hσ] at hnn
    have hP := hge
    rw [payoff_univ2] at hP hnn
    have t3 := exp_tangent (a 0 + a 1) A
    rw [← hE] at t3
    have hEpos : 0 < E := Real.exp_pos A
    -- equality case: `a = astar`
    have hk : ∀ k : Fin 2, a k = A / 2 := by
      intro k
      by_contra hne
      have hs : x - a k ≠ x - A / 2 := by intro h; apply hne; linarith
      have tk := exp_tangent_strict (x - a k) (x - A / 2) hs
      have t0 := exp_tangent (x - a 0) (x - A / 2)
      have t1 := exp_tangent (x - a 1) (x - A / 2)
      rw [hexA] at tk t0 t1
      fin_cases k
      · simp only [Fin.zero_eta] at tk; nlinarith
      · simp only [Fin.mk_one] at tk; nlinarith
    have hS : a 0 + a 1 = A := by rw [hk 0, hk 1]; ring
    have hE3 : E ≤ 3 := by
      have t0 := exp_tangent (x - a 0) (x - A / 2)
      have t1 := exp_tangent (x - a 1) (x - A / 2)
      rw [hexA] at t0 t1
      nlinarith
    have hAle : A ≤ Real.log 3 := by
      rw [← Real.exp_le_exp, Real.exp_log (by norm_num : (0:ℝ) < 3)]; exact hE3
    rw [jointProfit2, hσ]
    simp only [Finset.mem_univ, if_true]
    nlinarith [sq_nonneg x]

noncomputable def ADX : ℝ → ℝ := fun D => (D + 2 * Real.log 2) / 3

theorem isAD_X : IsAD CX gX 2 ADX := by
  intro D hD
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : 0 ≤ ADX D := by simp only [ADX]; positivity
  refine ⟨h0, ?_⟩
  rw [Cderiv_CX _ h0]
  simp only [gX]
  rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
  simp only [ADX]
  push_cast
  ring

/-- No symmetric profile is a joint-profit maximizing outcome at `κ = 1/1000`, `Ā = ∞`. -/
theorem no_sym_JPM (x : ℝ) (σ : AddictivePlatforms.Compete.ConsumerStrategy 2) :
    ¬ IsJPM (uOf vX) CX γX (1/1000) ⊤ (fun _ : Fin 2 => x) σ := by
  intro h
  have hx : 0 ≤ x := h.1 0
  set p0 : Fin 2 → ℝ := ![0, Real.log (50/9)] with hp0
  have hl50 : 0 ≤ Real.log (50/9) := Real.log_nonneg (by norm_num)
  have hp0nn : ∀ k, 0 ≤ p0 k := by
    intro k; fin_cases k <;> simp [hp0, hl50]
  have hmax := h.2.2.1 p0 hp0nn
  have hL := asym_profit (1/1000) σ p0 (by simp [hp0]) (by simp [hp0]) (h.2.1 p0 hp0nn)
  have hRs := sym_profit (1/1000) (by norm_num) σ x hx (h.2.1 _ (fun _ => hx))
  -- numerics: log(10/3) − log 3 ≥ 1/10 and log(50/9) ≤ 41/9
  have h1 : Real.log (10/3) - Real.log 3 ≥ 1/10 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 10/3/3 by norm_num)
    norm_num at this ⊢
    linarith
  have h2 : Real.log (50/9) ≤ 41/9 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 50/9 by norm_num)
    linarith
  have h3 : Real.log (50/9) ^ 2 ≤ (41/9) ^ 2 := pow_le_pow_left₀ hl50 h2 2
  linarith

end AddictivePlatforms.Costly.D3Counter

open AddictivePlatforms.Costly in
theorem solution : ¬ (∀ (v C γ g : ℝ → ℝ) (K : ℕ) (hK : 2 ≤ K) (hS : Standing v C γ g K)
    (Abar : ℝ≥0∞) (hAbar : 0 < Abar) (κ : ℝ) (hκ : 0 < κ) (AD : ℝ → ℝ) (hAD : IsAD C g K AD),
    ∃ d1J d2J : ℝ,
      IsD1J AD γ κ Abar K d1J ∧ (∀ x : ℝ, IsD1J AD γ κ Abar K x → x = d1J) ∧
      IsD2J (uOf v) C Abar K d2J ∧ (∀ x : ℝ, IsD2J (uOf v) C Abar K x → x = d2J) ∧
      (∃ σ : AddictivePlatforms.Compete.ConsumerStrategy K,
        IsJPM (uOf v) C γ κ Abar (fun _ : Fin K => min d1J d2J) σ) ∧
      ∀ (d : Fin K → ℝ) (σ : AddictivePlatforms.Compete.ConsumerStrategy K), IsJPM (uOf v) C γ κ Abar d σ →
        ∀ k, d k = min d1J d2J) := by
  intro H
  obtain ⟨d1J, d2J, -, -, -, -, ⟨σ, hσ⟩, -⟩ :=
    H D3Counter.vX D3Counter.CX D3Counter.γX D3Counter.gX 2 le_rfl (D3Counter.standing_X 2) ⊤
      (by simp) (1/1000) (by norm_num) D3Counter.ADX D3Counter.isAD_X
  exact D3Counter.no_sym_JPM _ σ hσ
