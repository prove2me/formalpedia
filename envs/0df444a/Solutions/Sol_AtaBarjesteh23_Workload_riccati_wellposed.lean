-- Prove2me | solution 1 for AtaBarjesteh23.Workload.riccati_wellposed
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T20:13:32.49786+00:00
-- url     : https://prove2.me/submissions/f8495feb-7606-4898-a7c8-296dd5a84e3f

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting
import Definitions.Def_AtaBarjesteh23_Workload_DriftBM
import Definitions.Def_AtaBarjesteh23_Workload_Control

open MeasureTheory Set Filter Topology

theorem AtaB_lip_quad (c1 c2 d R : ℝ) (hR : 0 ≤ R) :
    LipschitzOnWith (Real.toNNReal (2 * |c1| * R + |c2|)) (fun y => c1 * y ^ 2 + c2 * y + d)
      (Metric.closedBall 0 R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hx hy
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  have : c1 * x ^ 2 + c2 * x + d - (c1 * y ^ 2 + c2 * y + d) = (c1 * (x + y) + c2) * (x - y) := by
    ring
  rw [this, abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  calc |c1 * (x + y) + c2| ≤ |c1 * (x + y)| + |c2| := abs_add_le _ _
    _ = |c1| * |x + y| + |c2| := by rw [abs_mul]
    _ ≤ |c1| * (|x| + |y|) + |c2| := by gcongr; exact abs_add_le _ _
    _ ≤ 2 * |c1| * R + |c2| := by nlinarith [abs_nonneg c1]

theorem AtaB_le_of_eps (a b c : ℝ) (hc : 0 < c) (h : ∀ ε > 0, a ≤ b + ε * c) : a ≤ b := by
  by_contra hab
  push_neg at hab
  have := h ((a - b) / (2 * c)) (div_pos (sub_pos.mpr hab) (by positivity))
  have e : (a - b) / (2 * c) * c = (a - b) / 2 := by field_simp
  rw [e] at this
  linarith

set_option maxHeartbeats 1000000 in
open AtaBarjesteh23.Workload in
theorem solution (M : Model) (hM : M.Standing) :
    (∀ γ, 0 ≤ γ → ∀ v₁ v₂ : ℝ → ℝ, M.SolvesMinus γ v₁ → M.SolvesMinus γ v₂ →
      EqOn v₁ v₂ (Icc (M.lgam γ) 0)) ∧
    (∀ γ, 0 ≤ γ → ∀ v₁ v₂ : ℝ → ℝ, M.SolvesPlus γ v₁ → M.SolvesPlus γ v₂ →
      EqOn v₁ v₂ (Icc 0 (M.ugam γ))) ∧
    (0 : ℝ) ∈ M.GammaMinus ∧ (0 : ℝ) ∈ M.GammaPlus ∧
    M.GammaMinus.OrdConnected ∧ M.GammaPlus.OrdConnected := by
  obtain ⟨hK, hm, hh, hb, hr, hH, hμ, hσ⟩ := hM
  have : Nonempty (Fin M.K) := ⟨⟨0, hK⟩⟩
  have hbs : 0 < M.bStar := by
    obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := fun k : Fin M.K => M.b k / M.m k)
    rw [Model.bStar, ← hk]
    exact div_pos (hb k) (hm k)
  have hhs : 0 < M.hStar := by
    obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := fun k : Fin M.K => M.h k / M.m k)
    rw [Model.hStar, ← hk]
    exact div_pos (hh k) (hm k)
  have hks : 0 < M.kappa := by
    obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := fun k : Fin M.K => M.r k / M.m k)
    rw [Model.kappa, ← hk]
    exact div_pos (hr k) (hm k)
  have hmne : M.m ≠ 0 := by
    intro h
    have := hm ⟨0, hK⟩
    rw [h] at this
    simp at this
  have ha : 0 < M.a := by
    have := hH.inv.dotProduct_mulVec_pos hmne
    simpa [Model.a] using this
  have hhmax : ∀ w, M.hcost w = max (M.hStar * w) (-(M.bStar * w)) := by
    intro w
    unfold Model.hcost
    split_ifs with h
    · rw [max_eq_left]; nlinarith
    · rw [max_eq_right]; push_neg at h; nlinarith
  have hhcont : Continuous M.hcost := by
    have : M.hcost = fun w => max (M.hStar * w) (-(M.bStar * w)) := funext hhmax
    rw [this]; fun_prop
  have hhneg : ∀ w ≤ 0, M.hcost w = -(M.bStar * w) := by
    intro w hw
    rw [hhmax, max_eq_right]; nlinarith
  have hhpos : ∀ w, 0 ≤ w → M.hcost w = M.hStar * w := by
    intro w hw
    rw [hhmax, max_eq_left]; nlinarith
  have hσ2 : 0 < M.σ ^ 2 := by positivity
  have hlgam_nonpos : ∀ γ, 0 ≤ γ → M.lgam γ < 0 := by
    intro γ hγ
    simp only [Model.lgam]
    have : 0 < γ + M.μ * M.kappa + M.a / 4 * M.kappa ^ 2 := by positivity
    have : 0 < 1 / M.bStar := by positivity
    nlinarith
  have hugam_nonneg : ∀ γ, 0 ≤ γ → 0 ≤ M.ugam γ := fun γ hγ => div_nonneg hγ hhs.le
  set c1 := M.a / (2 * M.σ ^ 2) with hc1
  set c2 := 2 * M.μ / M.σ ^ 2 with hc2
  have hc1p : 0 ≤ c1 := by positivity
  have hc2p : 0 ≤ c2 := by positivity
  have hLow : ∀ l t, M.rhsLower l t = fun y => c1 * y ^ 2 + (-c2) * y
      + (-c1 * M.kappa ^ 2 - c2 * M.kappa + 2 * (M.hcost l - M.hcost t) / M.σ ^ 2) := by
    intro l t; funext y; simp only [Model.rhsLower, c1, c2]; ring
  have hUp : ∀ u t, M.rhsUpper u t = fun y => c1 * y ^ 2 + (-c2) * y
      + 2 * (M.hcost u - M.hcost t) / M.σ ^ 2 := by
    intro u t; funext y; simp only [Model.rhsUpper, c1, c2]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- uniqueness for (50)–(51)
    intro γ hγ v₁ v₂ h₁ h₂
    set l := M.lgam γ
    obtain ⟨hc₁, hl₁, hd₁⟩ := h₁
    obtain ⟨hc₂, hl₂, hd₂⟩ := h₂
    obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hc₁
    obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hc₂
    set R := max (max C₁ C₂) 0
    have hR : 0 ≤ R := le_max_right _ _
    refine ODE_solution_unique_of_mem_Icc_right (v := fun t => M.rhsLower l t)
      (s := fun _ => Metric.closedBall 0 R) (K := Real.toNNReal (2 * |c1| * R + |-c2|))
      ?_ hc₁ ?_ ?_ hc₂ ?_ ?_ (by rw [hl₁, hl₂])
    · intro t _
      rw [hLow]
      exact AtaB_lip_quad _ _ _ R hR
    · intro t ht
      exact (hd₁ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
    · intro t ht
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hC₁ t (Ico_subset_Icc_self ht)).trans
        ((le_max_left _ _).trans (le_max_left _ _))
    · intro t ht
      exact (hd₂ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
    · intro t ht
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hC₂ t (Ico_subset_Icc_self ht)).trans
        ((le_max_right _ _).trans (le_max_left _ _))
  · -- uniqueness for (52)–(53)
    intro γ hγ v₁ v₂ h₁ h₂
    set u := M.ugam γ
    obtain ⟨hc₁, hu₁, hd₁⟩ := h₁
    obtain ⟨hc₂, hu₂, hd₂⟩ := h₂
    obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hc₁
    obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hc₂
    set R := max (max C₁ C₂) 0
    have hR : 0 ≤ R := le_max_right _ _
    refine ODE_solution_unique_of_mem_Icc_left (v := fun t => M.rhsUpper u t)
      (s := fun _ => Metric.closedBall 0 R) (K := Real.toNNReal (2 * |c1| * R + |-c2|))
      ?_ hc₁ ?_ ?_ hc₂ ?_ ?_ (by rw [hu₁, hu₂])
    · intro t _
      rw [hUp]
      exact AtaB_lip_quad _ _ _ R hR
    · intro t ht
      exact (hd₁ t (Ioc_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE_of_mem ht)
    · intro t ht
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hC₁ t (Ioc_subset_Icc_self ht)).trans
        ((le_max_left _ _).trans (le_max_left _ _))
    · intro t ht
      exact (hd₂ t (Ioc_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE_of_mem ht)
    · intro t ht
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hC₂ t (Ioc_subset_Icc_self ht)).trans
        ((le_max_right _ _).trans (le_max_left _ _))
  · -- existence of `v⁻_0`: Picard–Lindelöf for the clamped field, then a priori bounds
    set l0 := M.lgam 0 with hl0def
    have hl0 : l0 < 0 := hlgam_nonpos 0 le_rfl
    have hhl0 : M.hcost l0 = M.μ * M.kappa + M.a / 4 * M.kappa ^ 2 := by
      rw [hhneg l0 hl0.le]
      simp only [l0, Model.lgam]
      field_simp
      ring
    set p : ℝ → ℝ := fun y => max (-M.kappa) (min y 0) with hp
    have hpmem : ∀ y, -M.kappa ≤ p y ∧ p y ≤ 0 := fun y =>
      ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
    have hplip : LipschitzWith 1 p := (LipschitzWith.id.min_const 0).const_max (-M.kappa)
    set F : ℝ → ℝ → ℝ := fun t y => M.rhsLower l0 t (p y) with hF
    set Lr := c1 * M.kappa ^ 2 + c2 * M.kappa + 2 * M.hcost l0 / M.σ ^ 2 with hLr
    have hLr0 : 0 ≤ Lr := by
      have := hhcont.continuousOn (s := univ)
      have : 0 ≤ M.hcost l0 := by rw [hhl0]; positivity
      positivity
    have hFbd : ∀ t ∈ Icc l0 0, ∀ y, |F t y| ≤ Lr := by
      intro t ht y
      obtain ⟨hp1, hp2⟩ := hpmem y
      have hht : M.hcost t = -(M.bStar * t) := hhneg t ht.2
      have hhl0' : M.hcost l0 = -(M.bStar * l0) := hhneg l0 hl0.le
      have e1 : 0 ≤ M.hcost l0 - M.hcost t := by rw [hht, hhl0']; nlinarith [ht.1]
      have e2 : M.hcost l0 - M.hcost t ≤ M.hcost l0 := by rw [hht]; nlinarith [ht.2]
      have q1 : p y ^ 2 ≤ M.kappa ^ 2 := by nlinarith
      have q2 : 0 ≤ p y + M.kappa := by linarith
      have q3 : p y + M.kappa ≤ M.kappa := by linarith
      have r1 : 0 ≤ 2 * (M.hcost l0 - M.hcost t) / M.σ ^ 2 := by positivity
      have r2 : 2 * (M.hcost l0 - M.hcost t) / M.σ ^ 2 ≤ 2 * M.hcost l0 / M.σ ^ 2 := by
        gcongr
      simp only [F, Model.rhsLower]
      rw [← hc1, ← hc2, abs_le]
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left q1 hc1p, mul_le_mul_of_nonneg_left q3 hc2p,
          mul_nonneg hc2p q2, sq_nonneg (p y)]
      · nlinarith [mul_le_mul_of_nonneg_left q1 hc1p, mul_nonneg hc2p q2, sq_nonneg (p y),
          mul_nonneg hc1p (sq_nonneg (p y))]
    set L : NNReal := ⟨Lr, hLr0⟩
    set A : NNReal := ⟨Lr * (0 - l0), by nlinarith⟩
    set Kq := Real.toNNReal (2 * |c1| * M.kappa + |-c2|)
    have hPL : IsPicardLindelof F (tmin := l0) (tmax := 0) ⟨l0, le_rfl, hl0.le⟩ (-M.kappa)
        A 0 L (Kq * 1) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro t _
        have hq := AtaB_lip_quad c1 (-c2)
          (-c1 * M.kappa ^ 2 - c2 * M.kappa + 2 * (M.hcost l0 - M.hcost t) / M.σ ^ 2)
          M.kappa hks.le
        have := hq.comp (hplip.lipschitzOnWith (s := Metric.closedBall (-M.kappa) A)) (by
          intro y _
          rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le]
          obtain ⟨h1, h2⟩ := hpmem y
          constructor <;> linarith)
        convert this using 1
        funext y
        simp only [F, Function.comp, hLow]
      · intro x _
        simp only [F, Model.rhsLower]
        exact (by fun_prop : Continuous fun t => _).continuousOn
      · intro t ht x _
        rw [Real.norm_eq_abs]
        exact hFbd t ht x
      · simp only [L, A, NNReal.coe_mk, sub_zero, NNReal.coe_zero]
        rw [max_eq_left (by linarith)]
        exact le_rfl
    obtain ⟨α, hα0, hαd⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    have hαc : ContinuousOn α (Icc l0 0) := fun t ht => (hαd t ht).continuousWithinAt
    have hαd' : ∀ x ∈ Ico l0 0, HasDerivWithinAt α (F x (α x)) (Ici x) x := fun x hx =>
      (hαd x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)
    -- upper bound `α ≤ 0`
    have hup : ∀ x ∈ Icc l0 0, α x ≤ 0 := by
      refine image_le_of_deriv_right_lt_deriv_boundary' (f' := fun x => F x (α x))
        (B := fun _ => 0) (B' := fun _ => 0) hαc hαd' ?_ continuousOn_const
        (fun x _ => hasDerivWithinAt_const _ _ _) ?_
      · rw [hα0]; linarith
      · intro x hx hx0
        have hx0' : α x = 0 := hx0
        show F x (α x) < 0
        rw [hx0']
        have hp0 : p 0 = 0 := by simp [p, hks.le]
        have hval : F x 0 = 2 * M.bStar * x / M.σ ^ 2 := by
          simp only [F, hp0, Model.rhsLower, hhl0]
          rw [hhneg x hx.2.le]
          field_simp
          ring
        rw [hval]
        apply div_neg_of_neg_of_pos _ hσ2
        nlinarith [hx.2]
    -- lower bound `-κ ≤ α`
    have hlow : ∀ x ∈ Icc l0 0, -M.kappa ≤ α x := by
      have key : ∀ ε > 0, ∀ x ∈ Icc l0 0, -α x ≤ M.kappa + ε * (1 + (x - l0)) := by
        intro ε hε
        refine image_le_of_deriv_right_lt_deriv_boundary' (f := fun x => -α x)
          (f' := fun x => -F x (α x)) (B := fun x => M.kappa + ε * (1 + (x - l0)))
          (B' := fun _ => ε) hαc.neg (fun x hx => (hαd' x hx).neg) ?_ (by fun_prop) ?_ ?_
        · show -α l0 ≤ _; rw [hα0]; nlinarith
        · intro x _
          have := (((hasDerivWithinAt_id x (Ici x)).sub_const l0).const_add 1).const_mul ε
            |>.const_add M.kappa
          exact this.congr_deriv (mul_one ε)
        · intro x hx hxe
          have hxe' : -α x = M.kappa + ε * (1 + (x - l0)) := hxe
          have hpos : 0 < ε * (1 + (x - l0)) := mul_pos hε (by linarith [hx.1])
          have hlt : α x < -M.kappa := by linarith
          have hpx : p (α x) = -M.kappa := by
            simp only [p]
            rw [min_eq_left (by linarith), max_eq_left hlt.le]
          have hval : M.rhsLower l0 x (-M.kappa) = 2 * (M.hcost l0 - M.hcost x) / M.σ ^ 2 := by
            simp only [Model.rhsLower]; ring
          show -F x (α x) < ε
          simp only [F, hpx]
          rw [hval, hhneg x hx.2.le, hhneg l0 hl0.le]
          have : 0 ≤ 2 * (-(M.bStar * l0) - -(M.bStar * x)) / M.σ ^ 2 := by
            apply div_nonneg _ hσ2.le; nlinarith [hx.1]
          linarith
      intro x hx
      have hc : 0 < 1 + (x - l0) := by linarith [hx.1]
      have := AtaB_le_of_eps (-α x) M.kappa _ hc (fun ε hε => key ε hε x hx)
      linarith
    have hpα : ∀ x ∈ Icc l0 0, p (α x) = α x := by
      intro x hx
      simp only [p]
      rw [min_eq_left (hup x hx), max_eq_right (hlow x hx)]
    refine ⟨le_rfl, α, hαc, hα0, ?_⟩
    intro w hw
    have := hαd w hw
    simp only [F, hpα w hw] at this
    exact this
  · -- `0 ∈ Γ⁺`: on the degenerate interval `[0, u_0] = {0}` the zero function works
    refine ⟨le_rfl, fun _ => 0, continuousOn_const, rfl, ?_⟩
    intro w hw
    have hu0 : M.ugam 0 = 0 := by simp [Model.ugam]
    rw [hu0] at hw ⊢
    have : w = 0 := le_antisymm hw.2 hw.1
    subst this
    have : M.rhsUpper 0 0 0 = 0 := by simp [Model.rhsUpper]
    rw [this]
    exact hasDerivWithinAt_const _ _ _
  · -- `Γ⁻` is an interval: restrict and translate a solution for a larger `γ`
    refine ⟨fun x hx y hy z hz => ?_⟩
    have hz0 : 0 ≤ z := hx.1.trans hz.1
    refine ⟨hz0, ?_⟩
    obtain ⟨v, hvc, hvl, hvd⟩ := hy.2
    set l2 := M.lgam y
    set l := M.lgam z
    have hl2 : l2 ≤ l := by
      simp only [l2, l, Model.lgam]
      have : 0 < 1 / M.bStar := by positivity
      nlinarith [hz.2]
    have hl : l < 0 := hlgam_nonpos z hz0
    set d := l2 - l
    have hmaps : MapsTo (fun w => w + d) (Icc l 0) (Icc l2 0) := by
      intro w hw; simp only [d, mem_Icc] at hw ⊢; constructor <;> linarith [hw.1, hw.2]
    refine ⟨fun w => v (w + d), ?_, ?_, ?_⟩
    · exact hvc.comp (continuousOn_id.add continuousOn_const) hmaps
    · show v (l + d) = -M.kappa
      have : l + d = l2 := by simp only [d]; ring
      rw [this, hvl]
    · intro w hw
      have hw' := hmaps hw
      have h := (hvd (w + d) hw').comp w ((hasDerivAt_id w).add_const d).hasDerivWithinAt hmaps
      refine h.congr_deriv ?_
      simp only [id, mul_one]
      rw [hLow, hLow]
      simp only
      rw [hhneg l2 (hl2.trans hl.le), hhneg _ hw'.2, hhneg l hl.le, hhneg w hw.2]
      simp only [d]
      ring
  · -- `Γ⁺` is an interval: restrict and translate a solution for a larger `γ`
    refine ⟨fun x hx y hy z hz => ?_⟩
    have hz0 : 0 ≤ z := hx.1.trans hz.1
    refine ⟨hz0, ?_⟩
    obtain ⟨v, hvc, hvu, hvd⟩ := hy.2
    set u2 := M.ugam y
    set u := M.ugam z
    have hu2 : u ≤ u2 := div_le_div_of_nonneg_right hz.2 hhs.le
    have hu : 0 ≤ u := hugam_nonneg z hz0
    set d := u2 - u
    have hmaps : MapsTo (fun w => w + d) (Icc 0 u) (Icc 0 u2) := by
      intro w hw; simp only [d, mem_Icc] at hw ⊢; constructor <;> linarith [hw.1, hw.2]
    refine ⟨fun w => v (w + d), ?_, ?_, ?_⟩
    · exact hvc.comp (continuousOn_id.add continuousOn_const) hmaps
    · show v (u + d) = 0
      have : u + d = u2 := by simp only [d]; ring
      rw [this, hvu]
    · intro w hw
      have hw' := hmaps hw
      have h := (hvd (w + d) hw').comp w ((hasDerivAt_id w).add_const d).hasDerivWithinAt hmaps
      refine h.congr_deriv ?_
      simp only [id, mul_one]
      rw [hUp, hUp]
      simp only
      rw [hhpos u2 (hu.trans hu2), hhpos _ hw'.1, hhpos u hu, hhpos w hw.1]
      simp only [d]
      ring
