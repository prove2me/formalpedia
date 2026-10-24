-- Prove2me | solution 1 for AtaBarjesteh23.Workload.lemma_4_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T20:19:25.124993+00:00
-- url     : https://prove2.me/submissions/4372c183-ffec-47c5-9384-177792f38cf8

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting
import Definitions.Def_AtaBarjesteh23_Workload_DriftBM
import Definitions.Def_AtaBarjesteh23_Workload_Control
import Theorems.Thm_AtaBarjesteh23_Workload_riccati_wellposed
import Theorems.Thm_AtaBarjesteh23_Workload_lemma_20

open MeasureTheory Set Filter Topology

theorem AtaB_basic (M : AtaBarjesteh23.Workload.Model) (hM : M.Standing) :
    0 < M.hStar ∧ 0 < M.bStar ∧ 0 < M.kappa ∧ 0 < M.a ∧ 0 ≤ M.μ ∧ 0 < M.σ ∧
    (∀ w, 0 ≤ w → M.hcost w = M.hStar * w) ∧ (∀ w ≤ 0, M.hcost w = -(M.bStar * w)) ∧
    Continuous M.hcost := by
  obtain ⟨hK, hm, hh, hb, hr, hH, hμ, hσ⟩ := hM
  have : Nonempty (Fin M.K) := ⟨⟨0, hK⟩⟩
  have hbs : 0 < M.bStar := by
    obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := fun k : Fin M.K => M.b k / M.m k)
    rw [AtaBarjesteh23.Workload.Model.bStar, ← hk]
    exact div_pos (hb k) (hm k)
  have hhs : 0 < M.hStar := by
    obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := fun k : Fin M.K => M.h k / M.m k)
    rw [AtaBarjesteh23.Workload.Model.hStar, ← hk]
    exact div_pos (hh k) (hm k)
  have hks : 0 < M.kappa := by
    obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := fun k : Fin M.K => M.r k / M.m k)
    rw [AtaBarjesteh23.Workload.Model.kappa, ← hk]
    exact div_pos (hr k) (hm k)
  have hmne : M.m ≠ 0 := by
    intro h
    have := hm ⟨0, hK⟩
    rw [h] at this
    simp at this
  have ha : 0 < M.a := by
    have := hH.inv.dotProduct_mulVec_pos hmne
    simpa [AtaBarjesteh23.Workload.Model.a] using this
  have hhmax : ∀ w, M.hcost w = max (M.hStar * w) (-(M.bStar * w)) := by
    intro w
    unfold AtaBarjesteh23.Workload.Model.hcost
    split_ifs with h
    · rw [max_eq_left]; nlinarith
    · rw [max_eq_right]; push_neg at h; nlinarith
  refine ⟨hhs, hbs, hks, ha, hμ, hσ, ?_, ?_, ?_⟩
  · intro w hw; rw [hhmax, max_eq_left]; nlinarith
  · intro w hw; rw [hhmax, max_eq_right]; nlinarith
  · have : M.hcost = fun w => max (M.hStar * w) (-(M.bStar * w)) := funext hhmax
    rw [this]; fun_prop

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

/-- Reflection `s ↦ u - s` maps derivatives within `[0, u]` to derivatives within `[0, u]`. -/
theorem AtaB_reflect {u : ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ}
    (hf : ∀ w ∈ Icc 0 u, HasDerivWithinAt f (f' w) (Icc 0 u) w) :
    ∀ s ∈ Icc 0 u, HasDerivWithinAt (fun s => f (u - s)) (-f' (u - s)) (Icc 0 u) s := by
  intro s hs
  have hmaps : MapsTo (fun s => u - s) (Icc 0 u) (Icc 0 u) := by
    intro x hx; simp only [mem_Icc] at hx ⊢; constructor <;> linarith [hx.1, hx.2]
  have h := (hf (u - s) (hmaps hs)).comp s ((hasDerivAt_id s).const_sub u).hasDerivWithinAt hmaps
  exact h.congr_deriv (by ring)

open AtaBarjesteh23.Workload

theorem AtaB_vPlus_solves (M : Model) {γ : ℝ} (hγ : γ ∈ M.GammaPlus) :
    M.SolvesPlus γ (M.vPlus γ) := Classical.epsilon_spec hγ.2

theorem AtaB_plus_refl (M : Model) (hM : M.Standing) {u : ℝ} (hu : 0 ≤ u) (v : ℝ → ℝ)
    (hv : ∀ w ∈ Icc 0 u, HasDerivWithinAt v (M.rhsUpper u w (v w)) (Icc 0 u) w) :
    ∀ s ∈ Icc 0 u, HasDerivWithinAt (fun s => v (u - s))
      (-(M.a / (2 * M.σ ^ 2)) * v (u - s) ^ 2 + 2 * M.μ / M.σ ^ 2 * v (u - s)
        - 2 * M.hStar / M.σ ^ 2 * s) (Icc 0 u) s := by
  obtain ⟨-, -, -, -, -, -, hhpos, -, -⟩ := AtaB_basic M hM
  intro s hs
  refine (AtaB_reflect hv s hs).congr_deriv ?_
  simp only [Model.rhsUpper]
  rw [hhpos u hu, hhpos (u - s) (by linarith [hs.2])]
  ring

theorem AtaB_plus_unrefl (M : Model) (hM : M.Standing) {u : ℝ} (hu : 0 ≤ u) (U : ℝ → ℝ)
    (hU : ∀ s ∈ Icc 0 u, HasDerivWithinAt U
      (-(M.a / (2 * M.σ ^ 2)) * U s ^ 2 + 2 * M.μ / M.σ ^ 2 * U s
        - 2 * M.hStar / M.σ ^ 2 * s) (Icc 0 u) s) :
    ∀ w ∈ Icc 0 u, HasDerivWithinAt (fun w => U (u - w)) (M.rhsUpper u w (U (u - w)))
      (Icc 0 u) w := by
  obtain ⟨-, -, -, -, -, -, hhpos, -, -⟩ := AtaB_basic M hM
  intro w hw
  refine (AtaB_reflect hU w hw).congr_deriv ?_
  simp only [Model.rhsUpper]
  rw [hhpos u hu, hhpos w hw.1]
  ring

theorem AtaB_plus_shift (M : Model) (hM : M.Standing) {γ γ2 : ℝ} (hγ : γ ∈ M.GammaPlus)
    (hγ2 : γ2 ∈ M.GammaPlus) (hle : γ ≤ γ2) :
    M.vPlus γ 0 = M.vPlus γ2 (M.ugam γ2 - M.ugam γ) := by
  obtain ⟨hhs, -, -, -, -, -, hhpos, -, -⟩ := AtaB_basic M hM
  obtain ⟨-, huniq, -⟩ := riccati_wellposed M hM
  obtain ⟨hvc, hvu, hvd⟩ := AtaB_vPlus_solves M hγ2
  set u2 := M.ugam γ2
  set u := M.ugam γ
  have hu2 : u ≤ u2 := div_le_div_of_nonneg_right hle hhs.le
  have hu : 0 ≤ u := div_nonneg hγ.1 hhs.le
  set d := u2 - u
  have hmaps : MapsTo (fun w => w + d) (Icc 0 u) (Icc 0 u2) := by
    intro w hw; simp only [d, mem_Icc] at hw ⊢; constructor <;> linarith [hw.1, hw.2]
  have hsol : M.SolvesPlus γ (fun w => M.vPlus γ2 (w + d)) := by
    refine ⟨hvc.comp (continuousOn_id.add continuousOn_const) hmaps, ?_, ?_⟩
    · show M.vPlus γ2 (u + d) = 0
      have : u + d = u2 := by simp only [d]; ring
      rw [this, hvu]
    · intro w hw
      have hw' := hmaps hw
      have h := (hvd (w + d) hw').comp w ((hasDerivAt_id w).add_const d).hasDerivWithinAt hmaps
      refine h.congr_deriv ?_
      simp only [mul_one, Model.rhsUpper]
      rw [hhpos u2 (hu.trans hu2), hhpos _ hw'.1, hhpos u hu, hhpos w hw.1]
      simp only [d]
      ring
  have := huniq γ hγ.1 _ _ (AtaB_vPlus_solves M hγ) hsol ⟨le_rfl, hu⟩
  simpa using this

/-- Reflected upper solution is strictly decreasing. -/
theorem AtaB_plus_anti (M : Model) (hM : M.Standing) {γ2 : ℝ} (hγ2 : γ2 ∈ M.GammaPlus)
    (hpos : 0 < M.ugam γ2) :
    StrictAntiOn (fun s => M.vPlus γ2 (M.ugam γ2 - s)) (Icc 0 (M.ugam γ2)) := by
  obtain ⟨hvc, hvu, hvd⟩ := AtaB_vPlus_solves M hγ2
  set u2 := M.ugam γ2
  have hR := AtaB_plus_refl M hM hpos.le _ hvd
  have hU0 : (fun s => M.vPlus γ2 (u2 - s)) 0 = 0 := by simp [hvu]
  have h20 := lemma_20 M hM u2 hpos _ hU0 hR
  have hmaps : MapsTo (fun s => u2 - s) (Icc 0 u2) (Icc 0 u2) := by
    intro x hx; simp only [mem_Icc] at hx ⊢; constructor <;> linarith [hx.1, hx.2]
  have hcont : ContinuousOn (fun s => M.vPlus γ2 (u2 - s)) (Icc 0 u2) :=
    hvc.comp (continuousOn_const.sub continuousOn_id) hmaps
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 u2) hcont
    (f' := fun s => derivWithin (fun s => M.vPlus γ2 (u2 - s)) (Icc 0 u2) s) ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx ⊢
    have hxI : x ∈ Icc 0 u2 := Ioo_subset_Icc_self hx
    rw [(hR x hxI).derivWithin (uniqueDiffOn_Icc hpos x hxI)]
    exact (hR x hxI).mono Ioo_subset_Icc_self
  · intro x hx
    rw [interior_Icc] at hx
    exact (h20 x ⟨hx.1, hx.2.le⟩).2

theorem AtaB_plus_value (M : Model) (hM : M.Standing) {γ γ2 : ℝ} (hγ : γ ∈ M.GammaPlus)
    (hγ2 : γ2 ∈ M.GammaPlus) (hle : γ ≤ γ2) :
    M.vPlus γ 0 = (fun s => M.vPlus γ2 (M.ugam γ2 - s)) (M.ugam γ) :=
  AtaB_plus_shift M hM hγ hγ2 hle

theorem AtaB_plus_cont (M : Model) (hM : M.Standing) :
    ContinuousOn (fun γ => M.vPlus γ 0) M.GammaPlus := by
  obtain ⟨hhs, -⟩ := AtaB_basic M hM
  intro γ hγ
  -- pick `γ2 ∈ Γ⁺` with `γ ≤ γ2` and either `γ < γ2` or `Γ⁺ ⊆ Iic γ`
  have key : ∀ γ2 ∈ M.GammaPlus, γ ≤ γ2 →
      ContinuousWithinAt (fun γ => M.vPlus γ 0) (M.GammaPlus ∩ Iic γ2) γ := by
    intro γ2 hγ2 hle
    obtain ⟨hvc, -, -⟩ := AtaB_vPlus_solves M hγ2
    set u2 := M.ugam γ2
    have hg : ContinuousWithinAt (fun γ' => M.vPlus γ2 (u2 - M.ugam γ'))
        (M.GammaPlus ∩ Iic γ2) γ := by
      have hmaps : MapsTo (fun γ' => u2 - M.ugam γ') (M.GammaPlus ∩ Iic γ2) (Icc 0 u2) := by
        intro x hx
        have h1 : M.ugam x ≤ u2 := div_le_div_of_nonneg_right hx.2 hhs.le
        have h2 : 0 ≤ M.ugam x := div_nonneg hx.1.1 hhs.le
        exact ⟨by linarith, by linarith⟩
      refine (hvc.comp ?_ hmaps) γ ⟨hγ, hle⟩
      exact (continuousOn_const.sub (continuousOn_id.div_const _))
    refine hg.congr (fun x hx => AtaB_plus_shift M hM hx.1 hγ2 hx.2)
      (AtaB_plus_shift M hM hγ hγ2 hle)
  by_cases h : ∃ γ2 ∈ M.GammaPlus, γ < γ2
  · obtain ⟨γ2, hγ2, hlt⟩ := h
    have := key γ2 hγ2 hlt.le
    exact (continuousWithinAt_inter (Iic_mem_nhds hlt)).mp this
  · push_neg at h
    have := key γ hγ le_rfl
    have hs : M.GammaPlus ∩ Iic γ = M.GammaPlus :=
      inter_eq_left.mpr (fun x hx => h x hx)
    rwa [hs] at this

theorem AtaB_plus_strictAnti (M : Model) (hM : M.Standing) :
    StrictAntiOn (fun γ => M.vPlus γ 0) M.GammaPlus := by
  obtain ⟨hhs, -⟩ := AtaB_basic M hM
  intro γ1 h1 γ2 h2 hlt
  have hu1 : 0 ≤ M.ugam γ1 := div_nonneg h1.1 hhs.le
  have hu12 : M.ugam γ1 < M.ugam γ2 := div_lt_div_of_pos_right hlt hhs
  have hanti := AtaB_plus_anti M hM h2 (hu1.trans_lt hu12)
  show M.vPlus γ2 0 < M.vPlus γ1 0
  rw [AtaB_plus_value M hM h1 h2 hlt.le]
  have := hanti ⟨hu1, hu12.le⟩ ⟨hu1.trans hu12.le, le_rfl⟩ hu12
  simpa using this

set_option maxHeartbeats 1000000 in
theorem AtaB_plus_unbdd (M : Model) (hM : M.Standing) :
    ¬ BddBelow ((fun γ => M.vPlus γ 0) '' M.GammaPlus) := by
  obtain ⟨hhs, hbs, hks, ha, hμ, hσ, hhpos, hhneg, hhcont⟩ := AtaB_basic M hM
  obtain ⟨-, huniq, -, -, -, -⟩ := riccati_wellposed M hM
  rintro ⟨B0, hB0⟩
  set D := |B0| + 1 with hDdef
  have hD : 0 < D := by positivity
  have hkD : ∀ γ ∈ M.GammaPlus, -D < M.vPlus γ 0 := fun γ hγ => by
    have h1 : B0 ≤ M.vPlus γ 0 := hB0 ⟨γ, hγ, rfl⟩
    have h2 := neg_abs_le B0
    linarith
  set c1 := M.a / (2 * M.σ ^ 2) with hc1d
  set c2 := 2 * M.μ / M.σ ^ 2 with hc2d
  set c4 := 2 * M.hStar / M.σ ^ 2 with hc4d
  have hc1 : 0 ≤ c1 := by positivity
  have hc2 : 0 ≤ c2 := by positivity
  have hc4 : 0 < c4 := by positivity
  set T := 2 * (D + 1) / c4 + 1 with hTd
  have hT : 1 ≤ T := by
    have : 0 ≤ 2 * (D + 1) / c4 := by positivity
    linarith
  have hT0 : 0 < T := by linarith
  have hTbig : D + 1 ≤ c4 * T ^ 2 / 2 := by
    have e : c4 * (2 * (D + 1) / c4) = 2 * (D + 1) := by field_simp
    nlinarith
  set p : ℝ → ℝ := fun y => max (-(D + 1)) (min y 0) with hp
  have hpmem : ∀ y, -(D + 1) ≤ p y ∧ p y ≤ 0 := fun y =>
    ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hplip : LipschitzWith 1 p := (LipschitzWith.id.min_const 0).const_max (-(D + 1))
  set F : ℝ → ℝ → ℝ := fun s y => -c1 * p y ^ 2 + c2 * p y - c4 * s with hF
  set Lr := c1 * (D + 1) ^ 2 + c2 * (D + 1) + c4 * T with hLr
  have hLr0 : 0 ≤ Lr := by positivity
  have hFbd : ∀ s ∈ Icc 0 T, ∀ y, |F s y| ≤ Lr := by
    intro s hs y
    obtain ⟨h1, h2⟩ := hpmem y
    have q1 : p y ^ 2 ≤ (D + 1) ^ 2 := by nlinarith
    have q2 : c1 * p y ^ 2 ≤ c1 * (D + 1) ^ 2 := mul_le_mul_of_nonneg_left q1 hc1
    have q3 : 0 ≤ c1 * p y ^ 2 := mul_nonneg hc1 (sq_nonneg _)
    have q4 : c2 * p y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc2 h2
    have q5 : -(c2 * (D + 1)) ≤ c2 * p y := by nlinarith
    have q6 : c4 * s ≤ c4 * T := mul_le_mul_of_nonneg_left hs.2 hc4.le
    have q7 : 0 ≤ c4 * s := mul_nonneg hc4.le hs.1
    simp only [F]
    rw [abs_le]
    constructor <;> nlinarith
  set L : NNReal := ⟨Lr, hLr0⟩
  set A : NNReal := ⟨Lr * T, by positivity⟩
  set Kq := Real.toNNReal (2 * |-c1| * (D + 1) + |c2|)
  have hPL : IsPicardLindelof F (tmin := 0) (tmax := T) ⟨0, le_rfl, hT0.le⟩ 0
      A 0 L (Kq * 1) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s _
      have hq := AtaB_lip_quad (-c1) c2 (-c4 * s) (D + 1) (by linarith)
      have := hq.comp (hplip.lipschitzOnWith (s := Metric.closedBall 0 A)) (by
        intro y _
        rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le]
        obtain ⟨h1, h2⟩ := hpmem y
        constructor <;> linarith)
      convert this using 1
      funext y
      simp only [F, Function.comp]
      ring
    · intro x _
      simp only [F]
      fun_prop
    · intro s hs x _
      rw [Real.norm_eq_abs]
      exact hFbd s hs x
    · simp only [L, A, sub_zero, NNReal.coe_zero]
      rw [max_eq_left (by linarith)]
      exact le_rfl
  obtain ⟨U, hU0, hUd⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hUc : ContinuousOn U (Icc 0 T) := fun t ht => (hUd t ht).continuousWithinAt
  have hUd' : ∀ x ∈ Ico 0 T, HasDerivWithinAt U (F x (U x)) (Ici x) x := fun x hx =>
    (hUd x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)
  -- `U ≤ 0`
  have hup : ∀ s ∈ Icc 0 T, U s ≤ 0 := by
    have key : ∀ ε > 0, ∀ s ∈ Icc 0 T, U s ≤ 0 + ε * (1 + s) := by
      intro ε hε
      refine image_le_of_deriv_right_lt_deriv_boundary' (f' := fun x => F x (U x))
        (B := fun s => 0 + ε * (1 + s)) (B' := fun _ => ε) hUc hUd' ?_ (by fun_prop) ?_ ?_
      · show U 0 ≤ _; rw [hU0]; nlinarith
      · intro x _
        have := (((hasDerivWithinAt_id x (Ici x)).const_add 1).const_mul ε).const_add 0
        exact this.congr_deriv (mul_one ε)
      · intro x hx hxe
        have hxe' : U x = 0 + ε * (1 + x) := hxe
        have hpos : 0 < ε * (1 + x) := mul_pos hε (by linarith [hx.1])
        have hpx : p (U x) = 0 := by
          simp only [p]
          rw [min_eq_right (by linarith), max_eq_right (by linarith)]
        show F x (U x) < ε
        simp only [F, hpx]
        have : 0 ≤ c4 * x := mul_nonneg hc4.le hx.1
        nlinarith
    intro s hs
    have := AtaB_le_of_eps (U s) 0 (1 + s) (by linarith [hs.1]) (fun ε hε => key ε hε s hs)
    exact this
  by_cases hS : ∃ s ∈ Icc 0 T, U s ≤ -D
  · set S := Icc 0 T ∩ U ⁻¹' Iic (-D) with hSd
    have hSc : IsClosed S := hUc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    obtain ⟨s0, hs0, hs0D⟩ := hS
    have hSne : S.Nonempty := ⟨s0, hs0, hs0D⟩
    have hSbdd : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
    set s1 := sInf S with hs1d
    have hs1 : s1 ∈ S := hSc.csInf_mem hSne hSbdd
    have hs1T : s1 ≤ T := hs1.1.2
    have hs1pos : 0 < s1 := by
      rcases hs1.1.1.lt_or_eq with h | h
      · exact h
      · exfalso
        have h2 : U s1 ≤ -D := hs1.2
        rw [← h, hU0] at h2
        linarith
    have hbefore : ∀ s ∈ Ico 0 s1, -D < U s := by
      intro s hs
      by_contra h
      push_neg at h
      have : s1 ≤ s := csInf_le hSbdd ⟨⟨hs.1, hs.2.le.trans hs1T⟩, h⟩
      linarith [hs.2]
    have hlow : ∀ s ∈ Icc 0 s1, -D ≤ U s := by
      have hcl : IsClosed (Icc 0 s1 ∩ U ⁻¹' Ici (-D)) :=
        (hUc.mono (Icc_subset_Icc_right hs1T)).preimage_isClosed_of_isClosed isClosed_Icc
          isClosed_Ici
      have hsub : Ico 0 s1 ⊆ Icc 0 s1 ∩ U ⁻¹' Ici (-D) := fun s hs =>
        ⟨Ico_subset_Icc_self hs, (hbefore s hs).le⟩
      have := closure_minimal hsub hcl
      rw [closure_Ico hs1pos.ne] at this
      exact fun s hs => (this hs).2
    have hpU : ∀ s ∈ Icc 0 s1, p (U s) = U s := by
      intro s hs
      simp only [p]
      rw [min_eq_left (hup s ⟨hs.1, hs.2.trans hs1T⟩), max_eq_right (by linarith [hlow s hs])]
    have hU20 : ∀ s ∈ Icc 0 s1, HasDerivWithinAt U
        (-(M.a / (2 * M.σ ^ 2)) * U s ^ 2 + 2 * M.μ / M.σ ^ 2 * U s
          - 2 * M.hStar / M.σ ^ 2 * s) (Icc 0 s1) s := by
      intro s hs
      have := (hUd s ⟨hs.1, hs.2.trans hs1T⟩).mono (Icc_subset_Icc_right hs1T)
      simp only [F, hpU s hs] at this
      exact this
    set γ := M.hStar * s1 with hγd
    have hug : M.ugam γ = s1 := by
      simp only [Model.ugam, γ]
      field_simp
    have hmaps : MapsTo (fun w => s1 - w) (Icc 0 s1) (Icc 0 s1) := by
      intro x hx; simp only [mem_Icc] at hx ⊢; constructor <;> linarith [hx.1, hx.2]
    have hsol : M.SolvesPlus γ (fun w => U (s1 - w)) := by
      unfold Model.SolvesPlus
      rw [hug]
      refine ⟨(hUc.mono (Icc_subset_Icc_right hs1T)).comp
        (continuousOn_const.sub continuousOn_id) hmaps, by simp [hU0], ?_⟩
      exact AtaB_plus_unrefl M hM hs1pos.le U hU20
    have hγ : γ ∈ M.GammaPlus := ⟨by positivity, _, hsol⟩
    have heq := huniq γ hγ.1 _ _ (AtaB_vPlus_solves M hγ) hsol
      ⟨le_rfl, by rw [hug]; exact hs1pos.le⟩
    have h1 := hkD γ hγ
    rw [heq] at h1
    simp only [sub_zero] at h1
    have h2 : U s1 ≤ -D := hs1.2
    linarith
  · push_neg at hS
    have hpU : ∀ s ∈ Icc 0 T, p (U s) = U s := by
      intro s hs
      simp only [p]
      rw [min_eq_left (hup s hs), max_eq_right (by linarith [hS s hs])]
    have hanti : AntitoneOn (fun s => U s + c4 * s ^ 2 / 2) (Icc 0 T) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
        (hUc.add (by fun_prop)) (f' := fun s => F s (U s) + c4 * s) ?_ ?_
      · intro x hx
        rw [interior_Icc] at hx ⊢
        have h1 := (hUd x (Ioo_subset_Icc_self hx)).mono Ioo_subset_Icc_self
        have h2 : HasDerivAt (fun s => c4 * s ^ 2 / 2) (c4 * x) x :=
          (((hasDerivAt_pow 2 x).const_mul c4).div_const 2).congr_deriv (by push_cast; ring)
        exact h1.add h2.hasDerivWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hxI : x ∈ Icc 0 T := Ioo_subset_Icc_self hx
        simp only [F, hpU x hxI]
        have := hup x hxI
        nlinarith [mul_nonneg hc1 (sq_nonneg (U x)), mul_nonpos_of_nonneg_of_nonpos hc2 this]
    have := hanti ⟨le_rfl, hT0.le⟩ ⟨hT0.le, le_rfl⟩ hT0.le
    simp only [hU0] at this
    have h3 := hS T ⟨hT0.le, le_rfl⟩
    nlinarith

theorem solution (M : Model) (hM : M.Standing) :
    ContinuousOn (fun γ => M.vPlus γ 0) M.GammaPlus ∧
    StrictAntiOn (fun γ => M.vPlus γ 0) M.GammaPlus ∧
    M.vPlus 0 0 = 0 ∧
    ¬ BddBelow ((fun γ => M.vPlus γ 0) '' M.GammaPlus) := by
  refine ⟨AtaB_plus_cont M hM, AtaB_plus_strictAnti M hM, ?_, AtaB_plus_unbdd M hM⟩
  have h0 := (riccati_wellposed M hM).2.2.2.1
  obtain ⟨-, hu, -⟩ := AtaB_vPlus_solves M h0
  simpa [Model.ugam] using hu
