-- Prove2me | solution 1 for AtaBarjesteh23.Workload.lemma_4_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T20:34:07.917666+00:00
-- url     : https://prove2.me/submissions/45f894ed-eaf1-43d0-aa1e-94e21a2965ad

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting
import Definitions.Def_AtaBarjesteh23_Workload_DriftBM
import Definitions.Def_AtaBarjesteh23_Workload_Control
import Theorems.Thm_AtaBarjesteh23_Workload_riccati_wellposed
import Theorems.Thm_AtaBarjesteh23_Workload_lemma_19
import Theorems.Thm_AtaBarjesteh23_Workload_corollary_6

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

theorem AtaB_vMinus_solves (M : Model) {γ : ℝ} (hγ : γ ∈ M.GammaMinus) :
    M.SolvesMinus γ (M.vMinus γ) := Classical.epsilon_spec hγ.2

theorem AtaB_lgam_neg (M : Model) (hM : M.Standing) {γ : ℝ} (hγ : 0 ≤ γ) : M.lgam γ < 0 := by
  obtain ⟨hhs, hbs, hks, ha, hμ, -⟩ := AtaB_basic M hM
  simp only [Model.lgam]
  have : 0 < γ + M.μ * M.kappa + M.a / 4 * M.kappa ^ 2 := by positivity
  have : 0 < 1 / M.bStar := by positivity
  nlinarith

theorem AtaB_lgam_anti (M : Model) (hM : M.Standing) {γ γ2 : ℝ} (h : γ ≤ γ2) :
    M.lgam γ2 ≤ M.lgam γ := by
  obtain ⟨-, hbs, -⟩ := AtaB_basic M hM
  simp only [Model.lgam]
  have : 0 < 1 / M.bStar := by positivity
  nlinarith

theorem AtaB_lgam_strictAnti (M : Model) (hM : M.Standing) {γ γ2 : ℝ} (h : γ < γ2) :
    M.lgam γ2 < M.lgam γ := by
  obtain ⟨-, hbs, -⟩ := AtaB_basic M hM
  simp only [Model.lgam]
  have : 0 < 1 / M.bStar := by positivity
  nlinarith

/-- Translating a solution of the lower Riccati equation on `[l, 0]` to `[0, -l]`. -/
theorem AtaB_minus_unshift (M : Model) (hM : M.Standing) {l : ℝ} (hl : l ≤ 0) (v : ℝ → ℝ)
    (hv : ∀ w ∈ Icc l 0, HasDerivWithinAt v (M.rhsLower l w (v w)) (Icc l 0) w) :
    ∀ s ∈ Icc 0 (-l), HasDerivWithinAt (fun s => v (l + s))
      (M.a / (2 * M.σ ^ 2) * (v (l + s) ^ 2 - M.kappa ^ 2)
        - 2 * M.μ / M.σ ^ 2 * (v (l + s) + M.kappa)
        + 2 * M.bStar / M.σ ^ 2 * s) (Icc 0 (-l)) s := by
  obtain ⟨-, -, -, -, -, -, -, hhneg, -⟩ := AtaB_basic M hM
  intro s hs
  have hmaps : MapsTo (fun s => l + s) (Icc 0 (-l)) (Icc l 0) := by
    intro x hx; simp only [mem_Icc] at hx ⊢; constructor <;> linarith [hx.1, hx.2]
  have h := (hv (l + s) (hmaps hs)).comp s ((hasDerivAt_id s).const_add l).hasDerivWithinAt hmaps
  refine h.congr_deriv ?_
  simp only [Model.rhsLower, mul_one]
  rw [hhneg l hl, hhneg (l + s) (by linarith [hs.2])]
  ring

/-- Translating a solution on `[0, -l]` back to `[l, 0]`. -/
theorem AtaB_minus_shift (M : Model) (hM : M.Standing) {l : ℝ} (hl : l ≤ 0) (U : ℝ → ℝ)
    (hU : ∀ s ∈ Icc 0 (-l), HasDerivWithinAt U
      (M.a / (2 * M.σ ^ 2) * (U s ^ 2 - M.kappa ^ 2) - 2 * M.μ / M.σ ^ 2 * (U s + M.kappa)
        + 2 * M.bStar / M.σ ^ 2 * s) (Icc 0 (-l)) s) :
    ∀ w ∈ Icc l 0, HasDerivWithinAt (fun w => U (w - l)) (M.rhsLower l w (U (w - l)))
      (Icc l 0) w := by
  obtain ⟨-, -, -, -, -, -, -, hhneg, -⟩ := AtaB_basic M hM
  intro w hw
  have hmaps : MapsTo (fun w => w - l) (Icc l 0) (Icc 0 (-l)) := by
    intro x hx; simp only [mem_Icc] at hx ⊢; constructor <;> linarith [hx.1, hx.2]
  have h := (hU (w - l) (hmaps hw)).comp w ((hasDerivAt_id w).sub_const l).hasDerivWithinAt hmaps
  refine h.congr_deriv ?_
  simp only [Model.rhsLower, mul_one]
  rw [hhneg l hl, hhneg w hw.2]
  ring

theorem AtaB_minus_shiftid (M : Model) (hM : M.Standing) {γ γ2 : ℝ} (hγ : γ ∈ M.GammaMinus)
    (hγ2 : γ2 ∈ M.GammaMinus) (hle : γ ≤ γ2) :
    M.vMinus γ 0 = M.vMinus γ2 (M.lgam γ2 - M.lgam γ) := by
  obtain ⟨-, -, -, -, -, -, -, hhneg, -⟩ := AtaB_basic M hM
  obtain ⟨huniq, -⟩ := riccati_wellposed M hM
  obtain ⟨hvc, hvl, hvd⟩ := AtaB_vMinus_solves M hγ2
  set l2 := M.lgam γ2
  set l := M.lgam γ
  have hl2 : l2 ≤ l := AtaB_lgam_anti M hM hle
  have hl : l < 0 := AtaB_lgam_neg M hM hγ.1
  set d := l2 - l
  have hmaps : MapsTo (fun w => w + d) (Icc l 0) (Icc l2 0) := by
    intro w hw; simp only [d, mem_Icc] at hw ⊢; constructor <;> linarith [hw.1, hw.2]
  have hsol : M.SolvesMinus γ (fun w => M.vMinus γ2 (w + d)) := by
    refine ⟨hvc.comp (continuousOn_id.add continuousOn_const) hmaps, ?_, ?_⟩
    · show M.vMinus γ2 (l + d) = -M.kappa
      have : l + d = l2 := by simp only [d]; ring
      rw [this, hvl]
    · intro w hw
      have hw' := hmaps hw
      have h := (hvd (w + d) hw').comp w ((hasDerivAt_id w).add_const d).hasDerivWithinAt hmaps
      refine h.congr_deriv ?_
      simp only [mul_one, Model.rhsLower]
      rw [hhneg l2 (hl2.trans hl.le), hhneg _ hw'.2, hhneg l hl.le, hhneg w hw.2]
      simp only [d]
      ring
  have := huniq γ hγ.1 _ _ (AtaB_vMinus_solves M hγ) hsol ⟨hl.le, le_rfl⟩
  simpa using this

/-- The translated lower solution is strictly increasing. -/
theorem AtaB_minus_mono (M : Model) (hM : M.Standing) {γ2 : ℝ} (hγ2 : γ2 ∈ M.GammaMinus) :
    StrictMonoOn (fun s => M.vMinus γ2 (M.lgam γ2 + s)) (Icc 0 (-M.lgam γ2)) := by
  obtain ⟨hvc, hvl, hvd⟩ := AtaB_vMinus_solves M hγ2
  set l2 := M.lgam γ2
  have hl2 : l2 < 0 := AtaB_lgam_neg M hM hγ2.1
  have hpos : 0 < -l2 := by linarith
  have hR := AtaB_minus_unshift M hM hl2.le _ hvd
  have hU0 : (fun s => M.vMinus γ2 (l2 + s)) 0 = -M.kappa := by simp [hvl]
  have h19 := lemma_19 M hM (-l2) hpos _ hU0 hR
  have hmaps : MapsTo (fun s => l2 + s) (Icc 0 (-l2)) (Icc l2 0) := by
    intro x hx; simp only [mem_Icc] at hx ⊢; constructor <;> linarith [hx.1, hx.2]
  have hcont : ContinuousOn (fun s => M.vMinus γ2 (l2 + s)) (Icc 0 (-l2)) :=
    hvc.comp (continuousOn_const.add continuousOn_id) hmaps
  refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 (-l2)) hcont
    (f' := fun s => derivWithin (fun s => M.vMinus γ2 (l2 + s)) (Icc 0 (-l2)) s) ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx ⊢
    have hxI : x ∈ Icc 0 (-l2) := Ioo_subset_Icc_self hx
    rw [(hR x hxI).derivWithin (uniqueDiffOn_Icc hpos x hxI)]
    exact (hR x hxI).mono Ioo_subset_Icc_self
  · intro x hx
    rw [interior_Icc] at hx
    exact h19 x ⟨hx.1, hx.2.le⟩

theorem AtaB_minus_cont (M : Model) (hM : M.Standing) :
    ContinuousOn (fun γ => M.vMinus γ 0) M.GammaMinus := by
  intro γ hγ
  have key : ∀ γ2 ∈ M.GammaMinus, γ ≤ γ2 →
      ContinuousWithinAt (fun γ => M.vMinus γ 0) (M.GammaMinus ∩ Iic γ2) γ := by
    intro γ2 hγ2 hle
    obtain ⟨hvc, -, -⟩ := AtaB_vMinus_solves M hγ2
    set l2 := M.lgam γ2
    have hg : ContinuousWithinAt (fun γ' => M.vMinus γ2 (l2 - M.lgam γ'))
        (M.GammaMinus ∩ Iic γ2) γ := by
      have hmaps : MapsTo (fun γ' => l2 - M.lgam γ') (M.GammaMinus ∩ Iic γ2) (Icc l2 0) := by
        intro x hx
        have h1 : l2 ≤ M.lgam x := AtaB_lgam_anti M hM hx.2
        have h2 : M.lgam x < 0 := AtaB_lgam_neg M hM hx.1.1
        have h3 : l2 < 0 := AtaB_lgam_neg M hM hγ2.1
        exact ⟨by linarith, by linarith⟩
      refine (hvc.comp ?_ hmaps) γ ⟨hγ, hle⟩
      simp only [Model.lgam]
      fun_prop
    exact hg.congr (fun x hx => AtaB_minus_shiftid M hM hx.1 hγ2 hx.2)
      (AtaB_minus_shiftid M hM hγ hγ2 hle)
  by_cases h : ∃ γ2 ∈ M.GammaMinus, γ < γ2
  · obtain ⟨γ2, hγ2, hlt⟩ := h
    exact (continuousWithinAt_inter (Iic_mem_nhds hlt)).mp (key γ2 hγ2 hlt.le)
  · push_neg at h
    have := key γ hγ le_rfl
    have hs : M.GammaMinus ∩ Iic γ = M.GammaMinus :=
      inter_eq_left.mpr (fun x hx => h x hx)
    rwa [hs] at this

theorem AtaB_minus_strictMono (M : Model) (hM : M.Standing) :
    StrictMonoOn (fun γ => M.vMinus γ 0) M.GammaMinus := by
  intro γ1 h1 γ2 h2 hlt
  have hl1 : M.lgam γ1 < 0 := AtaB_lgam_neg M hM h1.1
  have hl12 : M.lgam γ2 < M.lgam γ1 := AtaB_lgam_strictAnti M hM hlt
  have hmono := AtaB_minus_mono M hM h2
  show M.vMinus γ1 0 < M.vMinus γ2 0
  rw [AtaB_minus_shiftid M hM h1 h2 hlt.le]
  have := hmono (a := -M.lgam γ1) (b := -M.lgam γ2) ⟨by linarith, by linarith⟩
    ⟨by linarith, le_rfl⟩ (by linarith)
  simp only at this
  rwa [show M.lgam γ2 + -M.lgam γ1 = M.lgam γ2 - M.lgam γ1 by ring,
    show M.lgam γ2 + -M.lgam γ2 = 0 by ring] at this

theorem AtaB_minus_v0_nonpos (M : Model) (hM : M.Standing) :
    ∀ w ∈ Icc (M.lgam 0) 0, M.vMinus 0 w ≤ 0 := by
  obtain ⟨hhs, hbs, hks, ha, hμ, hσ, hhpos, hhneg, hhcont⟩ := AtaB_basic M hM
  have h0 := (riccati_wellposed M hM).2.2.1
  obtain ⟨hvc, hvl, hvd⟩ := AtaB_vMinus_solves M h0
  set l0 := M.lgam 0
  have hl0 : l0 < 0 := AtaB_lgam_neg M hM le_rfl
  have hσ2 : 0 < M.σ ^ 2 := by positivity
  have hhl0 : M.hcost l0 = M.μ * M.kappa + M.a / 4 * M.kappa ^ 2 := by
    rw [hhneg l0 hl0.le]
    simp only [l0, Model.lgam]
    field_simp
    ring
  have hd' : ∀ x ∈ Ico l0 0, HasDerivWithinAt (M.vMinus 0) (M.rhsLower l0 x (M.vMinus 0 x))
      (Ici x) x := fun x hx =>
    (hvd x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)
  refine image_le_of_deriv_right_lt_deriv_boundary'
    (f' := fun x => M.rhsLower l0 x (M.vMinus 0 x))
    (B := fun _ => 0) (B' := fun _ => 0) hvc hd' ?_ continuousOn_const
    (fun x _ => hasDerivWithinAt_const _ _ _) ?_
  · show M.vMinus 0 l0 ≤ 0
    rw [hvl]; linarith
  · intro x hx hx0
    have hx0' : M.vMinus 0 x = 0 := hx0
    show M.rhsLower l0 x (M.vMinus 0 x) < 0
    rw [hx0']
    have hval : M.rhsLower l0 x 0 = 2 * M.bStar * x / M.σ ^ 2 := by
      simp only [Model.rhsLower, hhl0]
      rw [hhneg x hx.2.le]
      field_simp
      ring
    rw [hval]
    apply div_neg_of_neg_of_pos _ hσ2
    nlinarith [hx.2]

theorem AtaB_minus_g0 (M : Model) (hM : M.Standing) : M.vMinus 0 0 < 0 := by
  obtain ⟨hhs, hbs, hks, ha, hμ, hσ, hhpos, hhneg, hhcont⟩ := AtaB_basic M hM
  have h0 := (riccati_wellposed M hM).2.2.1
  obtain ⟨hvc, hvl, hvd⟩ := AtaB_vMinus_solves M h0
  set l0 := M.lgam 0
  have hl0 : l0 < 0 := AtaB_lgam_neg M hM le_rfl
  have hhl0 : M.hcost l0 = M.μ * M.kappa + M.a / 4 * M.kappa ^ 2 := by
    rw [hhneg l0 hl0.le]
    simp only [l0, Model.lgam]
    field_simp
    ring
  rcases (AtaB_minus_v0_nonpos M hM 0 ⟨hl0.le, le_rfl⟩).lt_or_eq with h | h
  · exact h
  · exfalso
    have hc6 := corollary_6 M hM l0 hl0 (M.vMinus 0) hvl hvd 0 ⟨hl0, le_rfl⟩
    rw [(hvd 0 ⟨hl0.le, le_rfl⟩).derivWithin (uniqueDiffOn_Icc hl0 0 ⟨hl0.le, le_rfl⟩), h]
      at hc6
    simp only [Model.rhsLower, hhl0, hhneg 0 le_rfl] at hc6
    have : M.a / (2 * M.σ ^ 2) * (0 ^ 2 - M.kappa ^ 2) - 2 * M.μ / M.σ ^ 2 * (0 + M.kappa) +
        2 * (M.μ * M.kappa + M.a / 4 * M.kappa ^ 2 - -(M.bStar * 0)) / M.σ ^ 2 = 0 := by
      field_simp; ring
    linarith

/-- Uniqueness for the translated lower Riccati equation on `[0, s]`. -/
theorem AtaB_unique19 (M : Model) {s : ℝ} (U V : ℝ → ℝ)
    (hUc : ContinuousOn U (Icc 0 s)) (hVc : ContinuousOn V (Icc 0 s))
    (hU : ∀ t ∈ Icc 0 s, HasDerivWithinAt U
      (M.a / (2 * M.σ ^ 2) * (U t ^ 2 - M.kappa ^ 2) - 2 * M.μ / M.σ ^ 2 * (U t + M.kappa)
        + 2 * M.bStar / M.σ ^ 2 * t) (Icc 0 s) t)
    (hV : ∀ t ∈ Icc 0 s, HasDerivWithinAt V
      (M.a / (2 * M.σ ^ 2) * (V t ^ 2 - M.kappa ^ 2) - 2 * M.μ / M.σ ^ 2 * (V t + M.kappa)
        + 2 * M.bStar / M.σ ^ 2 * t) (Icc 0 s) t)
    (h0 : U 0 = V 0) : EqOn U V (Icc 0 s) := by
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hUc
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hVc
  set R := max (max C₁ C₂) 0
  have hR : 0 ≤ R := le_max_right _ _
  set c1 := M.a / (2 * M.σ ^ 2)
  set c2 := 2 * M.μ / M.σ ^ 2
  set c3 := 2 * M.bStar / M.σ ^ 2
  refine ODE_solution_unique_of_mem_Icc_right
    (v := fun t y => c1 * (y ^ 2 - M.kappa ^ 2) - c2 * (y + M.kappa) + c3 * t)
    (s := fun _ => Metric.closedBall 0 R) (K := Real.toNNReal (2 * |c1| * R + |-c2|))
    ?_ hUc ?_ ?_ hVc ?_ ?_ h0
  · intro t _
    have := AtaB_lip_quad c1 (-c2) (-c1 * M.kappa ^ 2 - c2 * M.kappa + c3 * t) R hR
    convert this using 1
    funext y; ring
  · intro t ht
    exact (hU t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  · intro t ht
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hC₁ t (Ico_subset_Icc_self ht)).trans ((le_max_left _ _).trans (le_max_left _ _))
  · intro t ht
    exact (hV t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  · intro t ht
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hC₂ t (Ico_subset_Icc_self ht)).trans ((le_max_right _ _).trans (le_max_left _ _))

set_option maxHeartbeats 1000000 in
theorem AtaB_minus_unbdd (M : Model) (hM : M.Standing) :
    ¬ BddAbove ((fun γ => M.vMinus γ 0) '' M.GammaMinus) := by
  obtain ⟨hhs, hbs, hks, ha, hμ, hσ, hhpos, hhneg, hhcont⟩ := AtaB_basic M hM
  obtain ⟨huniq, -, h0m, -⟩ := riccati_wellposed M hM
  rintro ⟨B0, hB0⟩
  set D := |B0| + 1 with hDdef
  have hD : 0 < D := by positivity
  have hkD : ∀ γ ∈ M.GammaMinus, M.vMinus γ 0 < D := fun γ hγ => by
    have h1 : M.vMinus γ 0 ≤ B0 := hB0 ⟨γ, hγ, rfl⟩
    have h2 := le_abs_self B0
    linarith
  set c1 := M.a / (2 * M.σ ^ 2) with hc1d
  set c2 := 2 * M.μ / M.σ ^ 2 with hc2d
  set c3 := 2 * M.bStar / M.σ ^ 2 with hc3d
  have hc1 : 0 ≤ c1 := by positivity
  have hc2 : 0 ≤ c2 := by positivity
  have hc3 : 0 < c3 := by positivity
  set C := c1 * M.kappa ^ 2 + c2 * (D + M.kappa) with hCd
  have hC : 0 ≤ C := by positivity
  set T := 2 * (C + D + 1 + M.kappa) / c3 + 1 with hTd
  have hT : 1 ≤ T := by
    have : 0 ≤ 2 * (C + D + 1 + M.kappa) / c3 := by positivity
    linarith
  have hT0 : 0 < T := by linarith
  have hTbig : C * T + D + 1 + M.kappa ≤ c3 * T ^ 2 / 2 := by
    have h1 : c3 * T / 2 = (C + D + 1 + M.kappa) + c3 / 2 := by
      rw [hTd]; field_simp
    have h2 : C + D + 1 + M.kappa ≤ c3 * T / 2 := by rw [h1]; linarith
    have h3 : c3 * T ^ 2 / 2 = T * (c3 * T / 2) := by ring
    rw [h3]
    have h4 : 0 ≤ D + 1 + M.kappa := by positivity
    nlinarith
  set p : ℝ → ℝ := fun y => max (-M.kappa) (min y (D + 1)) with hp
  have hpmem : ∀ y, -M.kappa ≤ p y ∧ p y ≤ D + 1 := fun y =>
    ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hplip : LipschitzWith 1 p := (LipschitzWith.id.min_const (D + 1)).const_max (-M.kappa)
  set F : ℝ → ℝ → ℝ := fun s y => c1 * (p y ^ 2 - M.kappa ^ 2) - c2 * (p y + M.kappa) + c3 * s
    with hF
  set Lr := c1 * M.kappa ^ 2 + c2 * (D + 1 + M.kappa) + c1 * (M.kappa + (D + 1)) ^ 2 + c3 * T
    with hLr
  have hLr0 : 0 ≤ Lr := by positivity
  have hFbd : ∀ s ∈ Icc 0 T, ∀ y, |F s y| ≤ Lr := by
    intro s hs y
    obtain ⟨h1, h2⟩ := hpmem y
    have q1 : p y ^ 2 ≤ (M.kappa + (D + 1)) ^ 2 :=
      sq_le_sq' (by linarith) (by linarith)
    have q2 : c1 * p y ^ 2 ≤ c1 * (M.kappa + (D + 1)) ^ 2 := mul_le_mul_of_nonneg_left q1 hc1
    have q3 : 0 ≤ c1 * p y ^ 2 := mul_nonneg hc1 (sq_nonneg _)
    have q4 : 0 ≤ c2 * (p y + M.kappa) := mul_nonneg hc2 (by linarith)
    have q5 : c2 * (p y + M.kappa) ≤ c2 * (D + 1 + M.kappa) :=
      mul_le_mul_of_nonneg_left (by linarith) hc2
    have q6 : c3 * s ≤ c3 * T := mul_le_mul_of_nonneg_left hs.2 hc3.le
    have q7 : 0 ≤ c3 * s := mul_nonneg hc3.le hs.1
    simp only [F]
    rw [abs_le]
    constructor <;> nlinarith
  set R := M.kappa + (D + 1) with hRd
  set L : NNReal := ⟨Lr, hLr0⟩
  set A : NNReal := ⟨Lr * T, by positivity⟩
  set Kq := Real.toNNReal (2 * |c1| * R + |-c2|)
  have hPL : IsPicardLindelof F (tmin := 0) (tmax := T) ⟨0, le_rfl, hT0.le⟩ (-M.kappa)
      A 0 L (Kq * 1) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s _
      have hq := AtaB_lip_quad c1 (-c2) (-c1 * M.kappa ^ 2 - c2 * M.kappa + c3 * s) R
        (by positivity)
      have := hq.comp (hplip.lipschitzOnWith (s := Metric.closedBall (-M.kappa) A)) (by
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
  -- `U ≥ -κ`
  have hlow : ∀ s ∈ Icc 0 T, -M.kappa ≤ U s := by
    have key : ∀ ε > 0, ∀ s ∈ Icc 0 T, -U s ≤ M.kappa + ε * (1 + s) := by
      intro ε hε
      refine image_le_of_deriv_right_lt_deriv_boundary' (f := fun x => -U x)
        (f' := fun x => -F x (U x)) (B := fun s => M.kappa + ε * (1 + s))
        (B' := fun _ => ε) hUc.neg (fun x hx => (hUd' x hx).neg) ?_ (by fun_prop) ?_ ?_
      · show -U 0 ≤ _; rw [hU0]; nlinarith
      · intro x _
        have := (((hasDerivWithinAt_id x (Ici x)).const_add 1).const_mul ε).const_add M.kappa
        exact this.congr_deriv (mul_one ε)
      · intro x hx hxe
        have hxe' : -U x = M.kappa + ε * (1 + x) := hxe
        have hpos : 0 < ε * (1 + x) := mul_pos hε (by linarith [hx.1])
        have hpx : p (U x) = -M.kappa := by
          simp only [p]
          rw [min_eq_left (by linarith), max_eq_left (by linarith)]
        show -F x (U x) < ε
        simp only [F, hpx]
        have : 0 ≤ c3 * x := mul_nonneg hc3.le hx.1
        nlinarith
    intro s hs
    have := AtaB_le_of_eps (-U s) M.kappa (1 + s) (by linarith [hs.1])
      (fun ε hε => key ε hε s hs)
    linarith
  by_cases hS : ∃ s ∈ Icc 0 T, D ≤ U s
  · set S := Icc 0 T ∩ U ⁻¹' Ici D with hSd
    have hSc : IsClosed S := hUc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    obtain ⟨s0, hs0, hs0D⟩ := hS
    have hSne : S.Nonempty := ⟨s0, hs0, hs0D⟩
    have hSbdd : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
    set s1 := sInf S with hs1d
    have hs1 : s1 ∈ S := hSc.csInf_mem hSne hSbdd
    have hs1T : s1 ≤ T := hs1.1.2
    have hs1D : D ≤ U s1 := hs1.2
    have hs1pos : 0 < s1 := by
      rcases hs1.1.1.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h, hU0] at hs1D
        linarith
    have hbefore : ∀ s ∈ Ico 0 s1, U s < D := by
      intro s hs
      by_contra h
      push_neg at h
      have : s1 ≤ s := csInf_le hSbdd ⟨⟨hs.1, hs.2.le.trans hs1T⟩, h⟩
      linarith [hs.2]
    have hupp : ∀ s ∈ Icc 0 s1, U s ≤ D := by
      have hcl : IsClosed (Icc 0 s1 ∩ U ⁻¹' Iic D) :=
        (hUc.mono (Icc_subset_Icc_right hs1T)).preimage_isClosed_of_isClosed isClosed_Icc
          isClosed_Iic
      have hsub : Ico 0 s1 ⊆ Icc 0 s1 ∩ U ⁻¹' Iic D := fun s hs =>
        ⟨Ico_subset_Icc_self hs, (hbefore s hs).le⟩
      have := closure_minimal hsub hcl
      rw [closure_Ico hs1pos.ne] at this
      exact fun s hs => (this hs).2
    have hpU : ∀ s ∈ Icc 0 s1, p (U s) = U s := by
      intro s hs
      simp only [p]
      rw [min_eq_left (by linarith [hupp s hs]), max_eq_right (hlow s ⟨hs.1, hs.2.trans hs1T⟩)]
    have hG : ∀ s ∈ Icc 0 s1, HasDerivWithinAt U
        (M.a / (2 * M.σ ^ 2) * (U s ^ 2 - M.kappa ^ 2) - 2 * M.μ / M.σ ^ 2 * (U s + M.kappa)
          + 2 * M.bStar / M.σ ^ 2 * s) (Icc 0 s1) s := by
      intro s hs
      have := (hUd s ⟨hs.1, hs.2.trans hs1T⟩).mono (Icc_subset_Icc_right hs1T)
      simp only [F, hpU s hs] at this
      exact this
    have hUc1 : ContinuousOn U (Icc 0 s1) := hUc.mono (Icc_subset_Icc_right hs1T)
    set l0 := M.lgam 0
    have hl0 : l0 < 0 := AtaB_lgam_neg M hM le_rfl
    rcases le_or_gt s1 (-l0) with hcase | hcase
    · -- compare with the solution for `γ = 0`
      obtain ⟨hvc, hvl, hvd⟩ := AtaB_vMinus_solves M h0m
      have hR0 := AtaB_minus_unshift M hM hl0.le _ hvd
      have hmaps : MapsTo (fun s => l0 + s) (Icc 0 s1) (Icc l0 0) := by
        intro x hx; simp only [mem_Icc] at hx ⊢; constructor <;> linarith [hx.1, hx.2]
      have heq := AtaB_unique19 M U (fun s => M.vMinus 0 (l0 + s)) hUc1
        (hvc.comp (continuousOn_const.add continuousOn_id) hmaps) hG
        (fun t ht => (hR0 t ⟨ht.1, ht.2.trans hcase⟩).mono (Icc_subset_Icc_right hcase))
        (by show U 0 = M.vMinus 0 (l0 + 0); rw [add_zero, hU0]; exact hvl.symm)
        ⟨hs1pos.le, le_rfl⟩
      have := AtaB_minus_v0_nonpos M hM (l0 + s1) (hmaps ⟨hs1pos.le, le_rfl⟩)
      simp only at heq
      linarith
    · -- `γ = b⋆ s₁ - μκ - aκ²/4 ≥ 0` has `l_γ = -s₁`
      set γ := M.bStar * s1 - M.μ * M.kappa - M.a / 4 * M.kappa ^ 2 with hγd
      have hl0v : -l0 = (M.μ * M.kappa + M.a / 4 * M.kappa ^ 2) / M.bStar := by
        simp only [l0, Model.lgam]; field_simp; ring
      have hγ0 : 0 ≤ γ := by
        rw [hl0v, div_lt_iff₀ hbs] at hcase
        simp only [γ]; nlinarith
      have hlg : M.lgam γ = -s1 := by
        simp only [Model.lgam, γ]; field_simp; ring
      have hG' : ∀ s ∈ Icc 0 (-(-s1)), HasDerivWithinAt U
          (M.a / (2 * M.σ ^ 2) * (U s ^ 2 - M.kappa ^ 2) - 2 * M.μ / M.σ ^ 2 * (U s + M.kappa)
            + 2 * M.bStar / M.σ ^ 2 * s) (Icc 0 (-(-s1))) s := by
        rw [neg_neg]; exact hG
      have hmaps : MapsTo (fun w => w - -s1) (Icc (-s1) 0) (Icc 0 s1) := by
        intro x hx; simp only [mem_Icc] at hx ⊢; constructor <;> linarith [hx.1, hx.2]
      have hsol : M.SolvesMinus γ (fun w => U (w - -s1)) := by
        unfold Model.SolvesMinus
        rw [hlg]
        refine ⟨hUc1.comp (continuousOn_id.sub continuousOn_const) hmaps, by simp [hU0], ?_⟩
        exact AtaB_minus_shift M hM (by linarith) U hG'
      have hγ : γ ∈ M.GammaMinus := ⟨hγ0, _, hsol⟩
      have heq := huniq γ hγ0 _ _ (AtaB_vMinus_solves M hγ) hsol
        ⟨by rw [hlg]; linarith, le_rfl⟩
      have h1 := hkD γ hγ
      rw [heq] at h1
      simp only [zero_sub, neg_neg] at h1
      linarith
  · push_neg at hS
    have hpU : ∀ s ∈ Icc 0 T, p (U s) = U s := by
      intro s hs
      simp only [p]
      rw [min_eq_left (by linarith [hS s hs]), max_eq_right (hlow s hs)]
    have hmono : MonotoneOn (fun s => U s - c3 * s ^ 2 / 2 + C * s) (Icc 0 T) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T)
        ((hUc.sub (by fun_prop)).add (by fun_prop)) (f' := fun s => F s (U s) - c3 * s + C) ?_ ?_
      · intro x hx
        rw [interior_Icc] at hx ⊢
        have h1 := (hUd x (Ioo_subset_Icc_self hx)).mono Ioo_subset_Icc_self
        have h2 : HasDerivAt (fun s => c3 * s ^ 2 / 2) (c3 * x) x :=
          (((hasDerivAt_pow 2 x).const_mul c3).div_const 2).congr_deriv (by push_cast; ring)
        have h3 : HasDerivAt (fun s => C * s) C x :=
          ((hasDerivAt_id x).const_mul C).congr_deriv (mul_one C)
        exact (h1.sub h2.hasDerivWithinAt).add h3.hasDerivWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hxI : x ∈ Icc 0 T := Ioo_subset_Icc_self hx
        simp only [F, hpU x hxI]
        have h1 := hlow x hxI
        have h2 := (hS x hxI).le
        have q1 : 0 ≤ c1 * U x ^ 2 := mul_nonneg hc1 (sq_nonneg _)
        have q2 : c2 * (U x + M.kappa) ≤ c2 * (D + M.kappa) :=
          mul_le_mul_of_nonneg_left (by linarith) hc2
        simp only [C]
        nlinarith
    have := hmono ⟨le_rfl, hT0.le⟩ ⟨hT0.le, le_rfl⟩ hT0.le
    simp only [hU0] at this
    have h3 := hS T ⟨hT0.le, le_rfl⟩
    nlinarith

theorem solution (M : Model) (hM : M.Standing) :
    ContinuousOn (fun γ => M.vMinus γ 0) M.GammaMinus ∧
    StrictMonoOn (fun γ => M.vMinus γ 0) M.GammaMinus ∧
    M.vMinus 0 0 < 0 ∧
    ¬ BddAbove ((fun γ => M.vMinus γ 0) '' M.GammaMinus) :=
  ⟨AtaB_minus_cont M hM, AtaB_minus_strictMono M hM, AtaB_minus_g0 M hM, AtaB_minus_unbdd M hM⟩
