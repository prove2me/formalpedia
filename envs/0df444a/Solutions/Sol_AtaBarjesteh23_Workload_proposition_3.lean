-- Prove2me | solution 1 for AtaBarjesteh23.Workload.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T20:38:37.463007+00:00
-- url     : https://prove2.me/submissions/aecdb1da-1788-4df6-b879-9e128058b142

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting
import Definitions.Def_AtaBarjesteh23_Workload_DriftBM
import Definitions.Def_AtaBarjesteh23_Workload_Control
import Theorems.Thm_AtaBarjesteh23_Workload_riccati_wellposed
import Theorems.Thm_AtaBarjesteh23_Workload_lemma_20
import Theorems.Thm_AtaBarjesteh23_Workload_corollary_6
import Theorems.Thm_AtaBarjesteh23_Workload_lemma_3
import Theorems.Thm_AtaBarjesteh23_Workload_corollary_1
import Theorems.Thm_AtaBarjesteh23_Workload_lemma_4_i
import Theorems.Thm_AtaBarjesteh23_Workload_lemma_4_ii

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

theorem AtaB_vMinus_solves (M : Model) {γ : ℝ} (hγ : γ ∈ M.GammaMinus) :
    M.SolvesMinus γ (M.vMinus γ) := Classical.epsilon_spec hγ.2

theorem AtaB_gammaStar_spec (M : Model) (hM : M.Standing) :
    M.gammaStar ∈ M.GammaMinus ∧ M.gammaStar ∈ M.GammaPlus ∧
      M.vMinus M.gammaStar 0 = M.vPlus M.gammaStar 0 :=
  Classical.epsilon_spec (corollary_1 M hM).exists

theorem AtaB_gammaStar_pos (M : Model) (hM : M.Standing) : 0 < M.gammaStar := by
  obtain ⟨hm, hp, he⟩ := AtaB_gammaStar_spec M hM
  rcases hm.1.lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h] at he
    have h1 := (lemma_4_i M hM).2.2.1
    have h2 := (lemma_4_ii M hM).2.2.1
    linarith

theorem AtaB_lgam_neg (M : Model) (hM : M.Standing) {γ : ℝ} (hγ : 0 ≤ γ) : M.lgam γ < 0 := by
  obtain ⟨hhs, hbs, hks, ha, hμ, -⟩ := AtaB_basic M hM
  simp only [Model.lgam]
  have : 0 < γ + M.μ * M.kappa + M.a / 4 * M.kappa ^ 2 := by positivity
  have : 0 < 1 / M.bStar := by positivity
  nlinarith

/-- The common form of the lower and upper Riccati right sides. -/
theorem AtaB_rhsLower_eq (M : Model) (hM : M.Standing) {γ : ℝ} (hγ : 0 ≤ γ) (w y : ℝ) :
    M.rhsLower (M.lgam γ) w y = M.a / (2 * M.σ ^ 2) * y ^ 2 - 2 * M.μ / M.σ ^ 2 * y
      + 2 * (γ - M.hcost w) / M.σ ^ 2 := by
  obtain ⟨hhs, hbs, hks, ha, hμ, hσ, hhpos, hhneg, -⟩ := AtaB_basic M hM
  simp only [Model.rhsLower]
  rw [hhneg _ (AtaB_lgam_neg M hM hγ).le]
  simp only [Model.lgam]
  field_simp
  ring

theorem AtaB_rhsUpper_eq (M : Model) (hM : M.Standing) {γ : ℝ} (hγ : 0 ≤ γ) (w y : ℝ)
    (hw : 0 ≤ w) :
    M.rhsUpper (M.ugam γ) w y = M.a / (2 * M.σ ^ 2) * y ^ 2 - 2 * M.μ / M.σ ^ 2 * y
      + 2 * (γ - M.hcost w) / M.σ ^ 2 := by
  obtain ⟨hhs, hbs, hks, ha, hμ, hσ, hhpos, hhneg, -⟩ := AtaB_basic M hM
  simp only [Model.rhsUpper]
  rw [hhpos (M.ugam γ) (div_nonneg hγ hhs.le)]
  simp only [Model.ugam]
  field_simp

theorem AtaB_vStar_deriv (M : Model) (hM : M.Standing) :
    ∀ w ∈ Icc M.lStar M.uStar, HasDerivWithinAt M.vStar
      (M.a / (2 * M.σ ^ 2) * M.vStar w ^ 2 - 2 * M.μ / M.σ ^ 2 * M.vStar w
        + 2 * (M.gammaStar - M.hcost w) / M.σ ^ 2) (Icc M.lStar M.uStar) w := by
  obtain ⟨hhs, hbs, hks, ha, hμ, hσ, hhpos, hhneg, -⟩ := AtaB_basic M hM
  obtain ⟨hm, hp, he⟩ := AtaB_gammaStar_spec M hM
  have hγ := AtaB_gammaStar_pos M hM
  obtain ⟨-, -, hmd⟩ := AtaB_vMinus_solves M hm
  obtain ⟨-, -, hpd⟩ := AtaB_vPlus_solves M hp
  have hl : M.lStar < 0 := AtaB_lgam_neg M hM hγ.le
  have hu : 0 < M.uStar := div_pos hγ hhs
  have heqm : EqOn M.vStar (M.vMinus M.gammaStar) (Icc M.lStar 0) := by
    intro x hx; simp [Model.vStar, hx.2]
  have heqp : EqOn M.vStar (M.vPlus M.gammaStar) (Icc 0 M.uStar) := by
    intro x hx
    rcases hx.1.lt_or_eq with h | h
    · simp [Model.vStar, not_le.mpr h]
    · subst h; simp [Model.vStar, he]
  intro w hw
  rw [← Icc_union_Icc_eq_Icc hl.le hu.le]
  refine HasDerivWithinAt.union ?_ ?_
  · by_cases h : w ≤ 0
    · have hwI : w ∈ Icc M.lStar 0 := ⟨hw.1, h⟩
      have := (hmd w hwI).congr heqm (heqm hwI)
      refine this.congr_deriv ?_
      rw [heqm hwI]
      exact AtaB_rhsLower_eq M hM hγ.le w _
    · apply HasFDerivWithinAt.of_notMem_closure
      rw [closure_Icc]
      exact fun hh => h hh.2
  · by_cases h : 0 ≤ w
    · have hwI : w ∈ Icc 0 M.uStar := ⟨h, hw.2⟩
      have := (hpd w hwI).congr heqp (heqp hwI)
      refine this.congr_deriv ?_
      rw [heqp hwI]
      exact AtaB_rhsUpper_eq M hM hγ.le w _ h
    · apply HasFDerivWithinAt.of_notMem_closure
      rw [closure_Icc]
      exact fun hh => h hh.1

theorem AtaB_vStar_deriv_pos (M : Model) (hM : M.Standing) :
    ∀ w ∈ Ioo M.lStar M.uStar, 0 < M.a / (2 * M.σ ^ 2) * M.vStar w ^ 2
      - 2 * M.μ / M.σ ^ 2 * M.vStar w + 2 * (M.gammaStar - M.hcost w) / M.σ ^ 2 := by
  obtain ⟨hhs, hbs, hks, ha, hμ, hσ, hhpos, hhneg, -⟩ := AtaB_basic M hM
  obtain ⟨hm, hp, he⟩ := AtaB_gammaStar_spec M hM
  have hγ := AtaB_gammaStar_pos M hM
  obtain ⟨-, hml, hmd⟩ := AtaB_vMinus_solves M hm
  obtain ⟨hpc, hpu, hpd⟩ := AtaB_vPlus_solves M hp
  have hl : M.lStar < 0 := AtaB_lgam_neg M hM hγ.le
  have hu : 0 < M.uStar := div_pos hγ hhs
  rw [show M.lgam M.gammaStar = M.lStar from rfl] at hml hmd
  intro w hw
  by_cases h : w ≤ 0
  · have hc6 := corollary_6 M hM M.lStar hl _ hml hmd w ⟨hw.1, h⟩
    have hwI : w ∈ Icc M.lStar 0 := ⟨hw.1.le, h⟩
    rw [(hmd w hwI).derivWithin (uniqueDiffOn_Icc hl w hwI),
      show M.rhsLower M.lStar w _ = _ from AtaB_rhsLower_eq M hM hγ.le w _] at hc6
    simpa [Model.vStar, h] using hc6
  · push_neg at h
    set u := M.uStar
    have hR := AtaB_plus_refl M hM hu.le _ hpd
    have hU0 : (fun s => M.vPlus M.gammaStar (u - s)) 0 = 0 := by simp [hpu, u, Model.uStar]
    have h20 := lemma_20 M hM u hu _ hU0 hR
    have hs : u - w ∈ Ioc 0 u := ⟨by linarith [hw.2], by linarith⟩
    have hd := (h20 (u - w) hs).2
    rw [(hR (u - w) (Ioc_subset_Icc_self hs)).derivWithin
      (uniqueDiffOn_Icc hu _ (Ioc_subset_Icc_self hs))] at hd
    simp only [sub_sub_cancel] at hd
    have hvs : M.vStar w = M.vPlus M.gammaStar w := by simp [Model.vStar, not_le.mpr h]
    rw [hvs, hhpos w h.le]
    have hγu : M.hStar * u = M.gammaStar := by simp only [u, Model.uStar, Model.ugam]; field_simp
    have e : 2 * M.hStar / M.σ ^ 2 * (u - w) = 2 * (M.gammaStar - M.hStar * w) / M.σ ^ 2 := by
      rw [← hγu]; ring
    rw [e] at hd
    linarith

theorem AtaB_bellman_deriv (M : Model) (hM : M.Standing) {l u γ : ℝ} {v : ℝ → ℝ}
    (hv : M.BellmanV l u γ v) :
    ∀ w ∈ Icc l u, HasDerivWithinAt v (M.a / (2 * M.σ ^ 2) * v w ^ 2 - 2 * M.μ / M.σ ^ 2 * v w
      + 2 * (γ - M.hcost w) / M.σ ^ 2) (Icc l u) w := by
  obtain ⟨hlu, hC1, hode, -, -, -, -⟩ := hv
  have hhcont : Continuous M.hcost := (AtaB_basic M hM).2.2.2.2.2.2.2.2
  have hUD : UniqueDiffOn ℝ (Icc l u) := uniqueDiffOn_Icc hlu
  have hRcont : ContinuousOn (fun w => M.a / (2 * M.σ ^ 2) * v w ^ 2 - 2 * M.μ / M.σ ^ 2 * v w
      + 2 * (γ - M.hcost w) / M.σ ^ 2) (Icc l u) := by
    have := hC1.continuousOn
    have := hhcont.continuousOn (s := Icc l u)
    fun_prop
  have hEq : EqOn (derivWithin v (Icc l u)) (fun w => M.a / (2 * M.σ ^ 2) * v w ^ 2
      - 2 * M.μ / M.σ ^ 2 * v w + 2 * (γ - M.hcost w) / M.σ ^ 2) (Icc l u) := by
    refine EqOn.of_subset_closure (s := Ioo l u) ?_ (hC1.continuousOn_derivWithin hUD le_rfl)
      hRcont Ioo_subset_Icc_self (by rw [closure_Ioo hlu.ne])
    intro w hw
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hw.1 hw.2)]
    exact hode w hw
  intro w hw
  have := ((hC1.differentiableOn (by norm_num)) w hw).hasDerivWithinAt
  rwa [hEq hw] at this

set_option maxHeartbeats 1000000 in
theorem solution (M : Model) (hM : M.Standing) :
    (∀ w ∈ Icc M.lStar M.uStar, M.vStar w ≤ 0) ∧
    StrictMonoOn M.vStar (Icc M.lStar M.uStar) ∧
    ContDiffOn ℝ 1 M.vStar (Icc M.lStar M.uStar) ∧
    M.BellmanV M.lStar M.uStar M.gammaStar M.vStar ∧
    ∀ (l u γ : ℝ) (v : ℝ → ℝ), M.BellmanV l u γ v →
      l = M.lStar ∧ u = M.uStar ∧ γ = M.gammaStar ∧ EqOn v M.vStar (Icc l u) := by
  obtain ⟨hhs, hbs, hks, ha, hμ, hσ, hhpos, hhneg, hhcont⟩ := AtaB_basic M hM
  obtain ⟨hm, hp, he⟩ := AtaB_gammaStar_spec M hM
  have hγ := AtaB_gammaStar_pos M hM
  obtain ⟨hmc, hml, hmd⟩ := AtaB_vMinus_solves M hm
  obtain ⟨hpc, hpu, hpd⟩ := AtaB_vPlus_solves M hp
  have hl : M.lStar < 0 := AtaB_lgam_neg M hM hγ.le
  have hu : 0 < M.uStar := div_pos hγ hhs
  have hlu : M.lStar < M.uStar := hl.trans hu
  have hD := AtaB_vStar_deriv M hM
  have hUD : UniqueDiffOn ℝ (Icc M.lStar M.uStar) := uniqueDiffOn_Icc hlu
  have hvc : ContinuousOn M.vStar (Icc M.lStar M.uStar) := fun w hw => (hD w hw).continuousWithinAt
  have hmono : StrictMonoOn M.vStar (Icc M.lStar M.uStar) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) hvc
      (f' := fun w => M.a / (2 * M.σ ^ 2) * M.vStar w ^ 2 - 2 * M.μ / M.σ ^ 2 * M.vStar w
        + 2 * (M.gammaStar - M.hcost w) / M.σ ^ 2) ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx ⊢
      exact (hD x (Ioo_subset_Icc_self hx)).mono Ioo_subset_Icc_self
    · intro x hx
      rw [interior_Icc] at hx
      exact AtaB_vStar_deriv_pos M hM x hx
  have hvu : M.vStar M.uStar = 0 := by
    simp only [Model.vStar, not_le.mpr hu, if_false]
    exact hpu
  have hvl : M.vStar M.lStar = -M.kappa := by
    simp only [Model.vStar, hl.le, if_true]
    exact hml
  have hRcont : ContinuousOn (fun w => M.a / (2 * M.σ ^ 2) * M.vStar w ^ 2
      - 2 * M.μ / M.σ ^ 2 * M.vStar w + 2 * (M.gammaStar - M.hcost w) / M.σ ^ 2)
      (Icc M.lStar M.uStar) := by
    have := hhcont.continuousOn (s := Icc M.lStar M.uStar)
    fun_prop
  have hderivEq : ∀ w ∈ Icc M.lStar M.uStar, derivWithin M.vStar (Icc M.lStar M.uStar) w =
      M.a / (2 * M.σ ^ 2) * M.vStar w ^ 2 - 2 * M.μ / M.σ ^ 2 * M.vStar w
        + 2 * (M.gammaStar - M.hcost w) / M.σ ^ 2 := fun w hw => (hD w hw).derivWithin (hUD w hw)
  have hC1 : ContDiffOn ℝ 1 M.vStar (Icc M.lStar M.uStar) := by
    rw [contDiffOn_one_iff_derivWithin hUD]
    exact ⟨fun w hw => (hD w hw).differentiableWithinAt, hRcont.congr hderivEq⟩
  have hhl : M.hcost M.lStar = M.gammaStar + M.μ * M.kappa + M.a / 4 * M.kappa ^ 2 := by
    rw [hhneg _ hl.le]; simp only [Model.lStar, Model.lgam]; field_simp
  have hhu : M.hcost M.uStar = M.gammaStar := by
    rw [hhpos _ hu.le]; simp only [Model.uStar, Model.ugam]; field_simp
  have hBV : M.BellmanV M.lStar M.uStar M.gammaStar M.vStar := by
    refine ⟨hlu, hC1, ?_, hvl, hvu, ?_, ?_⟩
    · intro w hw
      exact ((hD w (Ioo_subset_Icc_self hw)).hasDerivAt (Icc_mem_nhds hw.1 hw.2)).deriv
    · rw [hderivEq _ ⟨le_rfl, hlu.le⟩, hvl, hhl]
      field_simp; ring
    · rw [hderivEq _ ⟨hlu.le, le_rfl⟩, hvu, hhu]
      ring
  refine ⟨fun w hw => hvu ▸ hmono.monotoneOn hw ⟨hlu.le, le_rfl⟩ hw.2, hmono, hC1, hBV, ?_⟩
  -- uniqueness
  intro l u γ v hv
  obtain ⟨hγ0, hlg, hl0, hug, hu0⟩ := lemma_3 M hM l u γ v hv
  have hvd := AtaB_bellman_deriv M hM hv
  obtain ⟨hlu', hC1v, -, hvl', hvu', -, -⟩ := hv
  have hvcont : ContinuousOn v (Icc l u) := hC1v.continuousOn
  have hsm : M.SolvesMinus γ v := by
    rw [Model.SolvesMinus, ← hlg]
    refine ⟨hvcont.mono (Icc_subset_Icc_right hu0.le), hvl', ?_⟩
    intro w hw
    have := (hvd w ⟨hw.1, hw.2.trans hu0.le⟩).mono (Icc_subset_Icc_right hu0.le)
    rw [hlg, AtaB_rhsLower_eq M hM hγ0.le]
    rw [hlg] at this
    exact this
  have hsp : M.SolvesPlus γ v := by
    rw [Model.SolvesPlus, ← hug]
    refine ⟨hvcont.mono (Icc_subset_Icc_left hl0.le), hvu', ?_⟩
    intro w hw
    have := (hvd w ⟨hl0.le.trans hw.1, hw.2⟩).mono (Icc_subset_Icc_left hl0.le)
    rw [hug, AtaB_rhsUpper_eq M hM hγ0.le w _ hw.1]
    rw [hug] at this
    exact this
  have hγm : γ ∈ M.GammaMinus := ⟨hγ0.le, v, hsm⟩
  have hγp : γ ∈ M.GammaPlus := ⟨hγ0.le, v, hsp⟩
  obtain ⟨huniqm, huniqp, -⟩ := riccati_wellposed M hM
  have e1 := huniqm γ hγ0.le _ _ (AtaB_vMinus_solves M hγm) hsm
    ⟨(AtaB_lgam_neg M hM hγ0.le).le, le_rfl⟩
  have e2 := huniqp γ hγ0.le _ _ (AtaB_vPlus_solves M hγp) hsp
    ⟨le_rfl, (div_nonneg hγ0.le hhs.le)⟩
  have hγs : γ = M.gammaStar :=
    (corollary_1 M hM).unique ⟨hγm, hγp, by rw [e1, e2]⟩ ⟨hm, hp, he⟩
  subst hγs
  refine ⟨hlg, hug, rfl, ?_⟩
  intro w hw
  by_cases h : w ≤ 0
  · have := huniqm M.gammaStar hγ0.le _ _ (AtaB_vMinus_solves M hm) hsm
      ⟨by rw [← hlg]; exact hw.1, h⟩
    simp only [Model.vStar, h, if_true]
    exact this.symm
  · push_neg at h
    have := huniqp M.gammaStar hγ0.le _ _ (AtaB_vPlus_solves M hp) hsp
      ⟨h.le, by rw [← hug]; exact hw.2⟩
    simp only [Model.vStar, not_le.mpr h, if_false]
    exact this.symm
