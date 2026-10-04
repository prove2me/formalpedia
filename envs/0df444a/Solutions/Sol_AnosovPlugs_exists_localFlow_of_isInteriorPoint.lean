-- Prove2me | solution 1 for AnosovPlugs.exists_localFlow_of_isInteriorPoint
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-03T19:13:19.533977+00:00
-- url     : https://prove2.me/submissions/56772be7-4d03-42d4-8afe-9ff800b07c92

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

/-! ## A local flow of a `C¹` ODE in a normed space, with uniqueness -/

section LfODE

open Metric

theorem lf_ode_localFlow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {v : E → E} {z₀ : E} (hv : ContDiffAt ℝ 1 v z₀) {G : Set E} (hG : IsOpen G) (hz₀ : z₀ ∈ G) :
    ∃ ε > (0 : ℝ), ∃ ρ > (0 : ℝ), ∃ αE : E × ℝ → E,
      (∀ z ∈ ball z₀ ρ, αE (z, 0) = z ∧ ∀ t ∈ Icc (-ε) ε,
        HasDerivAt (fun s => αE (z, s)) (v (αE (z, t))) t ∧ αE (z, t) ∈ G) ∧
      (∀ t ∈ Icc (-ε) ε, ContinuousOn (fun z => αE (z, t)) (ball z₀ ρ)) ∧
      (∀ z ∈ ball z₀ ρ, ∀ h : ℝ, |h| ≤ ε → ∀ f : ℝ → E, f 0 = z →
        (∀ τ ∈ uIcc 0 h, HasDerivWithinAt f (v (f τ)) (uIcc 0 h) τ) →
        (∀ τ ∈ uIcc 0 h, f τ ∈ ball z₀ ρ) → ∀ τ ∈ uIcc 0 h, f τ = αE (z, τ)) := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hv
  have hpl0 := hpl 0
  obtain ⟨αE, hα1, hαc⟩ := hpl0.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hr' : (0 : ℝ) < r := NNReal.coe_pos.mpr hr
  have hra : (r : ℝ) ≤ a := by
    have h := hpl0.mul_max_le
    have h2 : (0 : ℝ) ≤ (L : ℝ) * max (0 + ε - 0) (0 - (0 - ε)) :=
      mul_nonneg L.2 (le_max_of_le_left (by linarith))
    have h3 := le_trans h2 h
    linarith
  have ha' : (0 : ℝ) < a := lt_of_lt_of_le hr' hra
  have hK : LipschitzOnWith K v (closedBall z₀ a) :=
    hpl0.lipschitzOnWith 0 ⟨by linarith, by linarith⟩
  set G' := G ∩ ball z₀ a with hG'
  have hG'o : IsOpen G' := hG.inter isOpen_ball
  have hz₀G' : z₀ ∈ G' := ⟨hz₀, mem_ball_self ha'⟩
  have h00 : αE (z₀, 0) = z₀ := (hα1 z₀ (mem_closedBall_self hr'.le)).1
  have hcont : ContinuousAt αE (z₀, 0) :=
    hαc.continuousAt (prod_mem_nhds (closedBall_mem_nhds z₀ hr')
      (Icc_mem_nhds (by linarith) (by linarith)))
  have hpre : αE ⁻¹' G' ∈ 𝓝 (z₀, (0 : ℝ)) :=
    hcont.preimage_mem_nhds (by rw [h00]; exact hG'o.mem_nhds hz₀G')
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hpre
  rw [← ball_prod_same] at hδsub
  refine ⟨min (δ / 2) (ε / 2), lt_min (by linarith) (by linarith), min δ r,
    lt_min hδ hr', αE, ?_⟩
  have hε1 : min (δ / 2) (ε / 2) ≤ δ / 2 := min_le_left _ _
  have hε2 : min (δ / 2) (ε / 2) ≤ ε / 2 := min_le_right _ _
  have hρ1 : min δ r ≤ δ := min_le_left _ _
  have hρ2 : min δ r ≤ (r : ℝ) := min_le_right _ _
  have hball_cb : ∀ z ∈ ball z₀ (min δ r), z ∈ closedBall z₀ r := fun z hz =>
    mem_closedBall.mpr (le_trans (le_of_lt (mem_ball.mp hz)) hρ2)
  -- the main pointwise facts about the flow
  have hmain : ∀ z ∈ ball z₀ (min δ r), αE (z, 0) = z ∧ ∀ t ∈ Icc (-min (δ / 2) (ε / 2))
      (min (δ / 2) (ε / 2)), HasDerivAt (fun s => αE (z, s)) (v (αE (z, t))) t ∧ αE (z, t) ∈ G' := by
    intro z hz
    have hzc := hball_cb z hz
    obtain ⟨hz0, hzd⟩ := hα1 z hzc
    refine ⟨hz0, fun t ht => ⟨?_, ?_⟩⟩
    · have htI : t ∈ Icc (0 - ε) (0 + ε) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      exact (hzd t htI).hasDerivAt (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))
    · apply hδsub
      refine ⟨mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz) hρ1), ?_⟩
      rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
      constructor <;> linarith [ht.1, ht.2]
  refine ⟨fun z hz => ⟨(hmain z hz).1, fun t ht => ⟨((hmain z hz).2 t ht).1,
    ((hmain z hz).2 t ht).2.1⟩⟩, ?_, ?_⟩
  · intro t ht
    have hti : t ∈ Icc (0 - ε) (0 + ε) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact hαc.comp (continuousOn_id.prodMk continuousOn_const)
      (fun z hz => ⟨hball_cb z hz, hti⟩)
  · intro z hz h hh f hf0 hfd hfb τ hτ
    have hsub : uIcc 0 h ⊆ Icc (-min (δ / 2) (ε / 2)) (min (δ / 2) (ε / 2)) := by
      obtain ⟨hh1, hh2⟩ := abs_le.mp hh
      apply uIcc_subset_Icc
      · constructor <;> linarith
      · exact ⟨hh1, hh2⟩
    have hgd : ∀ t ∈ uIcc 0 h, HasDerivAt (fun s => αE (z, s)) (v (αE (z, t))) t :=
      fun t ht => ((hmain z hz).2 t (hsub ht)).1
    have hgs : ∀ t ∈ uIcc 0 h, αE (z, t) ∈ closedBall z₀ a := fun t ht =>
      ball_subset_closedBall ((hmain z hz).2 t (hsub ht)).2.2
    have hfs : ∀ t ∈ uIcc 0 h, f t ∈ closedBall z₀ a := fun t ht =>
      mem_closedBall.mpr (le_trans (le_of_lt (mem_ball.mp (hfb t ht)))
        (le_trans hρ2 hra))
    have hfc : ContinuousOn f (uIcc 0 h) := fun t ht => (hfd t ht).continuousWithinAt
    have hgc : ContinuousOn (fun s => αE (z, s)) (uIcc 0 h) := fun t ht =>
      (hgd t ht).continuousAt.continuousWithinAt
    have hfg0 : f 0 = αE (z, 0) := by rw [hf0, (hmain z hz).1]
    rcases le_or_gt 0 h with h0 | h0
    · rw [uIcc_of_le h0] at hτ hgd hgs hfs hfc hgc hfd
      exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => v)
        (s := fun _ => closedBall z₀ a) (K := K) (fun _ _ => hK) hfc
        (fun t ht => (hfd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ht))
        (fun t ht => hfs t (Ico_subset_Icc_self ht)) hgc
        (fun t ht => (hgd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
        (fun t ht => hgs t (Ico_subset_Icc_self ht)) hfg0 hτ
    · rw [uIcc_of_ge h0.le] at hτ hgd hgs hfs hfc hgc hfd
      exact ODE_solution_unique_of_mem_Icc_left (v := fun _ => v)
        (s := fun _ => closedBall z₀ a) (K := K) (fun _ _ => hK) hfc
        (fun t ht => (hfd t (Ioc_subset_Icc_self ht)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsLE_of_mem ht))
        (fun t ht => hfs t (Ioc_subset_Icc_self ht)) hgc
        (fun t ht => (hgd t (Ioc_subset_Icc_self ht)).hasDerivWithinAt)
        (fun t ht => hgs t (Ioc_subset_Icc_self ht)) hfg0 hτ

end LfODE

/-! ## Transfer between the manifold and a chart -/

section LfManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {v : (x : M) → TangentSpace I x}

set_option backward.isDefEq.respectTransparency false in
/-- A solution of the chart ODE gives a manifold curve with the right derivative. -/
theorem lf_hasMFDerivAt_symm {x₀ : M} {f : ℝ → E} {t : ℝ}
    (hf3 : f t ∈ interior (extChartAt I x₀).target)
    (h : HasDerivAt f (tangentCoordChange I ((extChartAt I x₀).symm (f t)) x₀
      ((extChartAt I x₀).symm (f t)) (v ((extChartAt I x₀).symm (f t)))) t) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I ((extChartAt I x₀).symm ∘ f) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v ((extChartAt I x₀).symm (f t)))) := by
  set xₜ : M := (extChartAt I x₀).symm (f t) with hxt
  have hf3' := interior_subset hf3
  have hft1 := mem_preimage.mp <|
    mem_of_mem_of_subset hf3' (extChartAt I x₀).target_subset_preimage_source
  have hft2 := mem_extChartAt_source (I := I) xₜ
  refine ⟨(continuousAt_extChartAt_symm'' hf3').comp h.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ f) (v xₜ) t
  rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := v xₜ) hft2,
    ← tangentCoordChange_comp (x := x₀) ⟨⟨hft2, hft1⟩, hft2⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ h
  apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
    mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
      subset_trans interior_subset (extChartAt_target_subset_range ..),
      isOpen_interior, hf3⟩
  rw [← (extChartAt I x₀).right_inv hf3']
  exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

set_option backward.isDefEq.respectTransparency false in
/-- A manifold integral curve, read in the chart at an arbitrary base point `x₀`. -/
theorem lf_hasDerivWithinAt_chart {γ : ℝ → M} {s : Set ℝ} {t : ℝ} {x₀ : M}
    (hγ : IsMIntegralCurveOn γ v s) (ht : t ∈ s)
    (hsrc : γ t ∈ (extChartAt I x₀).source) :
    HasDerivWithinAt ((extChartAt I x₀) ∘ γ)
      (tangentCoordChange I (γ t) x₀ (γ t) (v (γ t))) s t := by
  replace hsrc := extChartAt_source I x₀ ▸ hsrc
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← hasMFDerivWithinAt_iff_hasFDerivWithinAt]
  apply (HasMFDerivWithinAt.comp t (hasMFDerivWithinAt_extChartAt (I := I) hsrc) (hγ _ ht)
    (Set.subset_preimage_image _ _)).congr_mfderiv
  rw [ContinuousLinearMap.ext_iff]
  intro a
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
    ← one_apply_eq_self (F := TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) t) a,
    ← ContinuousLinearMap.smulRight_apply,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  rfl

/-- Points of the interior of the chart target are interior points of the manifold. -/
theorem lf_isInteriorPoint_symm {x₀ : M} {z : E}
    (hz : z ∈ interior (extChartAt I x₀).target) :
    I.IsInteriorPoint ((extChartAt I x₀).symm z) := by
  have hz' := interior_subset hz
  have hsrc : (extChartAt I x₀).symm z ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source I]; exact (extChartAt I x₀).map_target hz'
  rw [I.isInteriorPoint_iff_of_mem_atlas (n := 1) one_ne_zero (chart_mem_atlas H x₀) hsrc]
  change extChartAt I x₀ ((extChartAt I x₀).symm z) ∈ interior (extChartAt I x₀).target
  rw [(extChartAt I x₀).right_inv hz']
  exact hz

set_option backward.isDefEq.respectTransparency false in
/-- The local flow near an interior point, for a general model with corners. -/
theorem lf_main [CompleteSpace E] (X : (x : M) → TangentSpace I x) (x₀ : M)
    (hX : ContMDiffAt I I.tangent 1 (fun x => (⟨x, X x⟩ : TangentBundle I M)) x₀)
    (hx₀ : I.IsInteriorPoint x₀) :
    ∃ ε > (0 : ℝ), ∃ O : Set M, IsOpen O ∧ x₀ ∈ O ∧ ∃ α : M → ℝ → M,
      (∀ y ∈ O, α y 0 = y ∧ IsMIntegralCurveOn (α y) X (Icc (-ε) ε) ∧
        ∀ τ ∈ Icc (-ε) ε, I.IsInteriorPoint (α y τ)) ∧
      (∀ τ ∈ Icc (-ε) ε, ContinuousOn (fun y => α y τ) O) ∧
      (∀ y ∈ O, ∀ h : ℝ, |h| ≤ ε → ∀ η : ℝ → M, η 0 = y →
        IsMIntegralCurveOn η X (uIcc 0 h) → (∀ τ ∈ uIcc 0 h, η τ ∈ O) →
        ∀ τ ∈ uIcc 0 h, η τ = α y τ) := by
  set φ := extChartAt I x₀ with hφ
  set v' : E → E := fun z ↦
    tangentCoordChange I (φ.symm z) x₀ (φ.symm z) (X (φ.symm z)) with hv'def
  rw [contMDiffAt_iff] at hX
  obtain ⟨_, hX⟩ := hX
  have hv' : ContDiffAt ℝ 1 v' (φ x₀) :=
    (hX.contDiffAt (range_mem_nhds_isInteriorPoint hx₀)).snd
  have hG : φ x₀ ∈ interior φ.target := (I.isInteriorPoint_iff).mp hx₀
  obtain ⟨ε, hε, ρ, hρ, αE, hflow, hcont, huniq⟩ :=
    lf_ode_localFlow hv' isOpen_interior hG
  refine ⟨ε, hε, φ.source ∩ φ ⁻¹' Metric.ball (φ x₀) ρ,
    isOpen_extChartAt_preimage' x₀ Metric.isOpen_ball,
    ⟨mem_extChartAt_source x₀, Metric.mem_ball_self hρ⟩,
    fun y τ => φ.symm (αE (φ y, τ)), ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨h0, hd⟩ := hflow (φ y) hy.2
    refine ⟨?_, ?_, ?_⟩
    · show φ.symm (αE (φ y, 0)) = y
      rw [h0]; exact φ.left_inv hy.1
    · intro t ht
      obtain ⟨hdt, hGt⟩ := hd t ht
      exact (lf_hasMFDerivAt_symm (v := X) (f := fun s => αE (φ y, s)) hGt hdt).hasMFDerivWithinAt
    · intro t ht
      exact lf_isInteriorPoint_symm (hd t ht).2
  · intro τ hτ
    have h1 : ContinuousOn (fun z => φ.symm (αE (z, τ))) (Metric.ball (φ x₀) ρ) :=
      (continuousOn_extChartAt_symm x₀).comp (hcont τ hτ)
        (fun z hz => interior_subset ((hflow z hz).2 τ hτ).2)
    exact h1.comp ((continuousOn_extChartAt x₀).mono inter_subset_left) (fun y hy => hy.2)
  · intro y hy h hh η hη0 hη hηO τ hτ
    have key := huniq (φ y) hy.2 h hh (φ ∘ η) (by simp [hη0])
      (fun s hs => by
        have hd := lf_hasDerivWithinAt_chart (x₀ := x₀) hη hs (hηO s hs).1
        have e : φ.symm (φ (η s)) = η s := φ.left_inv (hηO s hs).1
        show HasDerivWithinAt _ (tangentCoordChange I (φ.symm (φ (η s))) x₀
          (φ.symm (φ (η s))) (X (φ.symm (φ (η s))))) _ _
        rw [e]; exact hd)
      (fun s hs => (hηO s hs).2) τ hτ
    show η τ = φ.symm (αE (φ y, τ))
    rw [← key]
    exact (φ.left_inv (hηO τ hτ).1).symm

end LfManifold

open AnosovPlugs in
theorem solution
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    (X : (x : M) → TangentSpace I3 x) (hX : IsC1VectorField X)
    (x₀ : M) (hx₀ : I3.IsInteriorPoint x₀) :
    ∃ ε > (0 : ℝ), ∃ O : Set M, IsOpen O ∧ x₀ ∈ O ∧ ∃ α : M → ℝ → M,
      (∀ y ∈ O, α y 0 = y ∧ IsMIntegralCurveOn (α y) X (Icc (-ε) ε) ∧
        ∀ τ ∈ Icc (-ε) ε, I3.IsInteriorPoint (α y τ)) ∧
      (∀ τ ∈ Icc (-ε) ε, ContinuousOn (fun y => α y τ) O) ∧
      (∀ y ∈ O, ∀ h : ℝ, |h| ≤ ε → ∀ η : ℝ → M, η 0 = y →
        IsMIntegralCurveOn η X (uIcc 0 h) → (∀ τ ∈ uIcc 0 h, η τ ∈ O) →
        ∀ τ ∈ uIcc 0 h, η τ = α y τ) := by
  have hX' : ContMDiff I3 I3.tangent 1 (fun x => (⟨x, X x⟩ : TangentBundle I3 M)) := hX
  exact lf_main X x₀ (hX' x₀) hx₀
