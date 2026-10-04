-- Prove2me | solution 1 for AnosovPlugs.integralCurveOn_uIcc_unique
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-03T20:58:50.427387+00:00
-- url     : https://prove2.me/submissions/a957a282-975e-42b5-b5b1-822125934084

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set AnosovPlugs

/-! ## A manifold integral curve read in a chart at an arbitrary base point -/

section UqManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {v : (x : M) → TangentSpace I x}

set_option backward.isDefEq.respectTransparency false in
/-- A manifold integral curve, read in the chart at an arbitrary base point `x₀`. -/
theorem uq_chart {γ : ℝ → M} {s : Set ℝ} {t : ℝ} {x₀ : M}
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

end UqManifold

/-! ## The chart field is Lipschitz near the base point, within the model range -/

set_option backward.isDefEq.respectTransparency false in
theorem uq_lip
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    (X : (x : M) → TangentSpace I3 x) (hX : IsC1VectorField X) (x₀ : M) :
    ∃ K : NNReal, ∃ r > (0 : ℝ), LipschitzOnWith K
      (fun z => tangentCoordChange I3 ((extChartAt I3 x₀).symm z) x₀
        ((extChartAt I3 x₀).symm z) (X ((extChartAt I3 x₀).symm z)))
      (Metric.ball (extChartAt I3 x₀ x₀) r ∩ range I3) := by
  have hX' : ContMDiff I3 I3.tangent 1 (fun x => (⟨x, X x⟩ : TangentBundle I3 M)) := hX
  set φ := extChartAt I3 x₀ with hφ
  set v' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) := fun z ↦
    tangentCoordChange I3 (φ.symm z) x₀ (φ.symm z) (X (φ.symm z)) with hv'def
  have h := hX' x₀
  rw [contMDiffAt_iff] at h
  obtain ⟨_, h⟩ := h
  have hv' : ContDiffWithinAt ℝ 1 v' (range I3) (φ x₀) := h.snd
  obtain ⟨K, t, ht, hK⟩ := hv'.exists_lipschitzOnWith I3.convex_range
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhdsWithin_iff.1 ht
  exact ⟨K, r, hr, hK.mono hsub⟩

/-! ## Local agreement near a time where two integral curves agree -/

set_option backward.isDefEq.respectTransparency false in
theorem uq_local
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    (X : (x : M) → TangentSpace I3 x) (hX : IsC1VectorField X) {γ γ' : ℝ → M} {a b : ℝ}
    (hγ : IsMIntegralCurveOn γ X (uIcc a b)) (hγ' : IsMIntegralCurveOn γ' X (uIcc a b))
    {s₀ : ℝ} (hs₀ : s₀ ∈ uIcc a b) (h : γ' s₀ = γ s₀) :
    ∃ ε > (0 : ℝ), ∀ s ∈ uIcc a b, dist s s₀ < ε → γ' s = γ s := by
  set x₀ := γ s₀ with hx₀
  obtain ⟨K, r, hr, hK⟩ := uq_lip X hX x₀
  set φ := extChartAt I3 x₀ with hφ
  set v' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) := fun z ↦
    tangentCoordChange I3 (φ.symm z) x₀ (φ.symm z) (X (φ.symm z)) with hv'def
  set S : Set (EuclideanSpace ℝ (Fin 3)) := Metric.ball (φ x₀) r ∩ range I3 with hS
  set O : Set M := φ.source ∩ φ ⁻¹' Metric.ball (φ x₀) r with hO
  have hOo : IsOpen O := isOpen_extChartAt_preimage' x₀ Metric.isOpen_ball
  have hx₀O : x₀ ∈ O := ⟨mem_extChartAt_source x₀, Metric.mem_ball_self hr⟩
  have h1 : γ ⁻¹' O ∈ 𝓝[uIcc a b] s₀ := hγ.continuousWithinAt hs₀ (hOo.mem_nhds hx₀O)
  have h2 : γ' ⁻¹' O ∈ 𝓝[uIcc a b] s₀ :=
    hγ'.continuousWithinAt hs₀ (by rw [h]; exact hOo.mem_nhds hx₀O)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 (Filter.inter_mem h1 h2)
  refine ⟨ε, hε, ?_⟩
  set J : Set ℝ := uIcc a b ∩ Metric.ball s₀ ε with hJ
  have hJS : J ⊆ uIcc a b := inter_subset_left
  have hs₀J : s₀ ∈ J := ⟨hs₀, Metric.mem_ball_self hε⟩
  have hJord : J.OrdConnected := by
    rw [hJ, Real.ball_eq_Ioo]; exact OrdConnected.inter ordConnected_uIcc ordConnected_Ioo
  have hJO : ∀ u ∈ J, γ u ∈ O ∧ γ' u ∈ O := fun u hu => hball ⟨hu.2, hu.1⟩
  intro s hs hds
  have hsJ : s ∈ J := ⟨hs, hds⟩
  have hsub : uIcc s₀ s ⊆ J := hJord.uIcc_subset hs₀J hsJ
  -- facts about a curve that stays in `O` on `uIcc s₀ s`
  have hd : ∀ c : ℝ → M, IsMIntegralCurveOn c X (uIcc a b) → (∀ u ∈ uIcc s₀ s, c u ∈ O) →
      ∀ u ∈ uIcc s₀ s, HasDerivWithinAt (φ ∘ c) (v' ((φ ∘ c) u)) (uIcc s₀ s) u := by
    intro c hc hcO u hu
    have hdu := (uq_chart (x₀ := x₀) hc (hJS (hsub hu)) (hcO u hu).1).mono
      (fun w hw => hJS (hsub hw))
    have e : φ.symm (φ (c u)) = c u := φ.left_inv (hcO u hu).1
    show HasDerivWithinAt _ (tangentCoordChange I3 (φ.symm (φ (c u))) x₀
      (φ.symm (φ (c u))) (X (φ.symm (φ (c u))))) _ _
    rw [e]; exact hdu
  have hm : ∀ c : ℝ → M, (∀ u ∈ uIcc s₀ s, c u ∈ O) → ∀ u ∈ uIcc s₀ s, (φ ∘ c) u ∈ S :=
    fun c hcO u hu => ⟨(hcO u hu).2,
      extChartAt_target_subset_range x₀ (φ.map_source (hcO u hu).1)⟩
  have hc : ∀ c : ℝ → M, IsMIntegralCurveOn c X (uIcc a b) → (∀ u ∈ uIcc s₀ s, c u ∈ O) →
      ContinuousOn (φ ∘ c) (uIcc s₀ s) :=
    fun c hcc hcO => (continuousOn_extChartAt x₀).comp
      (hcc.continuousOn.mono (fun w hw => hJS (hsub hw))) (fun u hu => (hcO u hu).1)
  have hγO : ∀ u ∈ uIcc s₀ s, γ u ∈ O := fun u hu => (hJO u (hsub hu)).1
  have hγ'O : ∀ u ∈ uIcc s₀ s, γ' u ∈ O := fun u hu => (hJO u (hsub hu)).2
  have hfd := hd γ' hγ' hγ'O
  have hgd := hd γ hγ hγO
  have hfs := hm γ' hγ'O
  have hgs := hm γ hγO
  have hfc := hc γ' hγ' hγ'O
  have hgc := hc γ hγ hγO
  have h00 : (φ ∘ γ') s₀ = (φ ∘ γ) s₀ := by
    show φ (γ' s₀) = φ (γ s₀); rw [h]
  have key : (φ ∘ γ') s = (φ ∘ γ) s := by
    rcases le_total s₀ s with hle | hle
    · rw [uIcc_of_le hle] at hfd hgd hfs hgs hfc hgc
      exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => v')
        (s := fun _ => S) (K := K) (fun _ _ => hK) hfc
        (fun t ht => (hfd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ht))
        (fun t ht => hfs t (Ico_subset_Icc_self ht)) hgc
        (fun t ht => (hgd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ht))
        (fun t ht => hgs t (Ico_subset_Icc_self ht)) h00 (right_mem_Icc.2 hle)
    · rw [uIcc_of_ge hle] at hfd hgd hfs hgs hfc hgc
      exact ODE_solution_unique_of_mem_Icc_left (v := fun _ => v')
        (s := fun _ => S) (K := K) (fun _ _ => hK) hfc
        (fun t ht => (hfd t (Ioc_subset_Icc_self ht)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsLE_of_mem ht))
        (fun t ht => hfs t (Ioc_subset_Icc_self ht)) hgc
        (fun t ht => (hgd t (Ioc_subset_Icc_self ht)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsLE_of_mem ht))
        (fun t ht => hgs t (Ioc_subset_Icc_self ht)) h00 (left_mem_Icc.2 hle)
  exact φ.injOn (hJO s hsJ).2.1 (hJO s hsJ).1.1 key

/-! ## Uniqueness on a closed interval with an arbitrary base time -/

theorem uq_gen
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    [T2Space M]
    (X : (x : M) → TangentSpace I3 x) (hX : IsC1VectorField X) (γ γ' : ℝ → M) (a b : ℝ)
    (hγ : IsMIntegralCurveOn γ X (uIcc a b)) (hγ' : IsMIntegralCurveOn γ' X (uIcc a b))
    (hab : γ' a = γ a) :
    ∀ s ∈ uIcc a b, γ' s = γ s := by
  have : PreconnectedSpace (uIcc a b) := Subtype.preconnectedSpace isPreconnected_uIcc
  set U : Set (uIcc a b) := {x | γ' x = γ x} with hU
  have hclosed : IsClosed U :=
    isClosed_eq hγ'.continuousOn.domRestrict hγ.continuousOn.domRestrict
  have hopen : IsOpen U := by
    rw [Metric.isOpen_iff]
    rintro ⟨s₀, hs₀⟩ hx
    obtain ⟨ε, hε, hloc⟩ := uq_local X hX hγ hγ' hs₀ hx
    refine ⟨ε, hε, ?_⟩
    rintro ⟨s, hs⟩ hds
    exact hloc s hs hds
  have huniv : U = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨a, left_mem_uIcc⟩, hab⟩
  intro s hs
  have : (⟨s, hs⟩ : uIcc a b) ∈ U := huniv ▸ mem_univ _
  exact this

theorem solution
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    [T2Space M]
    (X : (x : M) → TangentSpace I3 x) (hX : IsC1VectorField X) (γ γ' : ℝ → M) (t : ℝ)
    (hγ : IsMIntegralCurveOn γ X (uIcc 0 t)) (hγ' : IsMIntegralCurveOn γ' X (uIcc 0 t))
    (h0 : γ' 0 = γ 0) :
    ∀ s ∈ uIcc 0 t, γ' s = γ s :=
  uq_gen X hX γ γ' 0 t hγ hγ' h0
