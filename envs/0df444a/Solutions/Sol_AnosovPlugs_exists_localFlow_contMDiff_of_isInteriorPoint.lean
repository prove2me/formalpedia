-- Prove2me | solution 1 for AnosovPlugs.exists_localFlow_contMDiff_of_isInteriorPoint
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-04T09:37:15.693657+00:00
-- url     : https://prove2.me/submissions/4511b238-bdde-4429-b967-658ee5f2204e

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing
import Theorems.Thm_AnosovPlugs_exists_localFlow_contDiffOn_of_contDiffAt

open scoped Manifold ContDiff Topology
open Set

/-! ## Transfer between the manifold and a chart -/

section LfManifold

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {v : (x : M) → TangentSpace I x}

set_option backward.isDefEq.respectTransparency false in
/-- A solution of the chart ODE gives a manifold curve with the right derivative. -/
theorem lm_hasMFDerivAt_symm {x₀ : M} {f : ℝ → E} {t : ℝ}
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
theorem lm_hasDerivWithinAt_chart {γ : ℝ → M} {s : Set ℝ} {t : ℝ} {x₀ : M}
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
theorem lm_isInteriorPoint_symm {x₀ : M} {z : E}
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
/-- The local `C¹` flow near an interior point, for a general model with corners. -/
theorem lm_main [FiniteDimensional ℝ E] (X : (x : M) → TangentSpace I x) (x₀ : M)
    (hX : ContMDiffAt I I.tangent 1 (fun x => (⟨x, X x⟩ : TangentBundle I M)) x₀)
    (hx₀ : I.IsInteriorPoint x₀) :
    ∃ ε > (0 : ℝ), ∃ O : Set M, IsOpen O ∧ x₀ ∈ O ∧ ∃ α : M → ℝ → M,
      (∀ y ∈ O, α y 0 = y ∧ IsMIntegralCurveOn (α y) X (Icc (-ε) ε) ∧
        ∀ τ ∈ Icc (-ε) ε, I.IsInteriorPoint (α y τ)) ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 1 (fun p : M × ℝ => α p.1 p.2) (O ×ˢ Ioo (-ε) ε) ∧
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
  obtain ⟨ε, hε, ρ, hρ, αE, hflow, hαC, huniq⟩ :=
    AnosovPlugs.exists_localFlow_contDiffOn_of_contDiffAt hv' isOpen_interior hG
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
      exact (lm_hasMFDerivAt_symm (v := X) (f := fun s => αE (φ y, s)) hGt hdt).hasMFDerivWithinAt
    · intro t ht
      exact lm_isInteriorPoint_symm (hd t ht).2
  · have hsrc : φ.source = (chartAt H x₀).source := extChartAt_source I x₀
    have h1 : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) 1 (φ ∘ Prod.fst)
        ((φ.source ∩ φ ⁻¹' Metric.ball (φ x₀) ρ) ×ˢ Ioo (-ε) ε) :=
      (contMDiffOn_extChartAt (I := I) (x := x₀) (n := 1)).comp contMDiffOn_fst
        (fun p hp => hsrc ▸ hp.1.1)
    have h2 : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 1 (Prod.snd : M × ℝ → ℝ)
        ((φ.source ∩ φ ⁻¹' Metric.ball (φ x₀) ρ) ×ˢ Ioo (-ε) ε) := contMDiffOn_snd
    have h12 := h1.prodMk_space h2
    have h3 : ContMDiffOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) 1 αE (Metric.ball (φ x₀) ρ ×ˢ Ioo (-ε) ε) :=
      hαC.contMDiffOn
    have h4 : ContMDiffOn 𝓘(ℝ, E) I 1 φ.symm φ.target := contMDiffOn_extChartAt_symm x₀
    exact h4.comp (h3.comp h12 (fun p hp => ⟨hp.1.2, hp.2⟩))
      (fun p hp => interior_subset (s := φ.target) ((hflow (φ p.1) hp.1.2).2 p.2 (Ioo_subset_Icc_self hp.2)).2)
  · intro y hy h hh η hη0 hη hηO τ hτ
    have key := huniq (φ y) hy.2 h hh (φ ∘ η) (by simp [hη0])
      (fun s hs => by
        have hd := lm_hasDerivWithinAt_chart (x₀ := x₀) hη hs (hηO s hs).1
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
      ContMDiffOn (I3.prod 𝓘(ℝ, ℝ)) I3 1 (fun p : M × ℝ => α p.1 p.2) (O ×ˢ Ioo (-ε) ε) ∧
      (∀ y ∈ O, ∀ h : ℝ, |h| ≤ ε → ∀ η : ℝ → M, η 0 = y →
        IsMIntegralCurveOn η X (uIcc 0 h) → (∀ τ ∈ uIcc 0 h, η τ ∈ O) →
        ∀ τ ∈ uIcc 0 h, η τ = α y τ) := by
  have hX' : ContMDiff I3 I3.tangent 1 (fun x => (⟨x, X x⟩ : TangentBundle I3 M)) := hX
  exact lm_main X x₀ (hX' x₀) hx₀
