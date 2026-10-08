-- Prove2me | solution 1 for AnosovPlugs.localSteps_of_embedding
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-04T20:36:37.103982+00:00
-- url     : https://prove2.me/submissions/34a30549-7495-45ec-94bb-bfb4b1344f05

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set AnosovPlugs

/-- The push-forward of an integral curve of `X` by `i` is an integral curve of `Z`. -/
theorem tr_isMIntegralCurveOn_comp
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    {X : (x : M) → TangentSpace I3 x} {Z : (w : N) → TangentSpace I3 w} {i : M → N}
    (hc : ContMDiff I3 I3 1 i) (hZ : ∀ x, mfderiv I3 I3 i x (X x) = Z (i x))
    (δ : ℝ → M) (s : Set ℝ) (hδ : IsMIntegralCurveOn δ X s) :
    IsMIntegralCurveOn (i ∘ δ) Z s := by
  intro t ht
  have hi : HasMFDerivAt I3 I3 i (δ t) (mfderiv I3 I3 i (δ t)) :=
    (hc.mdifferentiableAt one_ne_zero).hasMFDerivAt
  refine (hi.comp_hasMFDerivWithinAt t (hδ t ht)).congr_mfderiv ?_
  refine ContinuousLinearMap.ext_ring ?_
  change mfderiv I3 I3 i (δ t) ((1 : ℝ) • X (δ t)) = (1 : ℝ) • Z (i (δ t))
  rw [one_smul, one_smul]
  exact hZ (δ t)

/-- A `C¹` map with injective derivative at an interior point has a `C¹` local right inverse. -/
theorem tr_localRightInverse
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (i : M → N) (hi : ContMDiff I3 I3 1 i) (x : M) (hx : I3.IsInteriorPoint x)
    (hinj : Function.Injective (mfderiv I3 I3 i x)) (O : Set M) (hO : O ∈ 𝓝 x) :
    ∃ O' : Set N, IsOpen O' ∧ i x ∈ O' ∧ ∃ j : N → M, ContMDiffOn I3 I3 1 j O' ∧
      MapsTo j O' O ∧ ∀ y ∈ O', i (j y) = y := by
  set φ := extChartAt I3 x with hφ
  set ψ := extChartAt I3 (i x) with hψ
  set a := φ x with ha
  set F := writtenInExtChartAt I3 I3 x i with hFdef
  let D : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) := mfderiv I3 I3 i x
  have hDinj : Function.Injective D := hinj
  let Dₑ : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (LinearEquiv.ofInjectiveEndo
      (D : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) hDinj).toContinuousLinearEquiv
  have hDₑ : (Dₑ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) = D := by
    ext v
    simp [Dₑ, LinearEquiv.coe_ofInjectiveEndo]
  have hrange : range I3 ∈ 𝓝 a := range_mem_nhds_isInteriorPoint hx
  have hcd : ContDiffWithinAt ℝ 1 F (range I3) a := (contMDiffAt_iff.1 (hi x)).2
  have hcda : ContDiffAt ℝ 1 F a := hcd.contDiffAt hrange
  have hFw : HasFDerivWithinAt F D (range I3) a :=
    ((hi x).mdifferentiableAt one_ne_zero).hasMFDerivAt.2
  have hF : HasFDerivAt F D a := hFw.hasFDerivAt hrange
  have hF' : HasFDerivAt F (Dₑ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) a := by
    rw [hDₑ]; exact hF
  have hstrict := hcda.hasStrictFDerivAt' hF' one_ne_zero
  set G := hcda.localInverse hF' one_ne_zero with hGdef
  have hGC : ContDiffAt ℝ 1 G (F a) := hcda.to_localInverse hF' one_ne_zero
  have hGa : G (F a) = a := hcda.localInverse_apply_image hF' one_ne_zero
  have hGcont : ContinuousAt G (F a) := hstrict.localInverse_continuousAt
  have hright : ∀ᶠ b in 𝓝 (F a), F (G b) = b := hstrict.eventually_right_inverse
  have hFa : F a = ψ (i x) := by
    simp only [hFdef, writtenInExtChartAt, Function.comp_apply, ha, hφ, extChartAt_to_inv]
    rfl
  have hint : a ∈ interior φ.target := (I3.isInteriorPoint_iff).mp hx
  have hGint : ∀ᶠ b in 𝓝 (F a), G b ∈ interior φ.target := by
    have : Filter.Tendsto G (𝓝 (F a)) (𝓝 a) := by
      have h := hGcont.tendsto; rwa [hGa] at h
    exact this (isOpen_interior.mem_nhds hint)
  have hsymm : φ.symm a = x := φ.left_inv (mem_extChartAt_source x)
  have hOS : O ∩ i ⁻¹' ψ.source ∈ 𝓝 x :=
    Filter.inter_mem hO ((hi x).continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (i x)))
  have hGO : ∀ᶠ b in 𝓝 (F a), φ.symm (G b) ∈ O ∩ i ⁻¹' ψ.source := by
    have h1 : Filter.Tendsto φ.symm (𝓝 a) (𝓝 x) := hsymm ▸ (continuousAt_extChartAt_symm x).tendsto
    have h2 : Filter.Tendsto G (𝓝 (F a)) (𝓝 a) := by
      have h := hGcont.tendsto; rwa [hGa] at h
    exact (h1.comp h2) hOS
  have hall : ∀ᶠ b in 𝓝 (F a), F (G b) = b ∧ G b ∈ interior φ.target ∧
      φ.symm (G b) ∈ O ∩ i ⁻¹' ψ.source ∧ ContDiffAt ℝ 1 G b :=
    hright.and (hGint.and (hGO.and (hGC.eventually (by simp))))
  obtain ⟨T, hTsub, hTopen, hTmem⟩ := mem_nhds_iff.mp hall
  refine ⟨ψ.source ∩ ψ ⁻¹' T, isOpen_extChartAt_preimage' (i x) hTopen,
    ⟨mem_extChartAt_source (i x), show ψ (i x) ∈ T from hFa ▸ hTmem⟩, φ.symm ∘ G ∘ ψ, ?_, ?_, ?_⟩
  · have hψsrc : ψ.source = (chartAt (EuclideanHalfSpace 3) (i x)).source :=
      extChartAt_source I3 (i x)
    have h1 : ContMDiffOn I3 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 1 ψ (ψ.source ∩ ψ ⁻¹' T) :=
      (contMDiffOn_extChartAt (I := I3) (x := i x) (n := 1)).mono
        (fun y hy => hψsrc ▸ hy.1)
    have h2 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 1 G T :=
      ContDiffOn.contMDiffOn (fun b hb => (hTsub hb).2.2.2.contDiffWithinAt)
    have h3 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) I3 1 φ.symm φ.target :=
      contMDiffOn_extChartAt_symm x
    exact h3.comp (h2.comp h1 (fun y hy => hy.2))
      (fun y hy => interior_subset (s := φ.target) (hTsub hy.2).2.1)
  · intro y hy
    exact (hTsub hy.2).2.2.1.1
  · intro y hy
    have hP := hTsub hy.2
    have e1 : ψ (i (φ.symm (G (ψ y)))) = ψ y := hP.1
    exact ψ.injOn hP.2.2.1.2 hy.1 e1

theorem solution
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (X : (x : M) → TangentSpace I3 x) (Z : (w : N) → TangentSpace I3 w) (i : M → N)
    (hi : ContMDiff I3 I3 1 i)
    (hZ : ∀ x, mfderiv I3 I3 i x (X x) = Z (i x))
    (x₀ : M) (hx₀ : I3.IsInteriorPoint x₀) (hinj : Function.Injective (mfderiv I3 I3 i x₀))
    (hflow : ∃ ε > (0 : ℝ), ∃ O : Set M, IsOpen O ∧ x₀ ∈ O ∧ ∃ α : M → ℝ → M,
        (∀ y ∈ O, α y 0 = y ∧ IsMIntegralCurveOn (α y) X (Icc (-ε) ε) ∧
          ∀ τ ∈ Icc (-ε) ε, I3.IsInteriorPoint (α y τ)) ∧
        ContMDiffOn (I3.prod 𝓘(ℝ, ℝ)) I3 1 (fun p : M × ℝ => α p.1 p.2) (O ×ˢ Ioo (-ε) ε) ∧
        (∀ y ∈ O, ∀ h : ℝ, |h| ≤ ε → ∀ η : ℝ → M, η 0 = y →
          IsMIntegralCurveOn η X (uIcc 0 h) → (∀ τ ∈ uIcc 0 h, η τ ∈ O) →
          ∀ τ ∈ uIcc 0 h, η τ = α y τ)) :
    ∃ ε > (0 : ℝ), ∃ O : Set N, IsOpen O ∧ i x₀ ∈ O ∧ ∀ h : ℝ, |h| ≤ ε → ∃ f : N → N,
      ContMDiffOn I3 I3 1 f O ∧
      ∀ y ∈ O, ∃ η : ℝ → N, η 0 = y ∧ IsMIntegralCurveOn η Z (uIcc 0 h) ∧ η h = f y := by
  obtain ⟨ε, hε, O, hO, hx₀O, α, hα, hαC, -⟩ := hflow
  obtain ⟨O', hO', hiO', j, hjC, hjO, hij⟩ :=
    tr_localRightInverse i hi x₀ hx₀ hinj O (hO.mem_nhds hx₀O)
  refine ⟨ε / 2, by positivity, O', hO', hiO', fun h hh => ?_⟩
  obtain ⟨hh1, hh2⟩ := abs_le.mp hh
  refine ⟨fun y => i (α (j y) h), ?_, fun y hy => ⟨i ∘ α (j y), ?_, ?_, rfl⟩⟩
  · have hp : ContMDiffOn I3 (I3.prod 𝓘(ℝ, ℝ)) 1 (fun y => (j y, h)) O' :=
      hjC.prodMk contMDiffOn_const
    have hc := hαC.comp hp (fun y hy => ⟨hjO hy, by constructor <;> linarith⟩)
    exact hi.comp_contMDiffOn hc
  · show i (α (j y) 0) = y
    rw [(hα (j y) (hjO hy)).1, hij y hy]
  · refine tr_isMIntegralCurveOn_comp hi hZ _ _ ((hα (j y) (hjO hy)).2.1.mono ?_)
    exact uIcc_subset_Icc ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
