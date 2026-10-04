-- Prove2me | solution 1 for AnosovPlugs.mdifferentiableAt_of_comp_embedding
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-03T01:20:00.168033+00:00
-- url     : https://prove2.me/submissions/2c049ae5-fd2e-45a5-b0b8-80f68da5c5ee

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set
open AnosovPlugs

/-- An injective derivative between 3-manifolds sends an interior point to an interior point. -/
theorem interiorPoint_image_of_mfderiv_injective
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (f : M → N) (x : M) (hf : ContMDiffAt I3 I3 1 f x)
    (hinj : Function.Injective (mfderiv I3 I3 f x)) (hx : x ∈ I3.interior M) :
    f x ∈ I3.interior N := by
  have hsurj : Function.Surjective (mfderiv I3 I3 f x) := by
    let L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
      (mfderiv I3 I3 f x).toLinearMap
    exact LinearMap.surjective_of_injective (f := L) (fun a b hab => hinj hab)
  exact (hf.mdifferentiableAt one_ne_zero).isInteriorPoint_of_surjective_mfderiv hsurj hx

/-- The inverse of an embedding with injective derivative at an interior point, whose range is a
neighbourhood of the image point, is differentiable there. -/
theorem mdifferentiableAt_invFun_of_embedding
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    [Nonempty M]
    (i : M → N) (hi : ContMDiff I3 I3 1 i) (hemb : Topology.IsEmbedding i) (x : M)
    (hx : I3.IsInteriorPoint x) (hinj : Function.Injective (mfderiv I3 I3 i x))
    (hnhds : range i ∈ 𝓝 (i x)) :
    MDifferentiableAt I3 I3 (Function.invFun i) (i x) := by
  set j := Function.invFun i with hjdef
  have hleft : Function.LeftInverse j i := Function.leftInverse_invFun hemb.injective
  have hjx : j (i x) = x := hleft x
  have hjcont : ContinuousAt j (i x) := by
    rw [← hemb.isInducing.continuousAt_iff' hnhds]
    have : j ∘ i = id := funext hleft
    rw [this]
    exact continuousAt_id
  have hix : I3.IsInteriorPoint (i x) :=
    interiorPoint_image_of_mfderiv_injective i x (hi x) hinj hx
  set a := extChartAt I3 x x with ha
  set b0 := extChartAt I3 (i x) (i x) with hb0
  let D : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) := mfderiv I3 I3 i x
  have hDinj : Function.Injective D := hinj
  let Dₑ : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (LinearEquiv.ofInjectiveEndo
      (D : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) hDinj).toContinuousLinearEquiv
  have hDₑ : (Dₑ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) = D := by
    ext v
    simp [Dₑ, LinearEquiv.coe_ofInjectiveEndo]
  have hFw : HasFDerivWithinAt (writtenInExtChartAt I3 I3 x i)
      (Dₑ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) (range I3) a := by
    rw [hDₑ]
    exact ((hi x).mdifferentiableAt one_ne_zero).hasMFDerivAt.2
  have hrange : range I3 ∈ 𝓝 a := range_mem_nhds_isInteriorPoint hx
  have hF : HasFDerivAt (writtenInExtChartAt I3 I3 x i)
      (Dₑ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) a :=
    hFw.hasFDerivAt hrange
  set G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    extChartAt I3 x ∘ j ∘ (extChartAt I3 (i x)).symm with hG
  have hGb0 : G b0 = a := by
    simp only [hG, Function.comp_apply, hb0, extChartAt_to_inv, hjx, ha]
  have hc1 : ContinuousAt (extChartAt I3 (i x)).symm b0 := continuousAt_extChartAt_symm (i x)
  have hc2 : ContinuousAt j ((extChartAt I3 (i x)).symm b0) := by
    rw [hb0, extChartAt_to_inv]
    exact hjcont
  have hc12 : ContinuousAt (j ∘ (extChartAt I3 (i x)).symm) b0 := hc2.comp hc1
  have hGcont : ContinuousAt G b0 := by
    have h3 : ContinuousAt (extChartAt I3 x) ((j ∘ (extChartAt I3 (i x)).symm) b0) := by
      rw [Function.comp_apply, hb0, extChartAt_to_inv, hjx]
      exact continuousAt_extChartAt x
    exact h3.comp hc12
  have hFG : ∀ᶠ b in 𝓝 b0, writtenInExtChartAt I3 I3 x i (G b) = b := by
    have ht : (extChartAt I3 (i x)).target ∈ 𝓝 b0 :=
      mem_interior_iff_mem_nhds.1 ((ModelWithCorners.isInteriorPoint_iff (I := I3)).1 hix)
    have h1 : ∀ᶠ b in 𝓝 b0, (extChartAt I3 (i x)).symm b ∈ range i := by
      apply hc1.preimage_mem_nhds
      rw [hb0, extChartAt_to_inv]
      exact hnhds
    have h2 : ∀ᶠ b in 𝓝 b0, j ((extChartAt I3 (i x)).symm b) ∈ (extChartAt I3 x).source := by
      apply hc12.preimage_mem_nhds
      show (extChartAt I3 x).source ∈ 𝓝 (j ((extChartAt I3 (i x)).symm b0))
      rw [hb0, extChartAt_to_inv, hjx]
      exact extChartAt_source_mem_nhds x
    filter_upwards [ht, h1, h2] with b hbt hb1 hb2
    obtain ⟨y, hy⟩ := hb1
    simp only [writtenInExtChartAt, hG, Function.comp_apply]
    rw [PartialEquiv.left_inv _ hb2, ← hy, hleft y, hy, PartialEquiv.right_inv _ hbt]
  have hGd : HasFDerivAt G
      (Dₑ.symm : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) b0 := by
    refine HasFDerivAt.of_local_left_inverse hGcont ?_ hFG
    rw [hGb0]
    exact hF
  rw [mdifferentiableAt_iff]
  refine ⟨hjcont, ?_⟩
  have hW : writtenInExtChartAt I3 I3 (i x) j = G := by
    show extChartAt I3 (j (i x)) ∘ j ∘ (extChartAt I3 (i x)).symm = G
    rw [hjx]
  rw [hW]
  exact hGd.differentiableAt.differentiableWithinAt

theorem solution
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    {P : Type} [TopologicalSpace P] [ChartedSpace (EuclideanHalfSpace 3) P] [IsManifold I3 ∞ P]
    (i : M → N) (hi : ContMDiff I3 I3 1 i) (hemb : Topology.IsEmbedding i) (x : M)
    (hx : I3.IsInteriorPoint x) (hinj : Function.Injective (mfderiv I3 I3 i x))
    (hnhds : range i ∈ 𝓝 (i x)) (f : N → P) (hf : MDifferentiableAt I3 I3 (f ∘ i) x) :
    MDifferentiableAt I3 I3 f (i x) := by
  have : Nonempty M := ⟨x⟩
  have hj := mdifferentiableAt_invFun_of_embedding i hi hemb x hx hinj hnhds
  have hleft : Function.LeftInverse (Function.invFun i) i :=
    Function.leftInverse_invFun hemb.injective
  have hf' : MDifferentiableAt I3 I3 (f ∘ i) (Function.invFun i (i x)) := by
    rw [hleft x]
    exact hf
  have hcomp : MDifferentiableAt I3 I3 ((f ∘ i) ∘ Function.invFun i) (i x) := hf'.comp (i x) hj
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hnhds] with w hw
  obtain ⟨y, rfl⟩ := hw
  simp only [Function.comp_apply, hleft y]
