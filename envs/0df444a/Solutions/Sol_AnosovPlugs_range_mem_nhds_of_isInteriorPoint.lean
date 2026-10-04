-- Prove2me | solution 1 for AnosovPlugs.range_mem_nhds_of_isInteriorPoint
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-03T09:01:18.278761+00:00
-- url     : https://prove2.me/submissions/41824763-516c-4d8f-b462-4761e76c5a6f

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set
open AnosovPlugs

theorem solution
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (i : M → N) (hi : ContMDiff I3 I3 1 i) (x : M) (hx : I3.IsInteriorPoint x)
    (hinj : Function.Injective (mfderiv I3 I3 i x)) :
    range i ∈ 𝓝 (i x) := by
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
  have hstrict : HasStrictFDerivAt F (fderiv ℝ F a) a := hcda.hasStrictFDerivAt one_ne_zero
  have hFw : HasFDerivWithinAt F D (range I3) a :=
    ((hi x).mdifferentiableAt one_ne_zero).hasMFDerivAt.2
  have hF : HasFDerivAt F D a := hFw.hasFDerivAt hrange
  have heq : fderiv ℝ F a = D := hF.fderiv
  have hstrict' : HasStrictFDerivAt F
      (Dₑ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) a := by
    rw [hDₑ, ← heq]; exact hstrict
  have hmap : Filter.map F (𝓝 a) = 𝓝 (F a) := hstrict'.map_nhds_eq_of_equiv
  have hFa : F a = ψ (i x) := by
    simp only [hFdef, writtenInExtChartAt, Function.comp_apply, ha, hφ, extChartAt_to_inv]
    rfl
  set S := φ.source ∩ i ⁻¹' ψ.source with hS
  have hSn : S ∈ 𝓝 x :=
    Filter.inter_mem (extChartAt_source_mem_nhds x)
      ((hi x).continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (i x)))
  have hφS : φ '' S ∈ 𝓝 a :=
    extChartAt_image_nhds_mem_nhds_of_mem_interior_range (mem_extChartAt_source x) hx hSn
  have hFS : F '' (φ '' S) ∈ 𝓝 (ψ (i x)) := by
    rw [← hFa, ← hmap]; exact Filter.image_mem_map hφS
  have hsub : F '' (φ '' S) ⊆ ψ '' (i '' S) := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨i y, ⟨y, hy, rfl⟩, ?_⟩
    simp only [hFdef, writtenInExtChartAt, Function.comp_apply]
    rw [PartialEquiv.left_inv _ hy.1]
  have h1 : ψ ⁻¹' (ψ '' (i '' S)) ∈ 𝓝 (i x) :=
    (continuousAt_extChartAt (i x)).preimage_mem_nhds (Filter.mem_of_superset hFS hsub)
  refine Filter.mem_of_superset (Filter.inter_mem h1 (extChartAt_source_mem_nhds (I := I3) (i x))) ?_
  rintro w ⟨⟨_, ⟨y, hy, rfl⟩, hwy⟩, hw⟩
  exact ⟨y, (extChartAt I3 (i x)).injOn hy.2 hw hwy⟩
