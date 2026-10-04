-- Prove2me | solution 1 for AnosovPlugs.plugGluing_local_conjugacy
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-03T09:00:56.494763+00:00
-- url     : https://prove2.me/submissions/4947fb06-a3f6-41d0-81fc-c095e316026f

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing
import Theorems.Thm_AnosovPlugs_range_mem_nhds_of_isInteriorPoint
import Theorems.Thm_AnosovPlugs_exists_integralCurveOn_nhds
import Theorems.Thm_AnosovPlugs_isMIntegralCurveOn_uIcc_eq
import Theorems.Thm_AnosovPlugs_integralCurveOn_eq_comp_of_embedding
import Theorems.Thm_AnosovPlugs_normalCoord_nonneg_of_hasMFDerivWithinAt

open scoped Manifold ContDiff Topology
open Set
open AnosovPlugs

/-- Every point of the maximal invariant set of a plug is an interior point. -/
theorem lc_maxInvSet_isInteriorPoint
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {X : (x : M) → TangentSpace I3 x} (hX : IsPlug X) :
    ∀ x ∈ maxInvSet X, I3.IsInteriorPoint x := by
  intro x hx
  obtain ⟨γ, rfl, hγ⟩ := hx
  rcases I3.isInteriorPoint_or_isBoundaryPoint (γ 0) with h | h
  · exact h
  · exfalso
    have hb : γ 0 ∈ I3.boundary M := h
    have hd : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I3 γ univ 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ 0))) := (hγ 0).hasMFDerivWithinAt
    have h1 := normalCoord_nonneg_of_hasMFDerivWithinAt γ univ 0 (X (γ 0)) hd hb 1
      (by rw [posTangentConeAt_univ]; exact mem_univ _)
    have h2 := normalCoord_nonneg_of_hasMFDerivWithinAt γ univ 0 (X (γ 0)) hd hb (-1)
      (by rw [posTangentConeAt_univ]; exact mem_univ _)
    exact hX.2.2 (γ 0) hb (by linarith)

/-- Points on a complete integral curve lie in the maximal invariant set. -/
theorem lc_mem_maxInvSet_of_isMIntegralCurve
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {X : (x : M) → TangentSpace I3 x} {γ : ℝ → M} (hγ : IsMIntegralCurve γ X) (s : ℝ) :
    γ s ∈ maxInvSet X :=
  ⟨γ ∘ (· + s), by simp, hγ.comp_add s⟩

/-- The image of an integral curve on a set under a `C¹` map that sends one vector field to
another is an integral curve on the same set. -/
theorem lc_isMIntegralCurveOn_comp
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

/-- One side of the local conjugacy: near the maximal invariant set of a plug, an embedding
that sends `X` to `Z` is open and conjugates the partial flows. -/
theorem lc_side
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    [T2Space M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    [T2Space N]
    (X : (x : M) → TangentSpace I3 x) (Z : (w : N) → TangentSpace I3 w) (i : M → N)
    (hX : IsPlug X) (hi : ContMDiff I3 I3 1 i) (hemb : Topology.IsEmbedding i)
    (hinj : ∀ x, Function.Injective (mfderiv I3 I3 i x))
    (hZ : ∀ x, mfderiv I3 I3 i x (X x) = Z (i x)) :
    ∀ x ∈ maxInvSet X, range i ∈ 𝓝 (i x) ∧
      ∀ t : ℝ, ∀ᶠ y in 𝓝 x, flowMap Z t (i y) = i (flowMap X t y) := by
  intro x hx
  have hxint := lc_maxInvSet_isInteriorPoint hX x hx
  obtain ⟨γ, rfl, hγ⟩ := hx
  refine ⟨range_mem_nhds_of_isInteriorPoint i hi (γ 0) hxint (hinj (γ 0)), ?_⟩
  intro t
  have hint' : ∀ s ∈ uIcc 0 t, I3.IsInteriorPoint (γ s) := fun s _ =>
    lc_maxInvSet_isInteriorPoint hX _ (lc_mem_maxInvSet_of_isMIntegralCurve hγ s)
  have hev := exists_integralCurveOn_nhds X hX.1 γ t (hγ.isMIntegralCurveOn _) hint'
  filter_upwards [hev] with y hy
  obtain ⟨γy, hy0, hγy, hinty⟩ := hy
  -- the `X` side
  have hdefX : FlowDefined X y t := ⟨γy, hy0, hγy⟩
  have hXeq : flowMap X t y = γy t := by
    rw [flowMap, dif_pos hdefX]
    obtain ⟨hc0, hcγ⟩ := hdefX.choose_spec
    exact isMIntegralCurveOn_uIcc_eq X hX.1 γy _ t hγy hinty hcγ (hc0.trans hy0.symm) t
      right_mem_uIcc
  -- the `Z` side
  have hZc : IsMIntegralCurveOn (i ∘ γy) Z (uIcc 0 t) :=
    lc_isMIntegralCurveOn_comp hi hZ γy _ hγy
  have hdefZ : FlowDefined Z (i y) t := ⟨i ∘ γy, by simp [hy0], hZc⟩
  have hZeq : flowMap Z t (i y) = i (γy t) := by
    rw [flowMap, dif_pos hdefZ]
    obtain ⟨hz0, hzγ⟩ := hdefZ.choose_spec
    exact integralCurveOn_eq_comp_of_embedding X Z i hX.1 hi hemb hinj hZ γy t hγy hinty _ hzγ
      (hz0.trans (by simp [hy0])) t right_mem_uIcc
  rw [hZeq, hXeq]

theorem solution
    {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U] [T2Space U] [CompactSpace U]
    {V : Type} [TopologicalSpace V] [ChartedSpace (EuclideanHalfSpace 3) V]
    [IsManifold I3 ∞ V] [T2Space V] [CompactSpace V]
    {W : Type} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 3) W]
    [IsManifold I3 ∞ W] [T2Space W] [CompactSpace W]
    (X : (x : U) → TangentSpace I3 x) (Y : (y : V) → TangentSpace I3 y)
    (hX : IsPlug X) (hY : IsPlug Y)
    (Tout : Set U) (Tin : Set V) (hTout : IsUnionOfComponents Tout (outBoundary X))
    (hTin : IsUnionOfComponents Tin (inBoundary Y)) (φ : U → V)
    (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W)
    (hglue : IsPlugGluing X Y Tout φ Z iU iV) :
    (∀ x ∈ maxInvSet X, range iU ∈ 𝓝 (iU x) ∧
        ∀ t : ℝ, ∀ᶠ y in 𝓝 x, flowMap Z t (iU y) = iU (flowMap X t y)) ∧
    (∀ y ∈ maxInvSet Y, range iV ∈ 𝓝 (iV y) ∧
        ∀ t : ℝ, ∀ᶠ y' in 𝓝 y, flowMap Z t (iV y') = iV (flowMap Y t y')) := by
  obtain ⟨hcU, hcV, heU, heV, hdU, hdV, hcov, hiff, hZU, hZV⟩ := hglue
  exact ⟨lc_side X Z iU hX hcU heU hdU hZU, lc_side Y Z iV hY hcV heV hdV hZV⟩
