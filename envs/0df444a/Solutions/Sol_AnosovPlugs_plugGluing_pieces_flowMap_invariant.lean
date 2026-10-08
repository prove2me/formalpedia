-- Prove2me | solution 1 for AnosovPlugs.plugGluing_pieces_flowMap_invariant
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-04T23:58:54.191352+00:00
-- url     : https://prove2.me/submissions/59f5af92-d37d-4107-ac8f-7517794ca6d1

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing
import Theorems.Thm_AnosovPlugs_plugGluing_integralCurveOn_unique

open scoped Manifold ContDiff Topology
open Set AnosovPlugs

/-- The image of a complete integral curve under a `C¹` map that sends one vector field to
another is a complete integral curve. -/
lemma pi_isMIntegralCurve_comp
    {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U]
    {W : Type} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 3) W]
    [IsManifold I3 ∞ W]
    (X : (x : U) → TangentSpace I3 x) (Z : (w : W) → TangentSpace I3 w) (i : U → W)
    (hc : ContMDiff I3 I3 1 i) (hZ : ∀ x, mfderiv I3 I3 i x (X x) = Z (i x))
    (δ : ℝ → U) (hδ : IsMIntegralCurve δ X) : IsMIntegralCurve (i ∘ δ) Z := by
  intro t
  have hi : HasMFDerivAt I3 I3 i (δ t) (mfderiv I3 I3 i (δ t)) :=
    (hc.mdifferentiableAt one_ne_zero).hasMFDerivAt
  refine (hi.comp t (hδ t)).congr_mfderiv ?_
  refine ContinuousLinearMap.ext_ring ?_
  change mfderiv I3 I3 i (δ t) ((1 : ℝ) • X (δ t)) = (1 : ℝ) • Z (i (δ t))
  rw [one_smul, one_smul]
  exact hZ (δ t)

/-- Generic invariance: if `i` pushes `X` to `Z` and integral curves of `Z` on `[0, t]` are
unique, then the time-`t` map of `Z` preserves `i '' maxInvSet X`. -/
lemma pi_flowMap_mem
    {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U]
    {W : Type} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 3) W]
    [IsManifold I3 ∞ W]
    (X : (x : U) → TangentSpace I3 x) (Z : (w : W) → TangentSpace I3 w) (i : U → W)
    (hc : ContMDiff I3 I3 1 i) (hZ : ∀ x, mfderiv I3 I3 i x (X x) = Z (i x))
    (huniq : ∀ (γ γ' : ℝ → W) (t : ℝ), IsMIntegralCurveOn γ Z (uIcc 0 t) →
      IsMIntegralCurveOn γ' Z (uIcc 0 t) → γ' 0 = γ 0 → ∀ s ∈ uIcc 0 t, γ' s = γ s) :
    ∀ w ∈ i '' maxInvSet X, ∀ t : ℝ, flowMap Z t w ∈ i '' maxInvSet X := by
  rintro w ⟨x, ⟨δ, hδ0, hδ⟩, rfl⟩ t
  have hη : IsMIntegralCurve (i ∘ δ) Z := pi_isMIntegralCurve_comp X Z i hc hZ δ hδ
  have hd : FlowDefined Z (i x) t :=
    ⟨i ∘ δ, by simp [hδ0], hη.isMIntegralCurveOn _⟩
  have hflow : flowMap Z t (i x) = i (δ t) := by
    unfold flowMap
    rw [dif_pos hd]
    obtain ⟨h0', hc'⟩ := hd.choose_spec
    exact huniq (i ∘ δ) hd.choose t (hη.isMIntegralCurveOn _) hc'
      (by rw [h0']; simp [hδ0]) t right_mem_uIcc
  rw [hflow]
  exact ⟨δ t, ⟨δ ∘ (· + t), by simp, hδ.comp_add t⟩, rfl⟩

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
    (hφ : IsBoundaryDiffeo φ Tout Tin)
    (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W)
    (hglue : IsPlugGluing X Y Tout φ Z iU iV) :
    (∀ w ∈ iU '' maxInvSet X, ∀ t : ℝ, flowMap Z t w ∈ iU '' maxInvSet X) ∧
    (∀ w ∈ iV '' maxInvSet Y, ∀ t : ℝ, flowMap Z t w ∈ iV '' maxInvSet Y) := by
  have huniq := AnosovPlugs.plugGluing_integralCurveOn_unique X Y hX hY Tout Tin hTout hTin φ hφ
    Z iU iV hglue
  obtain ⟨hcU, hcV, -, -, -, -, -, -, hZU, hZV⟩ := hglue
  exact ⟨pi_flowMap_mem X Z iU hcU hZU huniq, pi_flowMap_mem Y Z iV hcV hZV huniq⟩
