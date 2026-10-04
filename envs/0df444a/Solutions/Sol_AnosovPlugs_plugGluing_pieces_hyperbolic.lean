-- Prove2me | solution 1 for AnosovPlugs.plugGluing_pieces_hyperbolic
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-03T01:20:00.040118+00:00
-- url     : https://prove2.me/submissions/5b2f2385-a7fe-468b-83e2-3dd34230cedb

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing
import Theorems.Thm_AnosovPlugs_hyperbolicSet_image_of_conjugacy
import Theorems.Thm_AnosovPlugs_plugGluing_local_conjugacy
import Theorems.Thm_AnosovPlugs_exists_comparable_metric
import Theorems.Thm_AnosovPlugs_flowMap_eq_of_isMIntegralCurve
import Theorems.Thm_AnosovPlugs_normalCoord_nonneg_of_hasMFDerivWithinAt

open scoped Manifold ContDiff Topology
open Set
open AnosovPlugs

/-- Every point of the maximal invariant set of a plug is an interior point. -/
theorem pieces_maxInvSet_isInteriorPoint
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
theorem pieces_mem_maxInvSet_of_isMIntegralCurve
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {X : (x : M) → TangentSpace I3 x} {γ : ℝ → M} (hγ : IsMIntegralCurve γ X) (s : ℝ) :
    γ s ∈ maxInvSet X :=
  ⟨γ ∘ (· + s), by simp, hγ.comp_add s⟩

/-- The maximal invariant set of a plug is invariant under the flow. -/
theorem pieces_maxInvSet_flow_invariant
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    [T2Space M]
    {X : (x : M) → TangentSpace I3 x} (hX : IsPlug X) :
    ∀ x ∈ maxInvSet X, ∀ t : ℝ, flowMap X t x ∈ maxInvSet X := by
  intro x hx t
  obtain ⟨γ, rfl, hγ⟩ := hx
  rw [flowMap_eq_of_isMIntegralCurve X hX.1 γ hγ
    (fun s => pieces_maxInvSet_isInteriorPoint hX _
      (pieces_mem_maxInvSet_of_isMIntegralCurve hγ s)) t]
  exact pieces_mem_maxInvSet_of_isMIntegralCurve hγ t

theorem solution
    {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U] [T2Space U] [CompactSpace U]
    {V : Type} [TopologicalSpace V] [ChartedSpace (EuclideanHalfSpace 3) V]
    [IsManifold I3 ∞ V] [T2Space V] [CompactSpace V]
    {W : Type} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 3) W]
    [IsManifold I3 ∞ W] [T2Space W] [CompactSpace W]
    (X : (x : U) → TangentSpace I3 x) (Y : (y : V) → TangentSpace I3 y)
    (hX : IsHyperbolicPlug X) (hY : IsHyperbolicPlug Y)
    (Tout : Set U) (Tin : Set V) (hTout : IsUnionOfComponents Tout (outBoundary X))
    (hTin : IsUnionOfComponents Tin (inBoundary Y)) (φ : U → V)
    (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W)
    (hglue : IsPlugGluing X Y Tout φ Z iU iV) :
    IsHyperbolicSet Z (iU '' maxInvSet X) ∧ IsHyperbolicSet Z (iV '' maxInvSet Y) := by
  obtain ⟨hU, hV⟩ :=
    plugGluing_local_conjugacy X Y hX.1 hY.1 Tout Tin hTout hTin φ Z iU iV hglue
  obtain ⟨hcU, hcV, heU, heV, hdU, hdV, _hcov, _hiff, hZU, hZV⟩ := hglue
  constructor
  · exact hyperbolicSet_image_of_conjugacy X Z iU (maxInvSet X) hX.2 hcU heU hdU hZU
      (pieces_maxInvSet_flow_invariant hX.1) (pieces_maxInvSet_isInteriorPoint hX.1)
      (fun x hx => (hU x hx).1) (fun x hx => (hU x hx).2)
      (fun g => exists_comparable_metric iU hcU hdU g)
  · exact hyperbolicSet_image_of_conjugacy Y Z iV (maxInvSet Y) hY.2 hcV heV hdV hZV
      (pieces_maxInvSet_flow_invariant hY.1) (pieces_maxInvSet_isInteriorPoint hY.1)
      (fun y hy => (hV y hy).1) (fun y hy => (hV y hy).2)
      (fun g => exists_comparable_metric iV hcV hdV g)
