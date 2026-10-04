-- Prove2me | solution 1 for AnosovPlugs.prop_1_1_gluing_hyperbolic_plugs
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-02T17:14:55.77779+00:00
-- url     : https://prove2.me/submissions/08f6c043-e798-49e2-b826-99bfa8b8b523
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing
import Theorems.Thm_AnosovPlugs_plugGluing_nonsingular
import Theorems.Thm_AnosovPlugs_plugGluing_transverse_boundary
import Theorems.Thm_AnosovPlugs_plugGluing_maxInvSet_hyperbolic

open scoped Manifold ContDiff Topology
open Set

open AnosovPlugs

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
    (hφ : IsBoundaryDiffeo φ Tout Tin)
    (htransv : ∀ p ∈ φ '' (exitLamination X ∩ Tout) ∩ entranceLamination Y,
      CurvesTransverseAt (pushLeaf φ Tout (exitLeaf X) p) (entranceLeaf Y p) p)
    (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W)
    (hglue : IsPlugGluing X Y Tout φ Z iU iV) :
    IsNonsingularTransverse Z ∧ IsHyperbolicSet Z (maxInvSet Z) := by
  exact ⟨⟨plugGluing_nonsingular X Y hX.1.2.1 hY.1.2.1 Tout φ Z iU iV hglue,
      plugGluing_transverse_boundary X Y hX.1 hY.1 Tout Tin hTout hTin φ hφ Z iU iV hglue⟩,
    plugGluing_maxInvSet_hyperbolic X Y hX hY Tout Tin hTout hTin φ hφ htransv Z iU iV hglue⟩
