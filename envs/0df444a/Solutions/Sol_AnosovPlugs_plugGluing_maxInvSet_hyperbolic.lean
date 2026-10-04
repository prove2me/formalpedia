-- Prove2me | solution 1 for AnosovPlugs.plugGluing_maxInvSet_hyperbolic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-02T20:31:30.502369+00:00
-- url     : https://prove2.me/submissions/110900ab-9179-46e9-b0a3-2839a4fbd1a2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing
import Theorems.Thm_AnosovPlugs_plugGluing_maxInvSet_subset
import Theorems.Thm_AnosovPlugs_plugGluing_maxInvSet_superset
import Theorems.Thm_AnosovPlugs_plugGluing_pieces_hyperbolic
import Theorems.Thm_AnosovPlugs_plugGluing_hyperbolic_of_pieces

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
    IsHyperbolicSet Z (maxInvSet Z) := by
  have hΛ := Subset.antisymm
    (plugGluing_maxInvSet_subset X Y hX.1 hY.1 Tout Tin hTout hTin φ hφ Z iU iV hglue)
    (plugGluing_maxInvSet_superset X Y Tout φ Z iU iV hglue)
  obtain ⟨hU, hV⟩ := plugGluing_pieces_hyperbolic X Y hX hY Tout Tin hTout hTin φ Z iU iV hglue
  exact plugGluing_hyperbolic_of_pieces X Y hX hY Tout Tin hTout hTin φ hφ htransv Z iU iV hglue
    hΛ hU hV
