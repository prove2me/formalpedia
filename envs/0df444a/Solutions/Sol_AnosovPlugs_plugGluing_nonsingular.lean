-- Prove2me | solution 1 for AnosovPlugs.plugGluing_nonsingular
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-02T17:14:54.899943+00:00
-- url     : https://prove2.me/submissions/70560058-b896-49d0-bea3-2a1970d85312

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

open AnosovPlugs

theorem solution
    {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U] [IsManifold I3 ∞ U]
    {V : Type} [TopologicalSpace V] [ChartedSpace (EuclideanHalfSpace 3) V] [IsManifold I3 ∞ V]
    {W : Type} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 3) W] [IsManifold I3 ∞ W]
    (X : (x : U) → TangentSpace I3 x) (Y : (y : V) → TangentSpace I3 y)
    (hX : ∀ x, X x ≠ 0) (hY : ∀ y, Y y ≠ 0)
    (Tout : Set U) (φ : U → V)
    (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W)
    (hglue : IsPlugGluing X Y Tout φ Z iU iV) :
    ∀ w, Z w ≠ 0 := by
  intro w hw
  obtain ⟨-, -, -, -, hdU, hdV, hcover, -, hZU, hZV⟩ := hglue
  have hw' : w ∈ range iU ∪ range iV := by rw [hcover]; exact mem_univ w
  rcases hw' with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact hX x (hdU x (by rw [hZU x, hw, map_zero]))
  · exact hY y (hdV y (by rw [hZV y, hw, map_zero]))
