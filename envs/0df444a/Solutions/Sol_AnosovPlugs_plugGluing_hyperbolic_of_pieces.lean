-- Prove2me | solution 1 for AnosovPlugs.plugGluing_hyperbolic_of_pieces
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-03T20:58:49.774738+00:00
-- url     : https://prove2.me/submissions/e45baf6d-07dd-4be2-be3e-41b38fa4b9bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing
import Theorems.Thm_AnosovPlugs_isHyperbolicSet_of_metric
import Theorems.Thm_AnosovPlugs_plugGluing_integralCurveOn_unique
import Theorems.Thm_AnosovPlugs_exists_localFlow_contMDiff_of_isInteriorPoint
import Theorems.Thm_AnosovPlugs_plugGluing_hyperbolic_of_pieces_of_flows

open scoped Manifold ContDiff Topology
open Set AnosovPlugs

/-- Reduction of `plugGluing_hyperbolic_of_pieces` (Prop 1.1, the hyperbolicity of the maximal
invariant set of the glued field) to five children: one metric for both pieces
(`isHyperbolicSet_of_metric`), uniqueness of integral curves of the glued field
(`plugGluing_integralCurveOn_unique`, whose own proof rests on `integralCurveOn_uIcc_unique`), C¹ local
flows of `X` and `Y` at interior points (`exists_localFlow_contMDiff_of_isInteriorPoint`), and the
hyperbolic extension theorem `plugGluing_hyperbolic_of_pieces_of_flows`. -/
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
    (hglue : IsPlugGluing X Y Tout φ Z iU iV)
    (hΛ : maxInvSet Z = iU '' maxInvSet X ∪ iV '' maxInvSet Y ∪
      {w | ∃ x ∈ exitLamination X ∩ Tout, φ x ∈ entranceLamination Y ∧
        ∃ γ : ℝ → W, γ 0 = iU x ∧ IsMIntegralCurve γ Z ∧ w ∈ range γ})
    (hU : IsHyperbolicSet Z (iU '' maxInvSet X)) (hV : IsHyperbolicSet Z (iV '' maxInvSet Y)) :
    IsHyperbolicSet Z (maxInvSet Z) := by
  obtain ⟨g, Es, Eu, C, lam, hC, hlam, hUg⟩ := hU
  exact plugGluing_hyperbolic_of_pieces_of_flows X Y hX hY Tout Tin hTout hTin φ hφ htransv Z iU iV
    hglue hΛ g ⟨Es, Eu, C, lam, hC, hlam, hUg⟩ (isHyperbolicSet_of_metric Z _ hV g)
    (plugGluing_integralCurveOn_unique X Y hX.1 hY.1 Tout Tin hTout hTin φ hφ Z iU iV hglue)
    (fun x₀ hx₀ => exists_localFlow_contMDiff_of_isInteriorPoint X hX.1.1 x₀ hx₀)
    (fun y₀ hy₀ => exists_localFlow_contMDiff_of_isInteriorPoint Y hY.1.1 y₀ hy₀)
