-- Prove2me | solution 1 for AnosovPlugs.plugGluing_hyperbolic_of_pieces_of_regularity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-04T23:58:52.57365+00:00
-- url     : https://prove2.me/submissions/3c176b57-e617-4839-89cc-b75dd7576688
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing
import Theorems.Thm_AnosovPlugs_flowMap_flowProperty_of_regularity
import Theorems.Thm_AnosovPlugs_plugGluing_pieces_flowMap_invariant
import Theorems.Thm_AnosovPlugs_plugGluing_hyperbolic_of_pieces_of_flowProperty

open scoped Manifold ContDiff Topology
open Set AnosovPlugs

/-- Reduction of `plugGluing_hyperbolic_of_pieces_of_regularity` to three theorems: the flow
properties of `flowMap Z` on the maximal invariant set (`flowMap_flowProperty_of_regularity`), the
invariance of the two pieces (`plugGluing_pieces_flowMap_invariant`), and the hyperbolic extension
theorem with these as hypotheses (`plugGluing_hyperbolic_of_pieces_of_flowProperty`). -/
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
    (g : RiemannianMetric3 W)
    (hU : ∃ (Es Eu : (x : W) → Submodule ℝ (TangentSpace I3 x)) (C lam : ℝ), 0 < C ∧ 0 < lam ∧
          ∀ x ∈ iU '' maxInvSet X,
            Module.finrank ℝ (Es x) = 1 ∧ Module.finrank ℝ (Eu x) = 1 ∧
            Es x ⊔ Submodule.span ℝ {Z x} ⊔ Eu x = ⊤ ∧
            (∀ t : ℝ, (Es x).map (mfderiv I3 I3 (flowMap Z t) x).toLinearMap = Es (flowMap Z t x)) ∧
            (∀ t : ℝ, (Eu x).map (mfderiv I3 I3 (flowMap Z t) x).toLinearMap = Eu (flowMap Z t x)) ∧
            (∀ t : ℝ, 0 ≤ t → ∀ v ∈ Es x,
              g.norm (flowMap Z t x) (mfderiv I3 I3 (flowMap Z t) x v)
                ≤ C * Real.exp (-lam * t) * g.norm x v) ∧
            (∀ t : ℝ, 0 ≤ t → ∀ v ∈ Eu x,
              g.norm (flowMap Z (-t) x) (mfderiv I3 I3 (flowMap Z (-t)) x v)
                ≤ C * Real.exp (-lam * t) * g.norm x v))
    (hV : ∃ (Es Eu : (x : W) → Submodule ℝ (TangentSpace I3 x)) (C lam : ℝ), 0 < C ∧ 0 < lam ∧
          ∀ x ∈ iV '' maxInvSet Y,
            Module.finrank ℝ (Es x) = 1 ∧ Module.finrank ℝ (Eu x) = 1 ∧
            Es x ⊔ Submodule.span ℝ {Z x} ⊔ Eu x = ⊤ ∧
            (∀ t : ℝ, (Es x).map (mfderiv I3 I3 (flowMap Z t) x).toLinearMap = Es (flowMap Z t x)) ∧
            (∀ t : ℝ, (Eu x).map (mfderiv I3 I3 (flowMap Z t) x).toLinearMap = Eu (flowMap Z t x)) ∧
            (∀ t : ℝ, 0 ≤ t → ∀ v ∈ Es x,
              g.norm (flowMap Z t x) (mfderiv I3 I3 (flowMap Z t) x v)
                ≤ C * Real.exp (-lam * t) * g.norm x v) ∧
            (∀ t : ℝ, 0 ≤ t → ∀ v ∈ Eu x,
              g.norm (flowMap Z (-t) x) (mfderiv I3 I3 (flowMap Z (-t)) x v)
                ≤ C * Real.exp (-lam * t) * g.norm x v))
    (huniq : ∀ (γ γ' : ℝ → W) (t : ℝ), IsMIntegralCurveOn γ Z (uIcc 0 t) → IsMIntegralCurveOn γ' Z (uIcc 0 t) →
            γ' 0 = γ 0 → ∀ s ∈ uIcc 0 t, γ' s = γ s)
    (hreg : ∀ w ∈ maxInvSet Z, I3.IsInteriorPoint w ∧ ∀ t : ℝ, ∃ O : Set W, IsOpen O ∧ w ∈ O ∧
        (∀ y ∈ O, FlowDefined Z y t) ∧ ContMDiffOn I3 I3 1 (flowMap Z t) O) :
    IsHyperbolicSet Z (maxInvSet Z) := by
  exact plugGluing_hyperbolic_of_pieces_of_flowProperty X Y hX hY Tout Tin hTout hTin φ hφ htransv Z iU iV
    hglue hΛ g hU hV huniq hreg (flowMap_flowProperty_of_regularity Z huniq hreg)
    (plugGluing_pieces_flowMap_invariant X Y hX.1 hY.1 Tout Tin hTout hTin φ hφ Z iU iV hglue)
