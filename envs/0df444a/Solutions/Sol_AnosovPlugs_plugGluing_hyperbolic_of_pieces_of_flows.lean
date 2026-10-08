-- Prove2me | solution 1 for AnosovPlugs.plugGluing_hyperbolic_of_pieces_of_flows
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-04T20:36:35.146743+00:00
-- url     : https://prove2.me/submissions/c70539a7-adf2-47ea-8562-aec856db23b2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing
import Theorems.Thm_AnosovPlugs_plugGluing_flowMap_contMDiffOn
import Theorems.Thm_AnosovPlugs_plugGluing_hyperbolic_of_pieces_of_regularity

open scoped Manifold ContDiff Topology
open Set AnosovPlugs

/-- Reduction of `plugGluing_hyperbolic_of_pieces_of_flows` to two children: the C¹ regularity of
the time-`t` maps of the glued field near its maximal invariant set
(`plugGluing_flowMap_contMDiffOn`), and the hyperbolic extension theorem with that regularity as a
hypothesis (`plugGluing_hyperbolic_of_pieces_of_regularity`). The hypotheses `hflowX` and `hflowY`
are not used here. -/
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
    (hflowX : ∀ x₀ : U, I3.IsInteriorPoint x₀ →
      ∃ ε > (0 : ℝ), ∃ O : Set U, IsOpen O ∧ x₀ ∈ O ∧ ∃ α : U → ℝ → U,
        (∀ y ∈ O, α y 0 = y ∧ IsMIntegralCurveOn (α y) X (Icc (-ε) ε) ∧
          ∀ τ ∈ Icc (-ε) ε, I3.IsInteriorPoint (α y τ)) ∧
        ContMDiffOn (I3.prod 𝓘(ℝ, ℝ)) I3 1 (fun p : U × ℝ => α p.1 p.2) (O ×ˢ Ioo (-ε) ε) ∧
        (∀ y ∈ O, ∀ h : ℝ, |h| ≤ ε → ∀ η : ℝ → U, η 0 = y →
          IsMIntegralCurveOn η X (uIcc 0 h) → (∀ τ ∈ uIcc 0 h, η τ ∈ O) →
          ∀ τ ∈ uIcc 0 h, η τ = α y τ))
    (hflowY : ∀ y₀ : V, I3.IsInteriorPoint y₀ →
      ∃ ε > (0 : ℝ), ∃ O : Set V, IsOpen O ∧ y₀ ∈ O ∧ ∃ α : V → ℝ → V,
        (∀ y ∈ O, α y 0 = y ∧ IsMIntegralCurveOn (α y) Y (Icc (-ε) ε) ∧
          ∀ τ ∈ Icc (-ε) ε, I3.IsInteriorPoint (α y τ)) ∧
        ContMDiffOn (I3.prod 𝓘(ℝ, ℝ)) I3 1 (fun p : V × ℝ => α p.1 p.2) (O ×ˢ Ioo (-ε) ε) ∧
        (∀ y ∈ O, ∀ h : ℝ, |h| ≤ ε → ∀ η : ℝ → V, η 0 = y →
          IsMIntegralCurveOn η Y (uIcc 0 h) → (∀ τ ∈ uIcc 0 h, η τ ∈ O) →
          ∀ τ ∈ uIcc 0 h, η τ = α y τ)) :
    IsHyperbolicSet Z (maxInvSet Z) := by
  exact plugGluing_hyperbolic_of_pieces_of_regularity X Y hX hY Tout Tin hTout hTin φ hφ htransv Z iU iV
    hglue hΛ g hU hV huniq
    (plugGluing_flowMap_contMDiffOn X Y hX.1 hY.1 Tout Tin hTout hTin φ hφ Z iU iV hglue)
