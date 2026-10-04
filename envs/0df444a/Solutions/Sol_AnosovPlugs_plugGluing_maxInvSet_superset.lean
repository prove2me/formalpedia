-- Prove2me | solution 1 for AnosovPlugs.plugGluing_maxInvSet_superset
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-02T20:31:31.111584+00:00
-- url     : https://prove2.me/submissions/269737e0-2ecf-40f1-97df-9342daaffd37

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

open AnosovPlugs

/-- The image of a complete integral curve under a `C¹` map that sends one vector field to
another is a complete integral curve. -/
lemma anosovPlugs_isMIntegralCurve_comp
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

theorem solution
    {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U] [T2Space U] [CompactSpace U]
    {V : Type} [TopologicalSpace V] [ChartedSpace (EuclideanHalfSpace 3) V]
    [IsManifold I3 ∞ V] [T2Space V] [CompactSpace V]
    {W : Type} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 3) W]
    [IsManifold I3 ∞ W] [T2Space W] [CompactSpace W]
    (X : (x : U) → TangentSpace I3 x) (Y : (y : V) → TangentSpace I3 y)
    (Tout : Set U) (φ : U → V)
    (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W)
    (hglue : IsPlugGluing X Y Tout φ Z iU iV) :
    iU '' maxInvSet X ∪ iV '' maxInvSet Y ∪
      {w | ∃ x ∈ exitLamination X ∩ Tout, φ x ∈ entranceLamination Y ∧
        ∃ γ : ℝ → W, γ 0 = iU x ∧ IsMIntegralCurve γ Z ∧ w ∈ range γ} ⊆ maxInvSet Z := by
  obtain ⟨hcU, hcV, -, -, -, -, -, -, hZU, hZV⟩ := hglue
  intro w hw
  rcases hw with (⟨x, ⟨δ, hδ0, hδ⟩, rfl⟩ | ⟨y, ⟨δ, hδ0, hδ⟩, rfl⟩) | ⟨x, -, -, γ, -, hγ, s, rfl⟩
  · exact ⟨iU ∘ δ, by simp [hδ0], anosovPlugs_isMIntegralCurve_comp X Z iU hcU hZU δ hδ⟩
  · exact ⟨iV ∘ δ, by simp [hδ0], anosovPlugs_isMIntegralCurve_comp Y Z iV hcV hZV δ hδ⟩
  · exact ⟨γ ∘ (· + s), by simp, hγ.comp_add s⟩

