-- Prove2me | solution 1 for AnosovPlugs.plugGluing_flowMap_contMDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-04T20:36:35.814446+00:00
-- url     : https://prove2.me/submissions/af0532c8-3ddc-4906-8bd6-e57b12501151

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing
import Theorems.Thm_AnosovPlugs_flowMap_contMDiffOn_of_localSteps
import Theorems.Thm_AnosovPlugs_localSteps_of_embedding
import Theorems.Thm_AnosovPlugs_plugGluing_localSteps_seam
import Theorems.Thm_AnosovPlugs_exists_localFlow_contMDiff_of_isInteriorPoint
import Theorems.Thm_AnosovPlugs_plugGluing_integralCurveOn_unique
import Theorems.Thm_AnosovPlugs_plugGluing_transverse_boundary
import Theorems.Thm_AnosovPlugs_normalCoord_nonneg_of_hasMFDerivWithinAt
import Theorems.Thm_AnosovPlugs_integralCurve_lift_of_embedding

open scoped Manifold ContDiff Topology
open Set AnosovPlugs

/-- A complete integral curve of `Z` cannot pass through `i u` with `u` a boundary point of
`M`, when near that time the curve stays in the image of the embedding `i` (it avoids the
closed set `C` that, together with `range i`, covers `N`) and `X` is transverse to `∂M`. -/
theorem sr_lift_boundary_false
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (X : (x : M) → TangentSpace I3 x) (Z : (w : N) → TangentSpace I3 w) (i : M → N)
    (hi : ContMDiff I3 I3 1 i) (hemb : Topology.IsEmbedding i)
    (hinj : ∀ x, Function.Injective (mfderiv I3 I3 i x))
    (hZ : ∀ x, mfderiv I3 I3 i x (X x) = Z (i x))
    (hX : ∀ x ∈ I3.boundary M, normalCoord (X x) ≠ 0)
    (C : Set N) (hC : IsClosed C) (hcov : ∀ p, p ∈ range i ∨ p ∈ C)
    (γ : ℝ → N) (hγ : IsMIntegralCurve γ Z) (s : ℝ) (u : M) (hu : i u = γ s)
    (hub : u ∈ I3.boundary M) (hsC : γ s ∉ C) : False := by
  have hopen : IsOpen (γ ⁻¹' Cᶜ) := hC.isOpen_compl.preimage hγ.continuous
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen s hsC
  have ha : 0 < ε / 2 := half_pos hε
  have hsub : Icc (s - ε / 2) (s + ε / 2) ⊆ Metric.ball s ε := by
    intro r hr
    rw [Real.ball_eq_Ioo]
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hrange : ∀ r ∈ Icc (s - ε / 2) (s + ε / 2), γ r ∈ range i := fun r hr =>
    (hcov (γ r)).resolve_right (hball (hsub hr))
  obtain ⟨δ, hδ, hδX⟩ := integralCurve_lift_of_embedding X Z i hi hemb hinj hZ γ _
    (hγ.isMIntegralCurveOn _) hrange (nonempty_Icc.2 (by linarith))
  have hmem : s ∈ Icc (s - ε / 2) (s + ε / 2) := ⟨by linarith, by linarith⟩
  have hδs : δ s = u := hemb.injective ((hδ s hmem).trans hu.symm)
  have hb : δ s ∈ I3.boundary M := hδs ▸ hub
  have hc1 : (s + ε / 2) - s ∈ posTangentConeAt (Icc (s - ε / 2) (s + ε / 2)) s := by
    apply sub_mem_posTangentConeAt_of_segment_subset
    rw [segment_eq_Icc (by linarith)]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hc2 : (s - ε / 2) - s ∈ posTangentConeAt (Icc (s - ε / 2) (s + ε / 2)) s := by
    apply sub_mem_posTangentConeAt_of_segment_subset
    rw [segment_symm, segment_eq_Icc (by linarith)]
    exact Icc_subset_Icc le_rfl (by linarith)
  have h1 := normalCoord_nonneg_of_hasMFDerivWithinAt δ _ s (X (δ s)) (hδX s hmem) hb _ hc1
  have h2 := normalCoord_nonneg_of_hasMFDerivWithinAt δ _ s (X (δ s)) (hδX s hmem) hb _ hc2
  apply hX _ hb
  have e1 : (s + ε / 2) - s = ε / 2 := by ring
  have e2 : (s - ε / 2) - s = -(ε / 2) := by ring
  rw [e1] at h1
  rw [e2] at h2
  rcases lt_trichotomy (normalCoord (X (δ s))) 0 with h | h | h
  · nlinarith
  · exact h
  · nlinarith

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
    ∀ w ∈ maxInvSet Z, I3.IsInteriorPoint w ∧ ∀ t : ℝ, ∃ O : Set W, IsOpen O ∧ w ∈ O ∧
      (∀ y ∈ O, FlowDefined Z y t) ∧ ContMDiffOn I3 I3 1 (flowMap Z t) O := by
  rintro w ⟨γ, hγ0, hγ⟩
  have hg := hglue
  obtain ⟨hcU, hcV, heU, heV, hdU, hdV, hcover, hiff, hZU, hZV⟩ := hg
  -- (a) the curve stays in the interior of `W`
  have hint : ∀ s, I3.IsInteriorPoint (γ s) := by
    intro s
    rcases I3.isInteriorPoint_or_isBoundaryPoint (γ s) with h | h
    · exact h
    · exfalso
      have hb : γ s ∈ I3.boundary W := h
      have hd : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I3 γ univ s
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Z (γ s))) := (hγ s).hasMFDerivWithinAt
      have h1 := normalCoord_nonneg_of_hasMFDerivWithinAt γ univ s (Z (γ s)) hd hb 1
        (by rw [posTangentConeAt_univ]; exact mem_univ _)
      have h2 := normalCoord_nonneg_of_hasMFDerivWithinAt γ univ s (Z (γ s)) hd hb (-1)
        (by rw [posTangentConeAt_univ]; exact mem_univ _)
      exact plugGluing_transverse_boundary X Y hX hY Tout Tin hTout hTin φ hφ Z iU iV hglue
        (γ s) hb (by linarith)
  -- (b) local steps at every point of the curve
  have hloc : ∀ s : ℝ,
      ∃ ε > (0 : ℝ), ∃ O : Set W, IsOpen O ∧ γ s ∈ O ∧ ∀ h : ℝ, |h| ≤ ε → ∃ f : W → W,
        ContMDiffOn I3 I3 1 f O ∧
        ∀ y ∈ O, ∃ η : ℝ → W, η 0 = y ∧ IsMIntegralCurveOn η Z (uIcc 0 h) ∧ η h = f y := by
    intro s
    have hp : γ s ∈ range iU ∪ range iV := hcover ▸ mem_univ _
    rcases hp with ⟨u, hu⟩ | ⟨v, hv⟩
    · rcases I3.isInteriorPoint_or_isBoundaryPoint u with hui | hub
      · rw [← hu]
        exact localSteps_of_embedding X Z iU hcU hZU u hui (hdU u)
          (exists_localFlow_contMDiff_of_isInteriorPoint X hX.1 u hui)
      · by_cases huT : u ∈ Tout
        · rw [← hu]
          exact plugGluing_localSteps_seam X Y hX hY Tout Tin hTout hTin φ hφ Z iU iV hglue
            u huT (hu ▸ hint s)
        · exfalso
          refine sr_lift_boundary_false X Z iU hcU heU hdU hZU hX.2.2 (range iV)
            (isCompact_range hcV.continuous).isClosed
            (fun p => by
              have : p ∈ range iU ∪ range iV := hcover ▸ mem_univ _
              exact this)
            γ hγ s u hu hub ?_
          rintro ⟨v, hv⟩
          exact huT ((hiff u v).mp (hu.trans hv.symm)).1
    · rcases I3.isInteriorPoint_or_isBoundaryPoint v with hvi | hvb
      · rw [← hv]
        exact localSteps_of_embedding Y Z iV hcV hZV v hvi (hdV v)
          (exists_localFlow_contMDiff_of_isInteriorPoint Y hY.1 v hvi)
      · by_cases hvT : v ∈ Tin
        · obtain ⟨x, hxT, rfl⟩ := hφ.1.surjOn hvT
          have hxe : iU x = iV (φ x) := (hiff x (φ x)).mpr ⟨hxT, rfl⟩
          rw [← hv, ← hxe]
          exact plugGluing_localSteps_seam X Y hX hY Tout Tin hTout hTin φ hφ Z iU iV hglue
            x hxT (by rw [hxe, hv]; exact hint s)
        · exfalso
          refine sr_lift_boundary_false Y Z iV hcV heV hdV hZV hY.2.2 (range iU)
            (isCompact_range hcU.continuous).isClosed
            (fun p => by
              have : p ∈ range iU ∪ range iV := hcover ▸ mem_univ _
              exact Or.symm this)
            γ hγ s v hv hvb ?_
          rintro ⟨x, hx⟩
          obtain ⟨hxT, rfl⟩ := (hiff x v).mp (hx.trans hv.symm)
          exact hvT (hφ.1.mapsTo hxT)
  -- (c) the chain lemma
  refine ⟨hγ0 ▸ hint 0, fun t => ?_⟩
  obtain ⟨O, hO, h0, hdef, hsm⟩ := flowMap_contMDiffOn_of_localSteps Z
    (plugGluing_integralCurveOn_unique X Y hX hY Tout Tin hTout hTin φ hφ Z iU iV hglue)
    γ t (hγ.isMIntegralCurveOn _) (fun s _ => hloc s)
  exact ⟨O, hO, hγ0 ▸ h0, hdef, hsm⟩
