-- Prove2me | solution 1 for AnosovPlugs.plugGluing_maxInvSet_subset
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-02T22:57:54.045264+00:00
-- url     : https://prove2.me/submissions/48e5945f-0f3a-41c3-8581-6c72b6e18594

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing
import Theorems.Thm_AnosovPlugs_integralCurve_lift_of_embedding
import Theorems.Thm_AnosovPlugs_normalCoord_nonneg_of_hasMFDerivWithinAt

open scoped Manifold ContDiff Topology
open Set

open AnosovPlugs

/-- Two closed sets that cover `ℝ`, and that are both proper, have a common point. -/
lemma plugGlue_inter_nonempty {A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : ∀ t, t ∈ A ∨ t ∈ B) (hAu : A ≠ univ) (hBu : B ≠ univ) : (A ∩ B).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have hAc : A = Bᶜ := by
    ext t
    refine ⟨fun ha hb => ?_, fun hb => (hAB t).resolve_right hb⟩
    have : t ∈ A ∩ B := ⟨ha, hb⟩
    rw [h] at this
    exact this
  have hclo : IsClopen A := ⟨hA, hAc ▸ hB.isOpen_compl⟩
  rcases isClopen_iff.mp hclo with h0 | h0
  · apply hBu
    ext t
    simp only [mem_univ, iff_true]
    exact (hAB t).resolve_left (by rw [h0]; exact notMem_empty t)
  · exact hAu h0

/-- Forward barrier: if no interval `[t₂, t₁]` in `A` starts at a point of `B`, then
`B` contains the ray from a point of `B`. -/
lemma plugGlue_fwd_barrier {A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : ∀ t, t ∈ A ∨ t ∈ B) {t₀ : ℝ} (ht₀ : t₀ ∈ B)
    (hno : ∀ t₂ t₁, t₂ < t₁ → Icc t₂ t₁ ⊆ A → t₂ ∈ B → False) : Ici t₀ ⊆ B := by
  intro t₁ ht₁
  by_contra h₁
  have hlt : t₀ < t₁ := lt_of_le_of_ne ht₁ (fun h => h₁ (h ▸ ht₀))
  have hKc : IsClosed (B ∩ Icc t₀ t₁) := hB.inter isClosed_Icc
  have hKne : (B ∩ Icc t₀ t₁).Nonempty := ⟨t₀, ht₀, le_rfl, hlt.le⟩
  have hKbdd : BddAbove (B ∩ Icc t₀ t₁) := ⟨t₁, fun u hu => hu.2.2⟩
  have hmem : sSup (B ∩ Icc t₀ t₁) ∈ B ∩ Icc t₀ t₁ := hKc.csSup_mem hKne hKbdd
  have h2lt : sSup (B ∩ Icc t₀ t₁) < t₁ :=
    lt_of_le_of_ne hmem.2.2 (fun h => h₁ (h ▸ hmem.1))
  have hIoc : Ioc (sSup (B ∩ Icc t₀ t₁)) t₁ ⊆ A := by
    intro u hu
    refine (hAB u).resolve_right fun huB => ?_
    have : u ≤ sSup (B ∩ Icc t₀ t₁) :=
      le_csSup hKbdd ⟨huB, hmem.2.1.trans hu.1.le, hu.2⟩
    exact absurd hu.1 (not_lt.mpr this)
  have hIcc : Icc (sSup (B ∩ Icc t₀ t₁)) t₁ ⊆ A := by
    rw [← closure_Ioc h2lt.ne]
    exact hA.closure_subset_iff.mpr hIoc
  exact hno _ t₁ h2lt hIcc hmem.1

/-- Backward barrier: the mirror form of `plugGlue_fwd_barrier`. -/
lemma plugGlue_bwd_barrier {A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : ∀ t, t ∈ A ∨ t ∈ B) {t₀ : ℝ} (ht₀ : t₀ ∈ A)
    (hno : ∀ t₁ t₂, t₁ < t₂ → Icc t₁ t₂ ⊆ B → t₂ ∈ A → False) : Iic t₀ ⊆ A := by
  intro t₁ ht₁
  by_contra h₁
  have hlt : t₁ < t₀ := lt_of_le_of_ne ht₁ (fun h => h₁ (h ▸ ht₀))
  have hKc : IsClosed (A ∩ Icc t₁ t₀) := hA.inter isClosed_Icc
  have hKne : (A ∩ Icc t₁ t₀).Nonempty := ⟨t₀, ht₀, hlt.le, le_rfl⟩
  have hKbdd : BddBelow (A ∩ Icc t₁ t₀) := ⟨t₁, fun u hu => hu.2.1⟩
  have hmem : sInf (A ∩ Icc t₁ t₀) ∈ A ∩ Icc t₁ t₀ := hKc.csInf_mem hKne hKbdd
  have h2lt : t₁ < sInf (A ∩ Icc t₁ t₀) :=
    lt_of_le_of_ne hmem.2.1 (fun h => h₁ (h ▸ hmem.1))
  have hIco : Ico t₁ (sInf (A ∩ Icc t₁ t₀)) ⊆ B := by
    intro u hu
    refine (hAB u).resolve_left fun huA => ?_
    have : sInf (A ∩ Icc t₁ t₀) ≤ u :=
      csInf_le hKbdd ⟨huA, hu.1, hu.2.le.trans hmem.2.2⟩
    exact absurd hu.2 (not_lt.mpr this)
  have hIcc : Icc t₁ (sInf (A ∩ Icc t₁ t₀)) ⊆ B := by
    rw [← closure_Ico h2lt.ne]
    exact hB.closure_subset_iff.mpr hIco
  exact hno t₁ _ h2lt hIcc hmem.1

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
    maxInvSet Z ⊆ iU '' maxInvSet X ∪ iV '' maxInvSet Y ∪
      {w | ∃ x ∈ exitLamination X ∩ Tout, φ x ∈ entranceLamination Y ∧
        ∃ γ : ℝ → W, γ 0 = iU x ∧ IsMIntegralCurve γ Z ∧ w ∈ range γ} := by
  rintro w ⟨γ, hγ0, hγ⟩
  obtain ⟨hcU, hcV, heU, heV, hdU, hdV, hcover, hiff, hZU, hZV⟩ := hglue
  have hAc : IsClosed (γ ⁻¹' range iU) :=
    (isCompact_range hcU.continuous).isClosed.preimage hγ.continuous
  have hBc : IsClosed (γ ⁻¹' range iV) :=
    (isCompact_range hcV.continuous).isClosed.preimage hγ.continuous
  have hAB : ∀ t, t ∈ γ ⁻¹' range iU ∨ t ∈ γ ⁻¹' range iV := fun t => by
    have : γ t ∈ range iU ∪ range iV := hcover ▸ mem_univ _
    exact this
  by_cases hAu : γ ⁻¹' range iU = univ
  · obtain ⟨δ, hδ, hδX⟩ := integralCurve_lift_of_embedding X Z iU hcU heU hdU hZU γ univ
      (hγ.isMIntegralCurveOn univ) (fun t _ => show t ∈ γ ⁻¹' range iU from hAu ▸ mem_univ t)
      univ_nonempty
    left; left
    refine ⟨δ 0, ⟨δ, rfl, isMIntegralCurve_iff_isMIntegralCurveOn.mpr hδX⟩, ?_⟩
    rw [hδ 0 (mem_univ _), hγ0]
  by_cases hBu : γ ⁻¹' range iV = univ
  · obtain ⟨δ, hδ, hδY⟩ := integralCurve_lift_of_embedding Y Z iV hcV heV hdV hZV γ univ
      (hγ.isMIntegralCurveOn univ) (fun t _ => show t ∈ γ ⁻¹' range iV from hBu ▸ mem_univ t)
      univ_nonempty
    left; right
    refine ⟨δ 0, ⟨δ, rfl, isMIntegralCurve_iff_isMIntegralCurveOn.mpr hδY⟩, ?_⟩
    rw [hδ 0 (mem_univ _), hγ0]
  right
  obtain ⟨t₀, ⟨x, hx⟩, ⟨y, hy⟩⟩ := plugGlue_inter_nonempty hAc hBc hAB hAu hBu
  obtain ⟨hxT, rfl⟩ := (hiff x y).mp (hx.trans hy.symm)
  have hfwd : Ici t₀ ⊆ γ ⁻¹' range iV := by
    refine plugGlue_fwd_barrier hAc hBc hAB ⟨φ x, hy⟩ ?_
    intro t₂ t₁ h21 hsub ht₂B
    obtain ⟨δ, hδ, hδX⟩ := integralCurve_lift_of_embedding X Z iU hcU heU hdU hZU γ
      (Icc t₂ t₁) (hγ.isMIntegralCurveOn _) hsub (nonempty_Icc.2 h21.le)
    obtain ⟨y₂, hy₂⟩ := ht₂B
    have hmem : t₂ ∈ Icc t₂ t₁ := ⟨le_rfl, h21.le⟩
    have hT := ((hiff (δ t₂) y₂).mp ((hδ t₂ hmem).trans hy₂.symm)).1
    obtain ⟨hb, hn⟩ := hTout.1 hT
    have hc : t₁ - t₂ ∈ posTangentConeAt (Icc t₂ t₁) t₂ :=
      sub_mem_posTangentConeAt_of_segment_subset (segment_eq_Icc h21.le).subset
    have h1 := normalCoord_nonneg_of_hasMFDerivWithinAt δ (Icc t₂ t₁) t₂ (X (δ t₂))
      (hδX t₂ hmem) hb (t₁ - t₂) hc
    have h2 := mul_neg_of_pos_of_neg (sub_pos.mpr h21) hn
    linarith
  have hbwd : Iic t₀ ⊆ γ ⁻¹' range iU := by
    refine plugGlue_bwd_barrier hAc hBc hAB ⟨x, hx⟩ ?_
    intro t₁ t₂ h12 hsub ht₂A
    obtain ⟨δ, hδ, hδY⟩ := integralCurve_lift_of_embedding Y Z iV hcV heV hdV hZV γ
      (Icc t₁ t₂) (hγ.isMIntegralCurveOn _) hsub (nonempty_Icc.2 h12.le)
    obtain ⟨x₂, hx₂⟩ := ht₂A
    have hmem : t₂ ∈ Icc t₁ t₂ := ⟨h12.le, le_rfl⟩
    obtain ⟨hx₂T, heq⟩ := (hiff x₂ (δ t₂)).mp (hx₂.trans (hδ t₂ hmem).symm)
    have hTin' : δ t₂ ∈ Tin := by rw [heq]; exact hφ.1.mapsTo hx₂T
    obtain ⟨hb, hn⟩ := hTin.1 hTin'
    have hseg : segment ℝ t₂ t₁ = Icc t₁ t₂ := by rw [segment_symm, segment_eq_Icc h12.le]
    have hc : t₁ - t₂ ∈ posTangentConeAt (Icc t₁ t₂) t₂ :=
      sub_mem_posTangentConeAt_of_segment_subset hseg.subset
    have h1 := normalCoord_nonneg_of_hasMFDerivWithinAt δ (Icc t₁ t₂) t₂ (Y (δ t₂))
      (hδY t₂ hmem) hb (t₁ - t₂) hc
    have h2 := mul_neg_of_neg_of_pos (sub_neg.mpr h12) hn
    linarith
  obtain ⟨δX, hδX, hδXc⟩ := integralCurve_lift_of_embedding X Z iU hcU heU hdU hZU γ
    (Iic t₀) (hγ.isMIntegralCurveOn _) hbwd nonempty_Iic
  have hδX0 : δX t₀ = x := heU.injective ((hδX t₀ (le_refl t₀)).trans hx.symm)
  obtain ⟨δY, hδY, hδYc⟩ := integralCurve_lift_of_embedding Y Z iV hcV heV hdV hZV γ
    (Ici t₀) (hγ.isMIntegralCurveOn _) hfwd nonempty_Ici
  have hδY0 : δY t₀ = φ x := heV.injective ((hδY t₀ (le_refl t₀)).trans hy.symm)
  have hunst : x ∈ unstableSet X := by
    refine ⟨δX ∘ (· + t₀), by simp [hδX0], ?_⟩
    refine (hδXc.comp_add t₀).mono ?_
    intro u hu
    have hu' : u ≤ 0 := hu
    show u + t₀ ≤ t₀
    linarith
  have hst : φ x ∈ stableSet Y := by
    refine ⟨δY ∘ (· + t₀), by simp [hδY0], ?_⟩
    refine (hδYc.comp_add t₀).mono ?_
    intro u hu
    have hu' : 0 ≤ u := hu
    show t₀ ≤ u + t₀
    linarith
  refine ⟨x, ⟨⟨hunst, hTout.1 hxT⟩, hxT⟩, ⟨hst, hTin.1 (hφ.1.mapsTo hxT)⟩,
    γ ∘ (· + t₀), by simp [hx], hγ.comp_add t₀, ⟨-t₀, by simp [hγ0]⟩⟩
