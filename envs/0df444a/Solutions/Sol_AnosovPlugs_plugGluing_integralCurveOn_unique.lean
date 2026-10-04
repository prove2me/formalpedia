-- Prove2me | solution 1 for AnosovPlugs.plugGluing_integralCurveOn_unique
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-03T20:58:51.800151+00:00
-- url     : https://prove2.me/submissions/db7bfbc7-4805-42ba-9423-49f4507536c7

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing
import Theorems.Thm_AnosovPlugs_integralCurve_lift_of_embedding
import Theorems.Thm_AnosovPlugs_normalCoord_nonneg_of_hasMFDerivWithinAt
import Theorems.Thm_AnosovPlugs_integralCurveOn_uIcc_unique

open scoped Manifold ContDiff Topology
open Set AnosovPlugs

/-- A shift of `uIcc 0 (s - s₀)` by `s₀` lies in `uIcc s₀ s`. -/
theorem gu_shift_mem {s₀ s u : ℝ} (hu : u ∈ uIcc 0 (s - s₀)) : u + s₀ ∈ uIcc s₀ s := by
  rw [mem_uIcc] at hu ⊢
  rcases hu with h | h
  · left; constructor <;> linarith [h.1, h.2]
  · right; constructor <;> linarith [h.1, h.2]

/-- A point of `uIcc s₀ s` is not farther from `s₀` than `s` is. -/
theorem gu_dist {s₀ s u : ℝ} (hu : u ∈ uIcc s₀ s) : dist u s₀ ≤ dist s s₀ := by
  rw [Real.dist_eq, Real.dist_eq]
  rw [mem_uIcc] at hu
  rcases hu with h | h
  · rw [abs_of_nonneg (by linarith [h.1]), abs_of_nonneg (by linarith [h.1, h.2])]
    linarith [h.2]
  · rw [abs_of_nonpos (by linarith [h.2]), abs_of_nonpos (by linarith [h.1, h.2])]
    linarith [h.1]

/-- Uniqueness of integral curves of a C¹ field on `uIcc s₀ s`, from the base-time-zero form. -/
theorem gu_uniq_shift
    {P : Type} [TopologicalSpace P] [ChartedSpace (EuclideanHalfSpace 3) P] [IsManifold I3 ∞ P]
    [T2Space P]
    (X' : (x : P) → TangentSpace I3 x) (hX' : IsC1VectorField X') (δ δ' : ℝ → P) (s₀ s : ℝ)
    (hδ : IsMIntegralCurveOn δ X' (uIcc s₀ s)) (hδ' : IsMIntegralCurveOn δ' X' (uIcc s₀ s))
    (h0 : δ' s₀ = δ s₀) : δ' s = δ s := by
  have e1 : IsMIntegralCurveOn (δ ∘ (· + s₀)) X' (uIcc 0 (s - s₀)) :=
    (hδ.comp_add s₀).mono fun u hu => gu_shift_mem hu
  have e2 : IsMIntegralCurveOn (δ' ∘ (· + s₀)) X' (uIcc 0 (s - s₀)) :=
    (hδ'.comp_add s₀).mono fun u hu => gu_shift_mem hu
  have h0' : (δ' ∘ (· + s₀)) 0 = (δ ∘ (· + s₀)) 0 := by simpa using h0
  have key := integralCurveOn_uIcc_unique X' hX' _ _ (s - s₀) e1 e2 h0' (s - s₀) right_mem_uIcc
  simp only [Function.comp_apply, sub_add_cancel] at key
  exact key

/-- Two integral curves of `Z` on `uIcc s₀ s` that stay in the image of a C¹ embedding which
maps a C¹ field `X'` to `Z`, and that agree at `s₀`, agree at `s`. -/
theorem gu_lift
    {P : Type} [TopologicalSpace P] [ChartedSpace (EuclideanHalfSpace 3) P] [IsManifold I3 ∞ P]
    [T2Space P]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (X' : (x : P) → TangentSpace I3 x) (hX' : IsC1VectorField X')
    (Z : (w : N) → TangentSpace I3 w) (i : P → N)
    (hi : ContMDiff I3 I3 1 i) (hemb : Topology.IsEmbedding i)
    (hinj : ∀ x, Function.Injective (mfderiv I3 I3 i x))
    (hZ : ∀ x, mfderiv I3 I3 i x (X' x) = Z (i x))
    (γ γ' : ℝ → N) (s₀ s : ℝ)
    (hγ : IsMIntegralCurveOn γ Z (uIcc s₀ s)) (hγ' : IsMIntegralCurveOn γ' Z (uIcc s₀ s))
    (hr : ∀ u ∈ uIcc s₀ s, γ u ∈ range i) (hr' : ∀ u ∈ uIcc s₀ s, γ' u ∈ range i)
    (h0 : γ' s₀ = γ s₀) : γ' s = γ s := by
  obtain ⟨δ, hδ, hδX⟩ :=
    integralCurve_lift_of_embedding X' Z i hi hemb hinj hZ γ _ hγ hr ⟨s₀, left_mem_uIcc⟩
  obtain ⟨δ', hδ', hδX'⟩ :=
    integralCurve_lift_of_embedding X' Z i hi hemb hinj hZ γ' _ hγ' hr' ⟨s₀, left_mem_uIcc⟩
  have e : δ' s₀ = δ s₀ :=
    hemb.injective (by rw [hδ' _ left_mem_uIcc, hδ _ left_mem_uIcc, h0])
  rw [← hδ s right_mem_uIcc, ← hδ' s right_mem_uIcc, gu_uniq_shift X' hX' δ δ' s₀ s hδX hδX' e]

/-- Forward barrier: an integral curve of `Z` on `[a, b]` that starts in `range iV` stays in
`range iV`, because the field `X` points out of `U` at the seam `Tout`. -/
theorem gu_fwd
    {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U] [IsManifold I3 ∞ U]
    {V : Type} [TopologicalSpace V] [ChartedSpace (EuclideanHalfSpace 3) V] [IsManifold I3 ∞ V]
    {W : Type} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 3) W] [IsManifold I3 ∞ W]
    (X : (x : U) → TangentSpace I3 x) (Tout : Set U)
    (hTout : IsUnionOfComponents Tout (outBoundary X))
    (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W)
    (hcU : ContMDiff I3 I3 1 iU) (heU : Topology.IsEmbedding iU)
    (hdU : ∀ x, Function.Injective (mfderiv I3 I3 iU x))
    (hZU : ∀ x, mfderiv I3 I3 iU x (X x) = Z (iU x))
    (hUc : IsClosed (range iU)) (hVc : IsClosed (range iV))
    (hcover : range iU ∪ range iV = univ) (hiffU : ∀ x y, iU x = iV y → x ∈ Tout)
    (γ : ℝ → W) (a b : ℝ) (hγ : IsMIntegralCurveOn γ Z (Icc a b)) (ha : γ a ∈ range iV) :
    ∀ s ∈ Icc a b, γ s ∈ range iV := by
  intro s₁ hs₁
  by_contra h₁
  have hlt : a < s₁ := lt_of_le_of_ne hs₁.1 (fun h => h₁ (h ▸ ha))
  have hsub : Icc a s₁ ⊆ Icc a b := Icc_subset_Icc_right hs₁.2
  have hKc : IsClosed (Icc a s₁ ∩ γ ⁻¹' range iV) :=
    (hγ.continuousOn.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc hVc
  have hKne : (Icc a s₁ ∩ γ ⁻¹' range iV).Nonempty := ⟨a, ⟨le_rfl, hlt.le⟩, ha⟩
  have hKbdd : BddAbove (Icc a s₁ ∩ γ ⁻¹' range iV) := ⟨s₁, fun u hu => hu.1.2⟩
  have hmem : sSup (Icc a s₁ ∩ γ ⁻¹' range iV) ∈ Icc a s₁ ∩ γ ⁻¹' range iV :=
    hKc.csSup_mem hKne hKbdd
  set s₂ := sSup (Icc a s₁ ∩ γ ⁻¹' range iV) with hs₂
  have h2lt : s₂ < s₁ := lt_of_le_of_ne hmem.1.2 (fun h => h₁ (h ▸ hmem.2))
  have hsub2 : Icc s₂ s₁ ⊆ Icc a b := fun u hu => hsub ⟨hmem.1.1.trans hu.1, hu.2⟩
  have hIoc : Ioc s₂ s₁ ⊆ Icc s₂ s₁ ∩ γ ⁻¹' range iU := by
    intro u hu
    refine ⟨Ioc_subset_Icc_self hu, ?_⟩
    have hc : γ u ∈ range iU ∪ range iV := hcover ▸ mem_univ _
    refine hc.resolve_right fun huV => ?_
    have : u ≤ s₂ := le_csSup hKbdd ⟨⟨hmem.1.1.trans hu.1.le, hu.2⟩, huV⟩
    exact absurd hu.1 (not_lt.mpr this)
  have hAc : IsClosed (Icc s₂ s₁ ∩ γ ⁻¹' range iU) :=
    (hγ.continuousOn.mono hsub2).preimage_isClosed_of_isClosed isClosed_Icc hUc
  have hIcc : Icc s₂ s₁ ⊆ γ ⁻¹' range iU := by
    intro u hu
    rw [← closure_Ioc h2lt.ne] at hu
    exact (hAc.closure_subset_iff.mpr hIoc hu).2
  obtain ⟨δ, hδ, hδX⟩ := integralCurve_lift_of_embedding X Z iU hcU heU hdU hZU γ
    (Icc s₂ s₁) (hγ.mono hsub2) hIcc (nonempty_Icc.2 h2lt.le)
  obtain ⟨y₂, hy₂⟩ := hmem.2
  have hm : s₂ ∈ Icc s₂ s₁ := ⟨le_rfl, h2lt.le⟩
  have hT := hiffU (δ s₂) y₂ ((hδ s₂ hm).trans hy₂.symm)
  obtain ⟨hb, hn⟩ := hTout.1 hT
  have hc : s₁ - s₂ ∈ posTangentConeAt (Icc s₂ s₁) s₂ :=
    sub_mem_posTangentConeAt_of_segment_subset (segment_eq_Icc h2lt.le).subset
  have h1 := normalCoord_nonneg_of_hasMFDerivWithinAt δ (Icc s₂ s₁) s₂ (X (δ s₂))
    (hδX s₂ hm) hb (s₁ - s₂) hc
  have h2 := mul_neg_of_pos_of_neg (sub_pos.mpr h2lt) hn
  linarith

/-- Backward barrier: an integral curve of `Z` on `[a, b]` that ends in `range iU` lies in
`range iU`, because the field `Y` points into `V` at the seam `Tin`. -/
theorem gu_bwd
    {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U] [IsManifold I3 ∞ U]
    {V : Type} [TopologicalSpace V] [ChartedSpace (EuclideanHalfSpace 3) V] [IsManifold I3 ∞ V]
    {W : Type} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 3) W] [IsManifold I3 ∞ W]
    (Y : (y : V) → TangentSpace I3 y) (Tin : Set V)
    (hTin : IsUnionOfComponents Tin (inBoundary Y))
    (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W)
    (hcV : ContMDiff I3 I3 1 iV) (heV : Topology.IsEmbedding iV)
    (hdV : ∀ y, Function.Injective (mfderiv I3 I3 iV y))
    (hZV : ∀ y, mfderiv I3 I3 iV y (Y y) = Z (iV y))
    (hUc : IsClosed (range iU)) (hVc : IsClosed (range iV))
    (hcover : range iU ∪ range iV = univ) (hiffV : ∀ x y, iU x = iV y → y ∈ Tin)
    (γ : ℝ → W) (a b : ℝ) (hγ : IsMIntegralCurveOn γ Z (Icc a b)) (hb : γ b ∈ range iU) :
    ∀ s ∈ Icc a b, γ s ∈ range iU := by
  intro s₁ hs₁
  by_contra h₁
  have hlt : s₁ < b := lt_of_le_of_ne hs₁.2 (fun h => h₁ (h ▸ hb))
  have hsub : Icc s₁ b ⊆ Icc a b := Icc_subset_Icc_left hs₁.1
  have hKc : IsClosed (Icc s₁ b ∩ γ ⁻¹' range iU) :=
    (hγ.continuousOn.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc hUc
  have hKne : (Icc s₁ b ∩ γ ⁻¹' range iU).Nonempty := ⟨b, ⟨hlt.le, le_rfl⟩, hb⟩
  have hKbdd : BddBelow (Icc s₁ b ∩ γ ⁻¹' range iU) := ⟨s₁, fun u hu => hu.1.1⟩
  have hmem : sInf (Icc s₁ b ∩ γ ⁻¹' range iU) ∈ Icc s₁ b ∩ γ ⁻¹' range iU :=
    hKc.csInf_mem hKne hKbdd
  set s₂ := sInf (Icc s₁ b ∩ γ ⁻¹' range iU) with hs₂
  have h2lt : s₁ < s₂ := lt_of_le_of_ne hmem.1.1 (fun h => h₁ (h ▸ hmem.2))
  have hsub2 : Icc s₁ s₂ ⊆ Icc a b := fun u hu => hsub ⟨hu.1, hu.2.trans hmem.1.2⟩
  have hIco : Ico s₁ s₂ ⊆ Icc s₁ s₂ ∩ γ ⁻¹' range iV := by
    intro u hu
    refine ⟨Ico_subset_Icc_self hu, ?_⟩
    have hc : γ u ∈ range iU ∪ range iV := hcover ▸ mem_univ _
    refine hc.resolve_left fun huU => ?_
    have : s₂ ≤ u := csInf_le hKbdd ⟨⟨hu.1, hu.2.le.trans hmem.1.2⟩, huU⟩
    exact absurd hu.2 (not_lt.mpr this)
  have hAc : IsClosed (Icc s₁ s₂ ∩ γ ⁻¹' range iV) :=
    (hγ.continuousOn.mono hsub2).preimage_isClosed_of_isClosed isClosed_Icc hVc
  have hIcc : Icc s₁ s₂ ⊆ γ ⁻¹' range iV := by
    intro u hu
    rw [← closure_Ico h2lt.ne] at hu
    exact (hAc.closure_subset_iff.mpr hIco hu).2
  obtain ⟨δ, hδ, hδY⟩ := integralCurve_lift_of_embedding Y Z iV hcV heV hdV hZV γ
    (Icc s₁ s₂) (hγ.mono hsub2) hIcc (nonempty_Icc.2 h2lt.le)
  obtain ⟨x₂, hx₂⟩ := hmem.2
  have hm : s₂ ∈ Icc s₁ s₂ := ⟨h2lt.le, le_rfl⟩
  have hT := hiffV x₂ (δ s₂) (hx₂.trans (hδ s₂ hm).symm)
  obtain ⟨hbd, hn⟩ := hTin.1 hT
  have hseg : segment ℝ s₂ s₁ = Icc s₁ s₂ := by rw [segment_symm, segment_eq_Icc h2lt.le]
  have hc : s₁ - s₂ ∈ posTangentConeAt (Icc s₁ s₂) s₂ :=
    sub_mem_posTangentConeAt_of_segment_subset hseg.subset
  have h1 := normalCoord_nonneg_of_hasMFDerivWithinAt δ (Icc s₁ s₂) s₂ (Y (δ s₂))
    (hδY s₂ hm) hbd (s₁ - s₂) hc
  have h2 := mul_neg_of_neg_of_pos (sub_neg.mpr h2lt) hn
  linarith

/-- Local step, forward in time: near a time where two integral curves of `Z` agree, they agree
at later times. -/
theorem gu_local_fwd
    {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U] [IsManifold I3 ∞ U]
    [T2Space U]
    {V : Type} [TopologicalSpace V] [ChartedSpace (EuclideanHalfSpace 3) V] [IsManifold I3 ∞ V]
    [T2Space V]
    {W : Type} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 3) W] [IsManifold I3 ∞ W]
    (X : (x : U) → TangentSpace I3 x) (Y : (y : V) → TangentSpace I3 y)
    (hX1 : IsC1VectorField X) (hY1 : IsC1VectorField Y) (Tout : Set U)
    (hTout : IsUnionOfComponents Tout (outBoundary X))
    (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W)
    (hcU : ContMDiff I3 I3 1 iU) (hcV : ContMDiff I3 I3 1 iV)
    (heU : Topology.IsEmbedding iU) (heV : Topology.IsEmbedding iV)
    (hdU : ∀ x, Function.Injective (mfderiv I3 I3 iU x))
    (hdV : ∀ y, Function.Injective (mfderiv I3 I3 iV y))
    (hZU : ∀ x, mfderiv I3 I3 iU x (X x) = Z (iU x))
    (hZV : ∀ y, mfderiv I3 I3 iV y (Y y) = Z (iV y))
    (hUc : IsClosed (range iU)) (hVc : IsClosed (range iV))
    (hcover : range iU ∪ range iV = univ) (hiffU : ∀ x y, iU x = iV y → x ∈ Tout)
    (γ γ' : ℝ → W) (t : ℝ) (hγ : IsMIntegralCurveOn γ Z (uIcc 0 t))
    (hγ' : IsMIntegralCurveOn γ' Z (uIcc 0 t)) (s₀ : ℝ) (hs₀ : s₀ ∈ uIcc 0 t)
    (h : γ' s₀ = γ s₀) :
    ∃ ε > 0, ∀ s ∈ uIcc 0 t, s₀ ≤ s → dist s s₀ < ε → γ' s = γ s := by
  by_cases hw : γ s₀ ∈ range iV
  · refine ⟨1, one_pos, fun s hs hle _ => ?_⟩
    have hsub : uIcc s₀ s ⊆ uIcc 0 t := ordConnected_uIcc.uIcc_subset hs₀ hs
    have hI : uIcc s₀ s = Icc s₀ s := uIcc_of_le hle
    have hγs : IsMIntegralCurveOn γ Z (Icc s₀ s) := hI ▸ hγ.mono hsub
    have hγs' : IsMIntegralCurveOn γ' Z (Icc s₀ s) := hI ▸ hγ'.mono hsub
    refine gu_lift Y hY1 Z iV hcV heV hdV hZV γ γ' s₀ s (hγ.mono hsub) (hγ'.mono hsub) ?_ ?_ h
    · rw [hI]
      exact gu_fwd X Tout hTout Z iU iV hcU heU hdU hZU hUc hVc hcover hiffU γ s₀ s hγs hw
    · rw [hI]
      exact gu_fwd X Tout hTout Z iU iV hcU heU hdU hZU hUc hVc hcover hiffU γ' s₀ s hγs'
        (h ▸ hw)
  · have hR : (range iV)ᶜ ∈ 𝓝 (γ s₀) := hVc.isOpen_compl.mem_nhds hw
    have hR' : (range iV)ᶜ ∈ 𝓝 (γ' s₀) := by rw [h]; exact hR
    obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.mem_nhdsWithin_iff.1 ((hγ.continuousWithinAt hs₀) hR)
    obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.mem_nhdsWithin_iff.1 ((hγ'.continuousWithinAt hs₀) hR')
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun s hs _ hds => ?_⟩
    have hsub : uIcc s₀ s ⊆ uIcc 0 t := ordConnected_uIcc.uIcc_subset hs₀ hs
    have hd : ∀ u ∈ uIcc s₀ s, dist u s₀ < min ε₁ ε₂ := fun u hu =>
      lt_of_le_of_lt (gu_dist hu) hds
    have hU : ∀ w : W, w ∉ range iV → w ∈ range iU := fun w hw' =>
      (show w ∈ range iU ∪ range iV from hcover ▸ mem_univ _).resolve_right hw'
    refine gu_lift X hX1 Z iU hcU heU hdU hZU γ γ' s₀ s (hγ.mono hsub) (hγ'.mono hsub)
      (fun u hu => hU _ (hb₁ ⟨Metric.mem_ball.2 ((hd u hu).trans_le (min_le_left _ _)),
        hsub hu⟩))
      (fun u hu => hU _ (hb₂ ⟨Metric.mem_ball.2 ((hd u hu).trans_le (min_le_right _ _)),
        hsub hu⟩)) h

/-- Local step, backward in time: near a time where two integral curves of `Z` agree, they agree
at earlier times. -/
theorem gu_local_bwd
    {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U] [IsManifold I3 ∞ U]
    [T2Space U]
    {V : Type} [TopologicalSpace V] [ChartedSpace (EuclideanHalfSpace 3) V] [IsManifold I3 ∞ V]
    [T2Space V]
    {W : Type} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 3) W] [IsManifold I3 ∞ W]
    (X : (x : U) → TangentSpace I3 x) (Y : (y : V) → TangentSpace I3 y)
    (hX1 : IsC1VectorField X) (hY1 : IsC1VectorField Y) (Tin : Set V)
    (hTin : IsUnionOfComponents Tin (inBoundary Y))
    (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W)
    (hcU : ContMDiff I3 I3 1 iU) (hcV : ContMDiff I3 I3 1 iV)
    (heU : Topology.IsEmbedding iU) (heV : Topology.IsEmbedding iV)
    (hdU : ∀ x, Function.Injective (mfderiv I3 I3 iU x))
    (hdV : ∀ y, Function.Injective (mfderiv I3 I3 iV y))
    (hZU : ∀ x, mfderiv I3 I3 iU x (X x) = Z (iU x))
    (hZV : ∀ y, mfderiv I3 I3 iV y (Y y) = Z (iV y))
    (hUc : IsClosed (range iU)) (hVc : IsClosed (range iV))
    (hcover : range iU ∪ range iV = univ) (hiffV : ∀ x y, iU x = iV y → y ∈ Tin)
    (γ γ' : ℝ → W) (t : ℝ) (hγ : IsMIntegralCurveOn γ Z (uIcc 0 t))
    (hγ' : IsMIntegralCurveOn γ' Z (uIcc 0 t)) (s₀ : ℝ) (hs₀ : s₀ ∈ uIcc 0 t)
    (h : γ' s₀ = γ s₀) :
    ∃ ε > 0, ∀ s ∈ uIcc 0 t, s ≤ s₀ → dist s s₀ < ε → γ' s = γ s := by
  by_cases hw : γ s₀ ∈ range iU
  · refine ⟨1, one_pos, fun s hs hle _ => ?_⟩
    have hsub : uIcc s₀ s ⊆ uIcc 0 t := ordConnected_uIcc.uIcc_subset hs₀ hs
    have hI : uIcc s₀ s = Icc s s₀ := uIcc_of_ge hle
    have hγs : IsMIntegralCurveOn γ Z (Icc s s₀) := hI ▸ hγ.mono hsub
    have hγs' : IsMIntegralCurveOn γ' Z (Icc s s₀) := hI ▸ hγ'.mono hsub
    refine gu_lift X hX1 Z iU hcU heU hdU hZU γ γ' s₀ s (hγ.mono hsub) (hγ'.mono hsub) ?_ ?_ h
    · rw [hI]
      exact gu_bwd Y Tin hTin Z iU iV hcV heV hdV hZV hUc hVc hcover hiffV γ s s₀ hγs hw
    · rw [hI]
      exact gu_bwd Y Tin hTin Z iU iV hcV heV hdV hZV hUc hVc hcover hiffV γ' s s₀ hγs'
        (h ▸ hw)
  · have hR : (range iU)ᶜ ∈ 𝓝 (γ s₀) := hUc.isOpen_compl.mem_nhds hw
    have hR' : (range iU)ᶜ ∈ 𝓝 (γ' s₀) := by rw [h]; exact hR
    obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.mem_nhdsWithin_iff.1 ((hγ.continuousWithinAt hs₀) hR)
    obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.mem_nhdsWithin_iff.1 ((hγ'.continuousWithinAt hs₀) hR')
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun s hs _ hds => ?_⟩
    have hsub : uIcc s₀ s ⊆ uIcc 0 t := ordConnected_uIcc.uIcc_subset hs₀ hs
    have hd : ∀ u ∈ uIcc s₀ s, dist u s₀ < min ε₁ ε₂ := fun u hu =>
      lt_of_le_of_lt (gu_dist hu) hds
    have hV : ∀ w : W, w ∉ range iU → w ∈ range iV := fun w hw' =>
      (show w ∈ range iU ∪ range iV from hcover ▸ mem_univ _).resolve_left hw'
    refine gu_lift Y hY1 Z iV hcV heV hdV hZV γ γ' s₀ s (hγ.mono hsub) (hγ'.mono hsub)
      (fun u hu => hV _ (hb₁ ⟨Metric.mem_ball.2 ((hd u hu).trans_le (min_le_left _ _)),
        hsub hu⟩))
      (fun u hu => hV _ (hb₂ ⟨Metric.mem_ball.2 ((hd u hu).trans_le (min_le_right _ _)),
        hsub hu⟩)) h

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
    ∀ (γ γ' : ℝ → W) (t : ℝ), IsMIntegralCurveOn γ Z (uIcc 0 t) → IsMIntegralCurveOn γ' Z (uIcc 0 t) →
      γ' 0 = γ 0 → ∀ s ∈ uIcc 0 t, γ' s = γ s := by
  intro γ γ' t hγ hγ' h0
  obtain ⟨hcU, hcV, heU, heV, hdU, hdV, hcover, hiff, hZU, hZV⟩ := hglue
  have hUc : IsClosed (range iU) := (isCompact_range hcU.continuous).isClosed
  have hVc : IsClosed (range iV) := (isCompact_range hcV.continuous).isClosed
  have hiffU : ∀ x y, iU x = iV y → x ∈ Tout := fun x y hxy => ((hiff x y).mp hxy).1
  have hiffV : ∀ x y, iU x = iV y → y ∈ Tin := fun x y hxy => by
    obtain ⟨hx, rfl⟩ := (hiff x y).mp hxy
    exact hφ.1.mapsTo hx
  have : PreconnectedSpace (uIcc (0 : ℝ) t) := Subtype.preconnectedSpace isPreconnected_uIcc
  set S : Set (uIcc (0 : ℝ) t) := {x | γ' x = γ x} with hS
  have hclosed : IsClosed S :=
    isClosed_eq hγ'.continuousOn.domRestrict hγ.continuousOn.domRestrict
  have hopen : IsOpen S := by
    rw [Metric.isOpen_iff]
    rintro ⟨s₀, hs₀⟩ hx
    obtain ⟨ε₁, hε₁, h₁⟩ := gu_local_fwd X Y hX.1 hY.1 Tout hTout Z iU iV hcU hcV heU heV
      hdU hdV hZU hZV hUc hVc hcover hiffU γ γ' t hγ hγ' s₀ hs₀ hx
    obtain ⟨ε₂, hε₂, h₂⟩ := gu_local_bwd X Y hX.1 hY.1 Tin hTin Z iU iV hcU hcV heU heV
      hdU hdV hZU hZV hUc hVc hcover hiffV γ γ' t hγ hγ' s₀ hs₀ hx
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
    rintro ⟨s, hs⟩ hds
    have hds' : dist s s₀ < min ε₁ ε₂ := hds
    rcases le_total s₀ s with hle | hle
    · exact h₁ s hs hle (hds'.trans_le (min_le_left _ _))
    · exact h₂ s hs hle (hds'.trans_le (min_le_right _ _))
  have huniv : S = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨0, left_mem_uIcc⟩, h0⟩
  intro s hs
  have : (⟨s, hs⟩ : uIcc (0 : ℝ) t) ∈ S := huniv ▸ mem_univ _
  exact this
