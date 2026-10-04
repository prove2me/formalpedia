-- Prove2me | solution 1 for AnosovPlugs.integralCurveOn_eq_comp_of_embedding
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-03T09:01:18.218783+00:00
-- url     : https://prove2.me/submissions/120d64ad-7cbc-43c1-87b8-6efff61754b0

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing
import Theorems.Thm_AnosovPlugs_integralCurve_lift_of_embedding

open scoped Manifold ContDiff Topology
open Set
open AnosovPlugs

section UIccHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {v : (x : M) → TangentSpace I x}

/-- Change the base point in the derivative `smulRight (v p)` to `f s` when `f s = p`. -/
theorem uIccAux_congr_pt {f : ℝ → M} {S : Set ℝ} {s : ℝ} {p : M}
    (h : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f S s ((1 : ℝ →L[ℝ] ℝ).smulRight (v p)))
    (hp : f s = p) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f S s ((1 : ℝ →L[ℝ] ℝ).smulRight (v (f s))) := by
  subst hp
  exact h

/-- Change the point `p` in the derivative `smulRight (v p)` to an equal point `q`. -/
theorem uIccAux_congr_val {f : ℝ → M} {S : Set ℝ} {s : ℝ} {p q : M}
    (h : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f S s ((1 : ℝ →L[ℝ] ℝ).smulRight (v p)))
    (hp : p = q) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f S s ((1 : ℝ →L[ℝ] ℝ).smulRight (v q)) := by
  subst hp
  exact h

/-- Gluing at the left endpoint: an integral curve `γ` on `(a - ε, a + ε)` before `a`, and an
integral curve `γ'` on `[a, b]` with `γ' a = γ a`, give an integral curve on `(a - ε, b)`. -/
theorem uIccAux_glue_left {γ γ' : ℝ → M} {a b ε : ℝ}
    (hγ : IsMIntegralCurveOn γ v (Ioo (a - ε) (a + ε))) (hε : 0 < ε)
    (hγ' : IsMIntegralCurveOn γ' v (Icc a b)) (hab : a < b)
    (h0 : γ' a = γ a) :
    IsMIntegralCurveOn (fun s => if s < a then γ s else γ' s) v (Ioo (a - ε) b) := by
  intro s hs
  rcases lt_trichotomy s a with hsa | rfl | hsa
  · have k := (hγ s ⟨hs.1, by linarith⟩).hasMFDerivAt (Ioo_mem_nhds hs.1 (by linarith))
    have e : (fun s => if s < a then γ s else γ' s) =ᶠ[𝓝 s] γ := by
      filter_upwards [Iio_mem_nhds hsa] with u hu
      simp [show u < a from hu]
    refine uIccAux_congr_pt (k.congr_of_eventuallyEq e).hasMFDerivWithinAt ?_
    simp [hsa]
  · have k0 := (hγ s ⟨by linarith, by linarith⟩).hasMFDerivAt
      (Ioo_mem_nhds (by linarith) (by linarith))
    have h1 : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u => if u < s then γ u else γ' u) (Iic s) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ s))) := by
      refine k0.hasMFDerivWithinAt.congr_mono ?_ ?_ (subset_univ _)
      · intro u hu
        rcases eq_or_lt_of_le (show u ≤ s from hu) with rfl | hu
        · simp [h0]
        · simp [hu]
      · simp [h0]
    have h2 : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u => if u < s then γ u else γ' u) (Ici s) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ s))) := by
      have k := (hγ' s ⟨le_rfl, hab.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hab)
      have k' := k.congr_mono (f₁ := fun u => if u < s then γ u else γ' u) (t := Ici s)
        (fun u hu => by simp [not_lt.mpr (show s ≤ u from hu)]) (by simp) le_rfl
      exact uIccAux_congr_val k' h0
    have h3 := h1.union h2
    rw [Iic_union_Ici] at h3
    refine uIccAux_congr_pt (h3.mono (subset_univ _)) ?_
    simp [h0]
  · have k := (hγ' s ⟨hsa.le, hs.2.le⟩).hasMFDerivAt (Icc_mem_nhds hsa hs.2)
    have e : (fun s => if s < a then γ s else γ' s) =ᶠ[𝓝 s] γ' := by
      filter_upwards [Ioi_mem_nhds hsa] with u hu
      simp [not_lt.mpr (le_of_lt (show a < u from hu))]
    refine uIccAux_congr_pt (k.congr_of_eventuallyEq e).hasMFDerivWithinAt ?_
    simp [not_lt.mpr hsa.le]

/-- Gluing at the right endpoint. -/
theorem uIccAux_glue_right {γ γ' : ℝ → M} {a b ε : ℝ}
    (hγ : IsMIntegralCurveOn γ v (Ioo (b - ε) (b + ε))) (hε : 0 < ε)
    (hγ' : IsMIntegralCurveOn γ' v (Icc a b)) (hab : a < b)
    (h0 : γ' b = γ b) :
    IsMIntegralCurveOn (fun s => if b < s then γ s else γ' s) v (Ioo a (b + ε)) := by
  intro s hs
  rcases lt_trichotomy s b with hsb | rfl | hsb
  · have k := (hγ' s ⟨hs.1.le, hsb.le⟩).hasMFDerivAt (Icc_mem_nhds hs.1 hsb)
    have e : (fun s => if b < s then γ s else γ' s) =ᶠ[𝓝 s] γ' := by
      filter_upwards [Iio_mem_nhds hsb] with u hu
      simp [not_lt.mpr (le_of_lt (show u < b from hu))]
    refine uIccAux_congr_pt (k.congr_of_eventuallyEq e).hasMFDerivWithinAt ?_
    simp [not_lt.mpr hsb.le]
  · have k0 := (hγ s ⟨by linarith, by linarith⟩).hasMFDerivAt
      (Ioo_mem_nhds (by linarith) (by linarith))
    have h1 : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u => if s < u then γ u else γ' u) (Ici s) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ s))) := by
      refine k0.hasMFDerivWithinAt.congr_mono ?_ ?_ (subset_univ _)
      · intro u hu
        rcases eq_or_lt_of_le (show s ≤ u from hu) with rfl | hu
        · simp [h0]
        · simp [hu]
      · simp [h0]
    have h2 : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u => if s < u then γ u else γ' u) (Iic s) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ s))) := by
      have k := (hγ' s ⟨hab.le, le_rfl⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hab)
      have k' := k.congr_mono (f₁ := fun u => if s < u then γ u else γ' u) (t := Iic s)
        (fun u hu => by simp [not_lt.mpr (show u ≤ s from hu)]) (by simp) le_rfl
      exact uIccAux_congr_val k' h0
    have h3 := h2.union h1
    rw [Iic_union_Ici] at h3
    refine uIccAux_congr_pt (h3.mono (subset_univ _)) ?_
    simp [h0]
  · have k := (hγ s ⟨by linarith, hs.2⟩).hasMFDerivAt (Ioo_mem_nhds (by linarith) hs.2)
    have e : (fun s => if b < s then γ s else γ' s) =ᶠ[𝓝 s] γ := by
      filter_upwards [Ioi_mem_nhds hsb] with u hu
      simp [show b < u from hu]
    refine uIccAux_congr_pt (k.congr_of_eventuallyEq e).hasMFDerivWithinAt ?_
    simp [hsb]

variable [IsManifold I 1 M]

/-- Short-time integral curve through an interior point, staying in the interior. -/
theorem uIccAux_short [CompleteSpace E] {x₀ : M} (t₀ : ℝ)
    (hv : ContMDiffAt I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)) x₀)
    (hx : I.IsInteriorPoint x₀) :
    ∃ η : ℝ → M, ∃ ε : ℝ, 0 < ε ∧ η t₀ = x₀ ∧
      IsMIntegralCurveOn η v (Ioo (t₀ - ε) (t₀ + ε)) ∧
      ∀ s ∈ Ioo (t₀ - ε) (t₀ + ε), I.IsInteriorPoint (η s) := by
  obtain ⟨η, hη0, hη⟩ := exists_isMIntegralCurveAt_of_contMDiffAt t₀ hv hx
  have hB : ∀ᶠ t in 𝓝 t₀, η t ∈ I.interior M :=
    hη.continuousAt.preimage_mem_nhds
      ((I.isOpen_interior (n := 1) (M := M) one_ne_zero).mem_nhds (by rw [hη0]; exact hx))
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff_ball.mp (hη.and hB)
  refine ⟨η, ε, hε, hη0, ?_, ?_⟩
  · intro s hs
    rw [← Real.ball_eq_Ioo] at hs
    exact (hall s hs).1.hasMFDerivWithinAt
  · intro s hs
    rw [← Real.ball_eq_Ioo] at hs
    exact (hall s hs).2

variable [T2Space M]

/-- Uniqueness forward on `[a, b]` when the first curve runs through interior points. -/
theorem uIccAux_eq_right {η γ γ' : ℝ → M} {a b ε : ℝ}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (hη : IsMIntegralCurveOn η v (Ioo (a - ε) (a + ε)))
    (hηint : ∀ s ∈ Ioo (a - ε) (a + ε), I.IsInteriorPoint (η s)) (hε : 0 < ε)
    (hγ : IsMIntegralCurveOn γ v (Icc a b)) (hint : ∀ s ∈ Icc a b, I.IsInteriorPoint (γ s))
    (hγ' : IsMIntegralCurveOn γ' v (Icc a b)) (hab : a < b)
    (h0 : γ a = η a) (h0' : γ' a = η a) :
    ∀ s ∈ Icc a b, γ' s = γ s := by
  have hGint : ∀ s ∈ Ioo (a - ε) b,
      I.IsInteriorPoint ((fun s => if s < a then η s else γ s) s) := by
    intro s hs
    show I.IsInteriorPoint (if s < a then η s else γ s)
    by_cases hsa : s < a
    · rw [if_pos hsa]; exact hηint s ⟨hs.1, by linarith⟩
    · rw [if_neg hsa]; exact hint s ⟨not_lt.mp hsa, hs.2.le⟩
  have hlt : a - ε / 2 < a := by linarith
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff (t₀ := a - ε / 2)
    (by constructor <;> linarith) hGint hv
    (uIccAux_glue_left hη hε hγ hab h0) (uIccAux_glue_left hη hε hγ' hab h0')
    (by show (if _ < a then _ else _) = (if _ < a then _ else _); rw [if_pos hlt, if_pos hlt])
  have hIco : ∀ s ∈ Ico a b, γ' s = γ s := by
    intro s hs
    have := heq ⟨by linarith [hs.1], hs.2⟩
    simp only [not_lt.mpr hs.1, if_false] at this
    exact this.symm
  have c1 : ContinuousWithinAt γ' (Ico a b) b :=
    (hγ'.continuousWithinAt ⟨hab.le, le_rfl⟩).mono Ico_subset_Icc_self
  have c2 : ContinuousWithinAt γ (Ico a b) b :=
    (hγ.continuousWithinAt ⟨hab.le, le_rfl⟩).mono Ico_subset_Icc_self
  have : Filter.NeBot (𝓝[Ico a b] b) := by
    rw [nhdsWithin_Ico_eq_nhdsLT hab]; infer_instance
  have hev : γ' =ᶠ[𝓝[Ico a b] b] γ :=
    Filter.mem_of_superset self_mem_nhdsWithin (fun s hs => hIco s hs)
  intro s hs
  rcases eq_or_lt_of_le hs.2 with rfl | hsb
  · exact tendsto_nhds_unique c1.tendsto (c2.tendsto.congr' hev.symm)
  · exact hIco s ⟨hs.1, hsb⟩

/-- Uniqueness backward on `[a, b]` when the first curve runs through interior points. -/
theorem uIccAux_eq_left {η γ γ' : ℝ → M} {a b ε : ℝ}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (hη : IsMIntegralCurveOn η v (Ioo (b - ε) (b + ε)))
    (hηint : ∀ s ∈ Ioo (b - ε) (b + ε), I.IsInteriorPoint (η s)) (hε : 0 < ε)
    (hγ : IsMIntegralCurveOn γ v (Icc a b)) (hint : ∀ s ∈ Icc a b, I.IsInteriorPoint (γ s))
    (hγ' : IsMIntegralCurveOn γ' v (Icc a b)) (hab : a < b)
    (h0 : γ b = η b) (h0' : γ' b = η b) :
    ∀ s ∈ Icc a b, γ' s = γ s := by
  have hGint : ∀ s ∈ Ioo a (b + ε),
      I.IsInteriorPoint ((fun s => if b < s then η s else γ s) s) := by
    intro s hs
    show I.IsInteriorPoint (if b < s then η s else γ s)
    by_cases hsb : b < s
    · rw [if_pos hsb]; exact hηint s ⟨by linarith, hs.2⟩
    · rw [if_neg hsb]; exact hint s ⟨hs.1.le, not_lt.mp hsb⟩
  have hlt : b < b + ε / 2 := by linarith
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff (t₀ := b + ε / 2)
    (by constructor <;> linarith) hGint hv
    (uIccAux_glue_right hη hε hγ hab h0) (uIccAux_glue_right hη hε hγ' hab h0')
    (by show (if b < _ then _ else _) = (if b < _ then _ else _); rw [if_pos hlt, if_pos hlt])
  have hIoc : ∀ s ∈ Ioc a b, γ' s = γ s := by
    intro s hs
    have := heq ⟨hs.1, by linarith [hs.2]⟩
    simp only [not_lt.mpr hs.2, if_false] at this
    exact this.symm
  have c1 : ContinuousWithinAt γ' (Ioc a b) a :=
    (hγ'.continuousWithinAt ⟨le_rfl, hab.le⟩).mono Ioc_subset_Icc_self
  have c2 : ContinuousWithinAt γ (Ioc a b) a :=
    (hγ.continuousWithinAt ⟨le_rfl, hab.le⟩).mono Ioc_subset_Icc_self
  have : Filter.NeBot (𝓝[Ioc a b] a) := by
    rw [nhdsWithin_Ioc_eq_nhdsGT hab]; infer_instance
  have hev : γ' =ᶠ[𝓝[Ioc a b] a] γ :=
    Filter.mem_of_superset self_mem_nhdsWithin (fun s hs => hIoc s hs)
  intro s hs
  rcases eq_or_lt_of_le hs.1 with rfl | has
  · exact tendsto_nhds_unique c1.tendsto (c2.tendsto.congr' hev.symm)
  · exact hIoc s ⟨has, hs.2⟩

end UIccHelpers

theorem r4_range_mem_nhds_aux
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (i : M → N) (hi : ContMDiff I3 I3 1 i) (x : M) (hx : I3.IsInteriorPoint x)
    (hinj : Function.Injective (mfderiv I3 I3 i x)) :
    range i ∈ 𝓝 (i x) := by
  set φ := extChartAt I3 x with hφ
  set ψ := extChartAt I3 (i x) with hψ
  set a := φ x with ha
  set F := writtenInExtChartAt I3 I3 x i with hFdef
  let D : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) := mfderiv I3 I3 i x
  have hDinj : Function.Injective D := hinj
  let Dₑ : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (LinearEquiv.ofInjectiveEndo
      (D : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) hDinj).toContinuousLinearEquiv
  have hDₑ : (Dₑ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) = D := by
    ext v
    simp [Dₑ, LinearEquiv.coe_ofInjectiveEndo]
  have hrange : range I3 ∈ 𝓝 a := range_mem_nhds_isInteriorPoint hx
  have hcd : ContDiffWithinAt ℝ 1 F (range I3) a := (contMDiffAt_iff.1 (hi x)).2
  have hcda : ContDiffAt ℝ 1 F a := hcd.contDiffAt hrange
  have hstrict : HasStrictFDerivAt F (fderiv ℝ F a) a := hcda.hasStrictFDerivAt one_ne_zero
  have hFw : HasFDerivWithinAt F D (range I3) a :=
    ((hi x).mdifferentiableAt one_ne_zero).hasMFDerivAt.2
  have hF : HasFDerivAt F D a := hFw.hasFDerivAt hrange
  have heq : fderiv ℝ F a = D := hF.fderiv
  have hstrict' : HasStrictFDerivAt F
      (Dₑ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) a := by
    rw [hDₑ, ← heq]; exact hstrict
  have hmap : Filter.map F (𝓝 a) = 𝓝 (F a) := hstrict'.map_nhds_eq_of_equiv
  have hFa : F a = ψ (i x) := by
    simp only [hFdef, writtenInExtChartAt, Function.comp_apply, ha, hφ, extChartAt_to_inv]
    rfl
  set S := φ.source ∩ i ⁻¹' ψ.source with hS
  have hSn : S ∈ 𝓝 x :=
    Filter.inter_mem (extChartAt_source_mem_nhds x)
      ((hi x).continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (i x)))
  have hφS : φ '' S ∈ 𝓝 a :=
    extChartAt_image_nhds_mem_nhds_of_mem_interior_range (mem_extChartAt_source x) hx hSn
  have hFS : F '' (φ '' S) ∈ 𝓝 (ψ (i x)) := by
    rw [← hFa, ← hmap]; exact Filter.image_mem_map hφS
  have hsub : F '' (φ '' S) ⊆ ψ '' (i '' S) := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨i y, ⟨y, hy, rfl⟩, ?_⟩
    simp only [hFdef, writtenInExtChartAt, Function.comp_apply]
    rw [PartialEquiv.left_inv _ hy.1]
  have h1 : ψ ⁻¹' (ψ '' (i '' S)) ∈ 𝓝 (i x) :=
    (continuousAt_extChartAt (i x)).preimage_mem_nhds (Filter.mem_of_superset hFS hsub)
  refine Filter.mem_of_superset (Filter.inter_mem h1 (extChartAt_source_mem_nhds (I := I3) (i x))) ?_
  rintro w ⟨⟨_, ⟨y, hy, rfl⟩, hwy⟩, hw⟩
  exact ⟨y, (extChartAt I3 (i x)).injOn hy.2 hw hwy⟩

theorem r4_uIcc_eq_aux
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    [T2Space M]
    (X : (x : M) → TangentSpace I3 x) (hX : IsC1VectorField X) (γ γ' : ℝ → M) (t : ℝ)
    (hγ : IsMIntegralCurveOn γ X (uIcc 0 t)) (hint : ∀ s ∈ uIcc 0 t, I3.IsInteriorPoint (γ s))
    (hγ' : IsMIntegralCurveOn γ' X (uIcc 0 t)) (h0 : γ' 0 = γ 0) :
    ∀ s ∈ uIcc 0 t, γ' s = γ s := by
  have hX' : ContMDiff I3 I3.tangent 1 (fun x => (⟨x, X x⟩ : TangentBundle I3 M)) := hX
  obtain ⟨η, ε, hε, hη0, hη, hηint⟩ :=
    uIccAux_short (v := X) 0 (hX' (γ 0)) (hint 0 left_mem_uIcc)
  rcases lt_trichotomy 0 t with ht | rfl | ht
  · rw [uIcc_of_le ht.le] at hγ hint hγ' ⊢
    exact uIccAux_eq_right hX' hη hηint hε hγ hint hγ' ht hη0.symm (h0.trans hη0.symm)
  · intro s hs
    rw [uIcc_self, mem_singleton_iff] at hs
    subst hs
    exact h0
  · rw [uIcc_of_ge ht.le] at hγ hint hγ' ⊢
    exact uIccAux_eq_left hX' hη hηint hε hγ hint hγ' ht hη0.symm (h0.trans hη0.symm)

/-- A shift of `uIcc 0 (s - s₀)` by `s₀` lies in `uIcc s₀ s`. -/
theorem r4_shift_mem_uIcc {s₀ s u : ℝ} (hu : u ∈ uIcc 0 (s - s₀)) : u + s₀ ∈ uIcc s₀ s := by
  rw [mem_uIcc] at hu ⊢
  rcases hu with h | h
  · left; constructor <;> linarith [h.1, h.2]
  · right; constructor <;> linarith [h.1, h.2]

/-- Local step: near a time where the two curves agree, they agree. -/
theorem r4_local_eq
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    [T2Space M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (X : (x : M) → TangentSpace I3 x) (Z : (w : N) → TangentSpace I3 w) (i : M → N)
    (hX : IsC1VectorField X) (hi : ContMDiff I3 I3 1 i) (hemb : Topology.IsEmbedding i)
    (hinj : ∀ x, Function.Injective (mfderiv I3 I3 i x))
    (hZ : ∀ x, mfderiv I3 I3 i x (X x) = Z (i x))
    (δ : ℝ → M) (t : ℝ) (hδ : IsMIntegralCurveOn δ X (uIcc 0 t))
    (hint : ∀ s ∈ uIcc 0 t, I3.IsInteriorPoint (δ s))
    (γ : ℝ → N) (hγ : IsMIntegralCurveOn γ Z (uIcc 0 t))
    (s₀ : ℝ) (hs₀ : s₀ ∈ uIcc 0 t) (h : γ s₀ = i (δ s₀)) :
    ∃ ε > 0, ∀ s ∈ uIcc 0 t, dist s s₀ < ε → γ s = i (δ s) := by
  have hR : range i ∈ 𝓝 (γ s₀) := by
    rw [h]; exact r4_range_mem_nhds_aux i hi (δ s₀) (hint s₀ hs₀) (hinj _)
  have hpre : γ ⁻¹' range i ∈ 𝓝[uIcc 0 t] s₀ := (hγ.continuousWithinAt hs₀) hR
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  refine ⟨ε, hε, ?_⟩
  set J : Set ℝ := uIcc 0 t ∩ Metric.ball s₀ ε with hJ
  have hJS : J ⊆ uIcc 0 t := inter_subset_left
  have hs₀J : s₀ ∈ J := ⟨hs₀, Metric.mem_ball_self hε⟩
  have hJord : J.OrdConnected := by
    rw [hJ, Real.ball_eq_Ioo]; exact OrdConnected.inter ordConnected_uIcc ordConnected_Ioo
  have hrange : ∀ u ∈ J, γ u ∈ range i := fun u hu => hball ⟨hu.2, hu.1⟩
  obtain ⟨η, hηeq, hηX⟩ := integralCurve_lift_of_embedding X Z i hi hemb hinj hZ γ J
    (hγ.mono hJS) hrange ⟨s₀, hs₀J⟩
  have hη0 : η s₀ = δ s₀ := hemb.injective ((hηeq s₀ hs₀J).trans h)
  intro s hs hds
  have hsJ : s ∈ J := ⟨hs, hds⟩
  have hsub : uIcc s₀ s ⊆ J := hJord.uIcc_subset hs₀J hsJ
  have hδ' : IsMIntegralCurveOn (δ ∘ (· + s₀)) X (uIcc 0 (s - s₀)) :=
    (hδ.comp_add s₀).mono fun u hu => hJS (hsub (r4_shift_mem_uIcc hu))
  have hη' : IsMIntegralCurveOn (η ∘ (· + s₀)) X (uIcc 0 (s - s₀)) :=
    (hηX.comp_add s₀).mono fun u hu => hsub (r4_shift_mem_uIcc hu)
  have hint' : ∀ u ∈ uIcc 0 (s - s₀), I3.IsInteriorPoint ((δ ∘ (· + s₀)) u) :=
    fun u hu => hint _ (hJS (hsub (r4_shift_mem_uIcc hu)))
  have h0' : (η ∘ (· + s₀)) 0 = (δ ∘ (· + s₀)) 0 := by simpa using hη0
  have key := r4_uIcc_eq_aux X hX _ _ (s - s₀) hδ' hint' hη' h0' (s - s₀) right_mem_uIcc
  simp only [Function.comp_apply, sub_add_cancel] at key
  rw [← hηeq s hsJ, key]

theorem solution
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    [T2Space M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    [T2Space N]
    (X : (x : M) → TangentSpace I3 x) (Z : (w : N) → TangentSpace I3 w) (i : M → N)
    (hX : IsC1VectorField X) (hi : ContMDiff I3 I3 1 i) (hemb : Topology.IsEmbedding i)
    (hinj : ∀ x, Function.Injective (mfderiv I3 I3 i x))
    (hZ : ∀ x, mfderiv I3 I3 i x (X x) = Z (i x))
    (δ : ℝ → M) (t : ℝ) (hδ : IsMIntegralCurveOn δ X (uIcc 0 t))
    (hint : ∀ s ∈ uIcc 0 t, I3.IsInteriorPoint (δ s))
    (γ : ℝ → N) (hγ : IsMIntegralCurveOn γ Z (uIcc 0 t)) (h0 : γ 0 = i (δ 0)) :
    ∀ s ∈ uIcc 0 t, γ s = i (δ s) := by
  have : PreconnectedSpace (uIcc (0 : ℝ) t) := Subtype.preconnectedSpace isPreconnected_uIcc
  set U : Set (uIcc (0 : ℝ) t) := {x | γ x = i (δ x)} with hU
  have hclosed : IsClosed U :=
    isClosed_eq hγ.continuousOn.domRestrict (hi.continuous.comp_continuousOn hδ.continuousOn).domRestrict
  have hopen : IsOpen U := by
    rw [Metric.isOpen_iff]
    rintro ⟨s₀, hs₀⟩ hx
    obtain ⟨ε, hε, hloc⟩ :=
      r4_local_eq X Z i hX hi hemb hinj hZ δ t hδ hint γ hγ s₀ hs₀ hx
    refine ⟨ε, hε, ?_⟩
    rintro ⟨s, hs⟩ hds
    exact hloc s hs hds
  have huniv : U = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨0, left_mem_uIcc⟩, h0⟩
  intro s hs
  have : (⟨s, hs⟩ : uIcc (0 : ℝ) t) ∈ U := huniv ▸ mem_univ _
  exact this
