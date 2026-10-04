-- Prove2me | solution 1 for AnosovPlugs.isMIntegralCurveOn_uIcc_eq
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-03T09:01:17.968833+00:00
-- url     : https://prove2.me/submissions/28a61f7b-ed49-4233-b215-7e6d79801953

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

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

theorem solution
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
