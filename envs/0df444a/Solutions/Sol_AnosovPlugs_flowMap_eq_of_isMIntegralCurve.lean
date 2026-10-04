-- Prove2me | solution 1 for AnosovPlugs.flowMap_eq_of_isMIntegralCurve
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-03T01:20:00.48735+00:00
-- url     : https://prove2.me/submissions/18f9596f-0c32-4336-a287-9c04f8622b7b

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set
open AnosovPlugs

section FlowMapHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {v : (x : M) → TangentSpace I x}

/-- Change the base point in the derivative `smulRight (v p)` to `f s` when `f s = p`. -/
theorem flowMapAux_congr_pt {f : ℝ → M} {S : Set ℝ} {s : ℝ} {p : M}
    (h : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f S s ((1 : ℝ →L[ℝ] ℝ).smulRight (v p)))
    (hp : f s = p) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f S s ((1 : ℝ →L[ℝ] ℝ).smulRight (v (f s))) := by
  subst hp
  exact h

/-- Change the point `p` in the derivative `smulRight (v p)` to an equal point `q`. -/
theorem flowMapAux_congr_val {f : ℝ → M} {S : Set ℝ} {s : ℝ} {p q : M}
    (h : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f S s ((1 : ℝ →L[ℝ] ℝ).smulRight (v p)))
    (hp : p = q) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I f S s ((1 : ℝ →L[ℝ] ℝ).smulRight (v q)) := by
  subst hp
  exact h

/-- Gluing at the left endpoint: a global integral curve `γ` before `a`, and an integral
curve `γ'` on `[a, b]` with `γ' a = γ a`, give an integral curve on `(a - 1, b)`. -/
theorem flowMapAux_glue_left {γ γ' : ℝ → M} {a b : ℝ}
    (hγ : IsMIntegralCurve γ v) (hγ' : IsMIntegralCurveOn γ' v (Icc a b)) (hab : a < b)
    (h0 : γ' a = γ a) :
    IsMIntegralCurveOn (fun s => if s < a then γ s else γ' s) v (Ioo (a - 1) b) := by
  intro s hs
  rcases lt_trichotomy s a with hsa | rfl | hsa
  · have e : (fun s => if s < a then γ s else γ' s) =ᶠ[𝓝 s] γ := by
      filter_upwards [Iio_mem_nhds hsa] with u hu
      simp [show u < a from hu]
    refine flowMapAux_congr_pt ((hγ s).congr_of_eventuallyEq e).hasMFDerivWithinAt ?_
    simp [hsa]
  · have h1 : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u => if u < s then γ u else γ' u) (Iic s) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ s))) := by
      refine (hγ s).hasMFDerivWithinAt.congr_mono ?_ ?_ (subset_univ _)
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
      exact flowMapAux_congr_val k' h0
    have h3 := h1.union h2
    rw [Iic_union_Ici] at h3
    refine flowMapAux_congr_pt (h3.mono (subset_univ _)) ?_
    simp [h0]
  · have k := (hγ' s ⟨hsa.le, hs.2.le⟩).hasMFDerivAt (Icc_mem_nhds hsa hs.2)
    have e : (fun s => if s < a then γ s else γ' s) =ᶠ[𝓝 s] γ' := by
      filter_upwards [Ioi_mem_nhds hsa] with u hu
      simp [not_lt.mpr (le_of_lt (show a < u from hu))]
    refine flowMapAux_congr_pt (k.congr_of_eventuallyEq e).hasMFDerivWithinAt ?_
    simp [not_lt.mpr hsa.le]

/-- Gluing at the right endpoint. -/
theorem flowMapAux_glue_right {γ γ' : ℝ → M} {a b : ℝ}
    (hγ : IsMIntegralCurve γ v) (hγ' : IsMIntegralCurveOn γ' v (Icc a b)) (hab : a < b)
    (h0 : γ' b = γ b) :
    IsMIntegralCurveOn (fun s => if b < s then γ s else γ' s) v (Ioo a (b + 1)) := by
  intro s hs
  rcases lt_trichotomy s b with hsb | rfl | hsb
  · have k := (hγ' s ⟨hs.1.le, hsb.le⟩).hasMFDerivAt (Icc_mem_nhds hs.1 hsb)
    have e : (fun s => if b < s then γ s else γ' s) =ᶠ[𝓝 s] γ' := by
      filter_upwards [Iio_mem_nhds hsb] with u hu
      simp [not_lt.mpr (le_of_lt (show u < b from hu))]
    refine flowMapAux_congr_pt (k.congr_of_eventuallyEq e).hasMFDerivWithinAt ?_
    simp [not_lt.mpr hsb.le]
  · have h1 : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u => if s < u then γ u else γ' u) (Ici s) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ s))) := by
      refine (hγ s).hasMFDerivWithinAt.congr_mono ?_ ?_ (subset_univ _)
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
      exact flowMapAux_congr_val k' h0
    have h3 := h2.union h1
    rw [Iic_union_Ici] at h3
    refine flowMapAux_congr_pt (h3.mono (subset_univ _)) ?_
    simp [h0]
  · have e : (fun s => if b < s then γ s else γ' s) =ᶠ[𝓝 s] γ := by
      filter_upwards [Ioi_mem_nhds hsb] with u hu
      simp [show b < u from hu]
    refine flowMapAux_congr_pt ((hγ s).congr_of_eventuallyEq e).hasMFDerivWithinAt ?_
    simp [hsb]

variable [IsManifold I 1 M] [T2Space M]

/-- Uniqueness forward: agreement at the left endpoint gives agreement at the right one. -/
theorem flowMapAux_eq_right {γ γ' : ℝ → M} {a b : ℝ}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurve γ v) (hint : ∀ s : ℝ, I.IsInteriorPoint (γ s))
    (hγ' : IsMIntegralCurveOn γ' v (Icc a b)) (hab : a < b) (h0 : γ' a = γ a) :
    γ' b = γ b := by
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff (t₀ := a - 1 / 2)
    (by constructor <;> linarith) (fun s _ => hint s) hv (hγ.isMIntegralCurveOn _)
    (flowMapAux_glue_left hγ hγ' hab h0)
    (by show γ _ = (if _ < a then _ else _); rw [if_pos (by linarith)])
  have hIco : ∀ s ∈ Ico a b, γ' s = γ s := by
    intro s hs
    have := heq ⟨by linarith [hs.1], hs.2⟩
    simp only [not_lt.mpr hs.1, if_false] at this
    exact this.symm
  have c1 : ContinuousWithinAt γ' (Ico a b) b :=
    (hγ'.continuousWithinAt ⟨hab.le, le_rfl⟩).mono Ico_subset_Icc_self
  have c2 : ContinuousWithinAt γ (Ico a b) b := hγ.continuous.continuousWithinAt
  have : Filter.NeBot (𝓝[Ico a b] b) := by
    rw [nhdsWithin_Ico_eq_nhdsLT hab]; infer_instance
  have hev : γ' =ᶠ[𝓝[Ico a b] b] γ :=
    Filter.mem_of_superset self_mem_nhdsWithin (fun s hs => hIco s hs)
  exact tendsto_nhds_unique c1.tendsto (c2.tendsto.congr' hev.symm)

/-- Uniqueness backward: agreement at the right endpoint gives agreement at the left one. -/
theorem flowMapAux_eq_left {γ γ' : ℝ → M} {a b : ℝ}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurve γ v) (hint : ∀ s : ℝ, I.IsInteriorPoint (γ s))
    (hγ' : IsMIntegralCurveOn γ' v (Icc a b)) (hab : a < b) (h0 : γ' b = γ b) :
    γ' a = γ a := by
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff (t₀ := b + 1 / 2)
    (by constructor <;> linarith) (fun s _ => hint s) hv (hγ.isMIntegralCurveOn _)
    (flowMapAux_glue_right hγ hγ' hab h0)
    (by show γ _ = (if b < _ then _ else _); rw [if_pos (by linarith)])
  have hIoc : ∀ s ∈ Ioc a b, γ' s = γ s := by
    intro s hs
    have := heq ⟨hs.1, by linarith [hs.2]⟩
    simp only [not_lt.mpr hs.2, if_false] at this
    exact this.symm
  have c1 : ContinuousWithinAt γ' (Ioc a b) a :=
    (hγ'.continuousWithinAt ⟨le_rfl, hab.le⟩).mono Ioc_subset_Icc_self
  have c2 : ContinuousWithinAt γ (Ioc a b) a := hγ.continuous.continuousWithinAt
  have : Filter.NeBot (𝓝[Ioc a b] a) := by
    rw [nhdsWithin_Ioc_eq_nhdsGT hab]; infer_instance
  have hev : γ' =ᶠ[𝓝[Ioc a b] a] γ :=
    Filter.mem_of_superset self_mem_nhdsWithin (fun s hs => hIoc s hs)
  exact tendsto_nhds_unique c1.tendsto (c2.tendsto.congr' hev.symm)

end FlowMapHelpers

theorem solution
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    [T2Space M]
    (X : (x : M) → TangentSpace I3 x) (hX : IsC1VectorField X) (γ : ℝ → M)
    (hγ : IsMIntegralCurve γ X) (hint : ∀ s : ℝ, I3.IsInteriorPoint (γ s)) (t : ℝ) :
    flowMap X t (γ 0) = γ t := by
  have hdef : FlowDefined X (γ 0) t := ⟨γ, rfl, hγ.isMIntegralCurveOn _⟩
  rw [flowMap, dif_pos hdef]
  have hspec := hdef.choose_spec
  generalize hdef.choose = γ' at hspec ⊢
  obtain ⟨hγ'0, hγ'⟩ := hspec
  rcases lt_trichotomy 0 t with ht | ht | ht
  · rw [uIcc_of_le ht.le] at hγ'
    exact flowMapAux_eq_right hX hγ hint hγ' ht hγ'0
  · subst ht
    exact hγ'0
  · rw [uIcc_of_ge ht.le] at hγ'
    exact flowMapAux_eq_left hX hγ hint hγ' ht hγ'0
