-- Prove2me | solution 1 for AnosovPlugs.integralCurve_lift_of_embedding
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-02T22:57:55.588989+00:00
-- url     : https://prove2.me/submissions/72e45ede-6335-483a-acab-660f52362e31

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

open AnosovPlugs

lemma hasDerivWithinAt_of_comp_aux
    (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (D : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3))
    (a : EuclideanSpace ℝ (Fin 3)) (sF : Set (EuclideanSpace ℝ (Fin 3)))
    (hF : HasFDerivWithinAt F (D : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) sF a)
    (g : ℝ → EuclideanSpace ℝ (Fin 3)) (s : Set ℝ) (t : ℝ) (ht : t ∈ s) (hg0 : g t = a)
    (hg : Filter.Tendsto g (𝓝[s] t) (𝓝[sF] a))
    (h : ℝ → EuclideanSpace ℝ (Fin 3)) (v : EuclideanSpace ℝ (Fin 3))
    (hh : HasDerivWithinAt h (D v) s t)
    (heq : ∀ᶠ u in 𝓝[s] t, F (g u) = h u) :
    HasDerivWithinAt g v s t := by
  have hFa : F a = h t := by
    have := heq.self_of_nhdsWithin ht
    rwa [hg0] at this
  have he : (fun u => F (g u) - F a - D (g u - a)) =o[𝓝[s] t] (fun u => g u - a) :=
    hF.isLittleO.comp_tendsto hg
  have h1 : (fun u => g u - a) =O[𝓝[s] t] (fun u => D (g u - a)) := D.isBigO_comp_rev _ _
  have he2 : (fun u => F (g u) - F a - D (g u - a)) =o[𝓝[s] t] (fun u => D (g u - a)) :=
    he.trans_isBigO h1
  have h2 : (fun u => D (g u - a)) =O[𝓝[s] t] (fun u => h u - h t) := by
    refine he2.right_isBigO_add.congr' (Filter.EventuallyEq.refl _ _) ?_
    filter_upwards [heq] with u hu
    rw [sub_add_cancel, hu, hFa]
  have h3 : (fun u => h u - h t) =O[𝓝[s] t] (fun u => u - t) := hh.hasFDerivWithinAt.isBigO_sub
  have h4 : (fun u => g u - a) =O[𝓝[s] t] (fun u => u - t) := h1.trans (h2.trans h3)
  have hA : (fun u => h u - h t - (u - t) • D v) =o[𝓝[s] t] (fun u => u - t) := hh.isLittleO
  have hB : (fun u => F (g u) - F a - D (g u - a)) =o[𝓝[s] t] (fun u => u - t) :=
    he.trans_isBigO h4
  have hC : (fun u => D.symm ((h u - h t - (u - t) • D v) - (F (g u) - F a - D (g u - a))))
      =o[𝓝[s] t] (fun u => u - t) :=
    ((D.symm : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)).isBigO_comp _ _).trans_isLittleO
      (hA.sub hB)
  rw [hasDerivWithinAt_iff_isLittleO, hg0]
  refine hC.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [heq] with u hu
  have hlin : h u - h t - (u - t) • D v - (F (g u) - F a - D (g u - a))
      = D (g u - a - (u - t) • v) := by
    rw [hu, hFa]
    simp only [map_sub, map_smul]
    abel
  rw [hlin, ContinuousLinearEquiv.symm_apply_apply]

theorem solution
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (X : (x : M) → TangentSpace I3 x) (Z : (w : N) → TangentSpace I3 w) (i : M → N)
    (hi : ContMDiff I3 I3 1 i) (hemb : Topology.IsEmbedding i)
    (hinj : ∀ x, Function.Injective (mfderiv I3 I3 i x))
    (hZ : ∀ x, mfderiv I3 I3 i x (X x) = Z (i x))
    (γ : ℝ → N) (s : Set ℝ) (hγ : IsMIntegralCurveOn γ Z s) (hrange : ∀ t ∈ s, γ t ∈ range i)
    (hs : s.Nonempty) :
    ∃ δ : ℝ → M, (∀ t ∈ s, i (δ t) = γ t) ∧ IsMIntegralCurveOn δ X s := by
  obtain ⟨t₀, ht₀⟩ := hs
  have : Nonempty M := ⟨(hrange t₀ ht₀).choose⟩
  set δ : ℝ → M := fun t => Function.invFun i (γ t) with hδdef
  have hδ : ∀ t ∈ s, i (δ t) = γ t := fun t ht => Function.invFun_eq (hrange t ht)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hcont : ContinuousWithinAt δ s t := by
    rw [hemb.isInducing.continuousWithinAt_iff]
    exact (hγ t ht).1.congr (fun u hu => hδ u hu) (hδ t ht)
  set x := δ t with hx
  have hw : γ t = i x := (hδ t ht).symm
  set a := extChartAt I3 x x with ha
  let D : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) := mfderiv I3 I3 i x
  have hDinj : Function.Injective D := hinj x
  let Dₑ : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (LinearEquiv.ofInjectiveEndo
      (D : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) hDinj).toContinuousLinearEquiv
  have hDₑ : (Dₑ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) = D := by
    ext v
    simp [Dₑ, LinearEquiv.coe_ofInjectiveEndo]
  have hF : HasFDerivWithinAt (writtenInExtChartAt I3 I3 x i)
      (Dₑ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) (range I3) a := by
    rw [hDₑ]
    exact ((hi x).mdifferentiableAt one_ne_zero).hasMFDerivAt.2
  let g : ℝ → EuclideanSpace ℝ (Fin 3) := extChartAt I3 x ∘ δ
  have hg0 : g t = a := rfl
  have hgcont : ContinuousWithinAt g s t :=
    ContinuousAt.comp_continuousWithinAt (g := extChartAt I3 x) (f := δ)
      (continuousAt_extChartAt x) hcont
  have hgT : Filter.Tendsto g (𝓝[s] t) (𝓝[range I3] a) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hgcont, Filter.Eventually.of_forall fun u => ?_⟩
    show extChartAt I3 x (δ u) ∈ range I3
    rw [extChartAt_coe]
    exact mem_range_self _
  let h : ℝ → EuclideanSpace ℝ (Fin 3) := extChartAt I3 (γ t) ∘ γ
  have hh : HasDerivWithinAt h (Z (γ t)) s t := by
    have := hγ.hasDerivWithinAt (t₀ := t) ht (mem_extChartAt_source (γ t))
    have e := tangentCoordChange_self (I := I3) (x := γ t) (z := γ t) (v := Z (γ t))
      (mem_extChartAt_source (γ t))
    rw [e] at this
    exact this
  have hv : (Dₑ (X x) : EuclideanSpace ℝ (Fin 3)) = Z (γ t) := by
    have h1 : (Dₑ (X x) : EuclideanSpace ℝ (Fin 3)) = D (X x) := by
      rw [← hDₑ]
      rfl
    have h2 : (Z (γ t) : EuclideanSpace ℝ (Fin 3)) = Z (i x) := by rw [hw]
    rw [h1, h2]
    exact hZ x
  have hh' : HasDerivWithinAt h (Dₑ (X x)) s t := by
    rw [hv]
    exact hh
  have heq : ∀ᶠ u in 𝓝[s] t, writtenInExtChartAt I3 I3 x i (g u) = h u := by
    filter_upwards [self_mem_nhdsWithin, hcont (extChartAt_source_mem_nhds (I := I3) x)]
      with u hu hsrc
    simp only [writtenInExtChartAt, Function.comp_apply, g, h]
    rw [PartialEquiv.left_inv _ hsrc, hδ u hu, hw]
  have hd : HasDerivWithinAt g (X x) s t :=
    hasDerivWithinAt_of_comp_aux _ Dₑ a (range I3) hF g s t ht hg0 hgT h (X x) hh' heq
  refine ⟨hcont, ?_⟩
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    PartialEquiv.refl_symm, modelWithCornersSelf_coe, range_id, preimage_id, inter_univ,
    Function.comp_id, id_eq]
  exact hd
