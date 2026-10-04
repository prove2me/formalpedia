-- Prove2me | solution 1 for AnosovPlugs.hyperbolicSet_image_of_conjugacy
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-03T01:20:00.749476+00:00
-- url     : https://prove2.me/submissions/01cb3096-5898-41fb-b2dc-461f6dfa1976

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set
open AnosovPlugs

/-- An injective derivative between 3-manifolds sends an interior point to an interior point. -/
theorem interiorPoint_image_of_mfderiv_injective
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (f : M → N) (x : M) (hf : ContMDiffAt I3 I3 1 f x)
    (hinj : Function.Injective (mfderiv I3 I3 f x)) (hx : x ∈ I3.interior M) :
    f x ∈ I3.interior N := by
  have hsurj : Function.Surjective (mfderiv I3 I3 f x) := by
    let L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
      (mfderiv I3 I3 f x).toLinearMap
    exact LinearMap.surjective_of_injective (f := L) (fun a b hab => hinj hab)
  exact (hf.mdifferentiableAt one_ne_zero).isInteriorPoint_of_surjective_mfderiv hsurj hx

/-- The inverse of an embedding with injective derivative at an interior point, whose range is a
neighbourhood of the image point, is differentiable there. -/
theorem mdifferentiableAt_invFun_of_embedding
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    [Nonempty M]
    (i : M → N) (hi : ContMDiff I3 I3 1 i) (hemb : Topology.IsEmbedding i) (x : M)
    (hx : I3.IsInteriorPoint x) (hinj : Function.Injective (mfderiv I3 I3 i x))
    (hnhds : range i ∈ 𝓝 (i x)) :
    MDifferentiableAt I3 I3 (Function.invFun i) (i x) := by
  set j := Function.invFun i with hjdef
  have hleft : Function.LeftInverse j i := Function.leftInverse_invFun hemb.injective
  have hjx : j (i x) = x := hleft x
  have hjcont : ContinuousAt j (i x) := by
    rw [← hemb.isInducing.continuousAt_iff' hnhds]
    have : j ∘ i = id := funext hleft
    rw [this]
    exact continuousAt_id
  have hix : I3.IsInteriorPoint (i x) :=
    interiorPoint_image_of_mfderiv_injective i x (hi x) hinj hx
  set a := extChartAt I3 x x with ha
  set b0 := extChartAt I3 (i x) (i x) with hb0
  let D : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) := mfderiv I3 I3 i x
  have hDinj : Function.Injective D := hinj
  let Dₑ : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (LinearEquiv.ofInjectiveEndo
      (D : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) hDinj).toContinuousLinearEquiv
  have hDₑ : (Dₑ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) = D := by
    ext v
    simp [Dₑ, LinearEquiv.coe_ofInjectiveEndo]
  have hFw : HasFDerivWithinAt (writtenInExtChartAt I3 I3 x i)
      (Dₑ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) (range I3) a := by
    rw [hDₑ]
    exact ((hi x).mdifferentiableAt one_ne_zero).hasMFDerivAt.2
  have hrange : range I3 ∈ 𝓝 a := range_mem_nhds_isInteriorPoint hx
  have hF : HasFDerivAt (writtenInExtChartAt I3 I3 x i)
      (Dₑ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) a :=
    hFw.hasFDerivAt hrange
  set G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    extChartAt I3 x ∘ j ∘ (extChartAt I3 (i x)).symm with hG
  have hGb0 : G b0 = a := by
    simp only [hG, Function.comp_apply, hb0, extChartAt_to_inv, hjx, ha]
  have hc1 : ContinuousAt (extChartAt I3 (i x)).symm b0 := continuousAt_extChartAt_symm (i x)
  have hc2 : ContinuousAt j ((extChartAt I3 (i x)).symm b0) := by
    rw [hb0, extChartAt_to_inv]
    exact hjcont
  have hc12 : ContinuousAt (j ∘ (extChartAt I3 (i x)).symm) b0 := hc2.comp hc1
  have hGcont : ContinuousAt G b0 := by
    have h3 : ContinuousAt (extChartAt I3 x) ((j ∘ (extChartAt I3 (i x)).symm) b0) := by
      rw [Function.comp_apply, hb0, extChartAt_to_inv, hjx]
      exact continuousAt_extChartAt x
    exact h3.comp hc12
  have hFG : ∀ᶠ b in 𝓝 b0, writtenInExtChartAt I3 I3 x i (G b) = b := by
    have ht : (extChartAt I3 (i x)).target ∈ 𝓝 b0 :=
      mem_interior_iff_mem_nhds.1 ((ModelWithCorners.isInteriorPoint_iff (I := I3)).1 hix)
    have h1 : ∀ᶠ b in 𝓝 b0, (extChartAt I3 (i x)).symm b ∈ range i := by
      apply hc1.preimage_mem_nhds
      rw [hb0, extChartAt_to_inv]
      exact hnhds
    have h2 : ∀ᶠ b in 𝓝 b0, j ((extChartAt I3 (i x)).symm b) ∈ (extChartAt I3 x).source := by
      apply hc12.preimage_mem_nhds
      show (extChartAt I3 x).source ∈ 𝓝 (j ((extChartAt I3 (i x)).symm b0))
      rw [hb0, extChartAt_to_inv, hjx]
      exact extChartAt_source_mem_nhds x
    filter_upwards [ht, h1, h2] with b hbt hb1 hb2
    obtain ⟨y, hy⟩ := hb1
    simp only [writtenInExtChartAt, hG, Function.comp_apply]
    rw [PartialEquiv.left_inv _ hb2, ← hy, hleft y, hy, PartialEquiv.right_inv _ hbt]
  have hGd : HasFDerivAt G
      (Dₑ.symm : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) b0 := by
    refine HasFDerivAt.of_local_left_inverse hGcont ?_ hFG
    rw [hGb0]
    exact hF
  rw [mdifferentiableAt_iff]
  refine ⟨hjcont, ?_⟩
  have hW : writtenInExtChartAt I3 I3 (i x) j = G := by
    show extChartAt I3 (j (i x)) ∘ j ∘ (extChartAt I3 (i x)).symm = G
    rw [hjx]
  rw [hW]
  exact hGd.differentiableAt.differentiableWithinAt

theorem mdifferentiableAt_of_comp_embedding_aux
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    {P : Type} [TopologicalSpace P] [ChartedSpace (EuclideanHalfSpace 3) P] [IsManifold I3 ∞ P]
    (i : M → N) (hi : ContMDiff I3 I3 1 i) (hemb : Topology.IsEmbedding i) (x : M)
    (hx : I3.IsInteriorPoint x) (hinj : Function.Injective (mfderiv I3 I3 i x))
    (hnhds : range i ∈ 𝓝 (i x)) (f : N → P) (hf : MDifferentiableAt I3 I3 (f ∘ i) x) :
    MDifferentiableAt I3 I3 f (i x) := by
  have : Nonempty M := ⟨x⟩
  have hj := mdifferentiableAt_invFun_of_embedding i hi hemb x hx hinj hnhds
  have hleft : Function.LeftInverse (Function.invFun i) i :=
    Function.leftInverse_invFun hemb.injective
  have hf' : MDifferentiableAt I3 I3 (f ∘ i) (Function.invFun i (i x)) := by
    rw [hleft x]
    exact hf
  have hcomp : MDifferentiableAt I3 I3 ((f ∘ i) ∘ Function.invFun i) (i x) := hf'.comp (i x) hj
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hnhds] with w hw
  obtain ⟨y, rfl⟩ := hw
  simp only [Function.comp_apply, hleft y]

namespace HypImageConj

local notation "E3" => EuclideanSpace ℝ (Fin 3)

lemma finrank_map_inj (L : E3 →L[ℝ] E3) (hL : Function.Injective L) (S : Submodule ℝ E3) :
    Module.finrank ℝ (S.map (L : E3 →ₗ[ℝ] E3)) = Module.finrank ℝ S :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (L : E3 →ₗ[ℝ] E3) hL S)).symm

lemma sup_map_inj (L : E3 →L[ℝ] E3) (hL : Function.Injective L) (S T : Submodule ℝ E3)
    (v : E3) (h : S ⊔ Submodule.span ℝ {v} ⊔ T = ⊤) :
    S.map (L : E3 →ₗ[ℝ] E3) ⊔ Submodule.span ℝ {L v} ⊔ T.map (L : E3 →ₗ[ℝ] E3) = ⊤ := by
  have hsurj : Function.Surjective (L : E3 →ₗ[ℝ] E3) :=
    LinearMap.surjective_of_injective (f := (L : E3 →ₗ[ℝ] E3)) hL
  have hspan : Submodule.span ℝ {L v} = (Submodule.span ℝ {v}).map (L : E3 →ₗ[ℝ] E3) := by
    rw [Submodule.map_span, Set.image_singleton, ContinuousLinearMap.coe_coe]
  rw [hspan, ← Submodule.map_sup, ← Submodule.map_sup, h, Submodule.map_top,
    LinearMap.range_eq_top.2 hsurj]

lemma map_map_of_comm (A B L L' : E3 →L[ℝ] E3) (h : ∀ u, B (L u) = L' (A u))
    (S : Submodule ℝ E3) :
    (S.map (L : E3 →ₗ[ℝ] E3)).map (B : E3 →ₗ[ℝ] E3) =
      (S.map (A : E3 →ₗ[ℝ] E3)).map (L' : E3 →ₗ[ℝ] E3) := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext u
  simp [h u]

lemma real_est {A B n m c₁ c₂ C e : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hC : 0 < C) (he : 0 < e)
    (h1 : A ≤ c₂ * B) (h2 : B ≤ C * e * n) (h3 : c₁ * n ≤ m) :
    A ≤ C * c₂ / c₁ * e * m := by
  have k1 : c₂ * B ≤ c₂ * (C * e * n) := mul_le_mul_of_nonneg_left h2 hc₂.le
  have k2 : C * c₂ * e * (c₁ * n) ≤ C * c₂ * e * m :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have : C * c₂ / c₁ * e * m = (C * c₂ * e * m) / c₁ := by ring
  rw [this, le_div_iff₀ hc₁]
  nlinarith

end HypImageConj

open HypImageConj

lemma mdiff_flow_of_inv
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    (F : M → M) (S : (x : M) → Submodule ℝ (TangentSpace I3 x)) (x : M)
    (hinv : (S x).map (mfderiv I3 I3 F x).toLinearMap = S (F x))
    (hrank : Module.finrank ℝ (S (F x)) = 1) : MDifferentiableAt I3 I3 F x := by
  by_contra hnd
  rw [mfderiv_zero_of_not_mdifferentiableAt hnd, ContinuousLinearMap.toLinearMap_zero,
    Submodule.map_zero] at hinv
  rw [← hinv, finrank_bot] at hrank
  exact zero_ne_one hrank

lemma conj_deriv
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (X : (x : M) → TangentSpace I3 x) (Z : (w : N) → TangentSpace I3 w) (i : M → N)
    (hi : ContMDiff I3 I3 1 i) (hemb : Topology.IsEmbedding i) (x : M)
    (hx : I3.IsInteriorPoint x) (hinj : Function.Injective (mfderiv I3 I3 i x))
    (hnhds : range i ∈ 𝓝 (i x)) (t : ℝ)
    (hconj : ∀ᶠ y in 𝓝 x, flowMap Z t (i y) = i (flowMap X t y))
    (hdX : MDifferentiableAt I3 I3 (flowMap X t) x) :
    flowMap Z t (i x) = i (flowMap X t x) ∧
      ∀ u : TangentSpace I3 x,
        (mfderiv I3 I3 (flowMap Z t) (i x) (mfderiv I3 I3 i x u) : EuclideanSpace ℝ (Fin 3)) =
          mfderiv I3 I3 i (flowMap X t x) (mfderiv I3 I3 (flowMap X t) x u) := by
  have hEq : (flowMap Z t ∘ i) =ᶠ[𝓝 x] (i ∘ flowMap X t) := hconj
  have hself : flowMap Z t (i x) = i (flowMap X t x) := hconj.self_of_nhds
  have hdi' : MDifferentiableAt I3 I3 i (flowMap X t x) :=
    (hi (flowMap X t x)).mdifferentiableAt one_ne_zero
  have hR : MDifferentiableAt I3 I3 (i ∘ flowMap X t) x := hdi'.comp x hdX
  have hL : MDifferentiableAt I3 I3 (flowMap Z t ∘ i) x := hR.congr_of_eventuallyEq hEq
  have hdZ : MDifferentiableAt I3 I3 (flowMap Z t) (i x) :=
    mdifferentiableAt_of_comp_embedding_aux i hi hemb x hx hinj hnhds _ hL
  have hdi : MDifferentiableAt I3 I3 i x := (hi x).mdifferentiableAt one_ne_zero
  refine ⟨hself, fun u => ?_⟩
  have h1 := mfderiv_comp x hdZ hdi
  have h2 := mfderiv_comp x hdi' hdX
  have h3 : mfderiv I3 I3 (flowMap Z t ∘ i) x = mfderiv I3 I3 (i ∘ flowMap X t) x :=
    hEq.mfderiv_eq
  rw [h1, h2] at h3
  have := DFunLike.congr_fun h3 u
  exact this

theorem solution
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (X : (x : M) → TangentSpace I3 x) (Z : (w : N) → TangentSpace I3 w) (i : M → N)
    (Λ : Set M) (hΛ : IsHyperbolicSet X Λ)
    (hi : ContMDiff I3 I3 1 i) (hemb : Topology.IsEmbedding i)
    (hinj : ∀ x, Function.Injective (mfderiv I3 I3 i x))
    (hZ : ∀ x, mfderiv I3 I3 i x (X x) = Z (i x))
    (hΛinv : ∀ x ∈ Λ, ∀ t : ℝ, flowMap X t x ∈ Λ)
    (hint : ∀ x ∈ Λ, I3.IsInteriorPoint x)
    (hnhds : ∀ x ∈ Λ, range i ∈ 𝓝 (i x))
    (hconj : ∀ x ∈ Λ, ∀ t : ℝ, ∀ᶠ y in 𝓝 x, flowMap Z t (i y) = i (flowMap X t y))
    (hmetric : ∀ g : RiemannianMetric3 M, ∃ g' : RiemannianMetric3 N, ∃ c₁ c₂ : ℝ,
      0 < c₁ ∧ 0 < c₂ ∧ ∀ (x : M) (v : TangentSpace I3 x),
        c₁ * g.norm x v ≤ g'.norm (i x) (mfderiv I3 I3 i x v) ∧
        g'.norm (i x) (mfderiv I3 I3 i x v) ≤ c₂ * g.norm x v) :
    IsHyperbolicSet Z (i '' Λ) := by
  obtain ⟨g, Es, Eu, C, lam, hC, hlam, h⟩ := hΛ
  obtain ⟨g', c₁, c₂, hc₁, hc₂, hcmp⟩ := hmetric g
  rcases Λ.eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
  · subst hempty
    exact ⟨g', fun _ => ⊥, fun _ => ⊥, 1, 1, one_pos, one_pos, fun w hw => by simp at hw⟩
  have : Nonempty M := ⟨x₀⟩
  have hj : ∀ x, Function.invFun i (i x) = x := Function.leftInverse_invFun hemb.injective
  let EsE : N → Submodule ℝ (EuclideanSpace ℝ (Fin 3)) := fun w =>
    (Es (Function.invFun i w)).map (mfderiv I3 I3 i (Function.invFun i w)).toLinearMap
  let EuE : N → Submodule ℝ (EuclideanSpace ℝ (Fin 3)) := fun w =>
    (Eu (Function.invFun i w)).map (mfderiv I3 I3 i (Function.invFun i w)).toLinearMap
  have hEsE : ∀ y, EsE (i y) = (Es y).map (mfderiv I3 I3 i y).toLinearMap := by
    intro y
    show (Es (Function.invFun i (i y))).map (mfderiv I3 I3 i (Function.invFun i (i y))).toLinearMap = _
    rw [hj]
  have hEuE : ∀ y, EuE (i y) = (Eu y).map (mfderiv I3 I3 i y).toLinearMap := by
    intro y
    show (Eu (Function.invFun i (i y))).map (mfderiv I3 I3 i (Function.invFun i (i y))).toLinearMap = _
    rw [hj]
  have hnorm : ∀ (p q : N), p = q → ∀ v : TangentSpace I3 p, g'.norm p v = g'.norm q v := by
    rintro p q rfl v; rfl
  refine ⟨g', EsE, EuE, C * c₂ / c₁, lam, by positivity, hlam, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨hrs, hru, hsup, hinvs, hinvu, hests, hestu⟩ := h x hx
  have hdX : ∀ s : ℝ, MDifferentiableAt I3 I3 (flowMap X s) x := fun s =>
    mdiff_flow_of_inv (flowMap X s) Es x (hinvs s) (h _ (hΛinv x hx s)).1
  have hcd : ∀ s : ℝ, _ := fun s =>
    conj_deriv X Z i hi hemb x (hint x hx) (hinj x) (hnhds x hx) s (hconj x hx s) (hdX s)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hEsE x]
    exact (finrank_map_inj (mfderiv I3 I3 i x) (hinj x) (Es x)).trans hrs
  · rw [hEuE x]
    exact (finrank_map_inj (mfderiv I3 I3 i x) (hinj x) (Eu x)).trans hru
  · rw [hEsE x, hEuE x, ← hZ x]
    exact sup_map_inj (mfderiv I3 I3 i x) (hinj x) (Es x) (Eu x) (X x) hsup
  · intro t
    obtain ⟨hself, hpt⟩ := hcd t
    have e1 : EsE (flowMap Z t (i x)) = EsE (i (flowMap X t x)) := by rw [hself]
    rw [e1, hEsE x, hEsE (flowMap X t x), ← hinvs t]
    exact map_map_of_comm (mfderiv I3 I3 (flowMap X t) x) (mfderiv I3 I3 (flowMap Z t) (i x))
      (mfderiv I3 I3 i x) (mfderiv I3 I3 i (flowMap X t x)) hpt (Es x)
  · intro t
    obtain ⟨hself, hpt⟩ := hcd t
    have e1 : EuE (flowMap Z t (i x)) = EuE (i (flowMap X t x)) := by rw [hself]
    rw [e1, hEuE x, hEuE (flowMap X t x), ← hinvu t]
    exact map_map_of_comm (mfderiv I3 I3 (flowMap X t) x) (mfderiv I3 I3 (flowMap Z t) (i x))
      (mfderiv I3 I3 i x) (mfderiv I3 I3 i (flowMap X t x)) hpt (Eu x)
  · intro t ht v hv
    obtain ⟨hself, hpt⟩ := hcd t
    rw [hEsE x] at hv
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hv
    have k : g'.norm (flowMap Z t (i x)) (mfderiv I3 I3 (flowMap Z t) (i x) (mfderiv I3 I3 i x u))
        = g'.norm (i (flowMap X t x))
            (mfderiv I3 I3 i (flowMap X t x) (mfderiv I3 I3 (flowMap X t) x u)) := by
      rw [hpt u]
      exact hnorm _ _ hself _
    simp only [ContinuousLinearMap.coe_coe]
    rw [k]
    exact real_est hc₁ hc₂ hC (Real.exp_pos _) (hcmp _ _).2 (hests t ht u hu) (hcmp x u).1
  · intro t ht v hv
    obtain ⟨hself, hpt⟩ := hcd (-t)
    rw [hEuE x] at hv
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hv
    have k : g'.norm (flowMap Z (-t) (i x))
        (mfderiv I3 I3 (flowMap Z (-t)) (i x) (mfderiv I3 I3 i x u))
        = g'.norm (i (flowMap X (-t) x))
            (mfderiv I3 I3 i (flowMap X (-t) x) (mfderiv I3 I3 (flowMap X (-t)) x u)) := by
      rw [hpt u]
      exact hnorm _ _ hself _
    simp only [ContinuousLinearMap.coe_coe]
    rw [k]
    exact real_est hc₁ hc₂ hC (Real.exp_pos _) (hcmp _ _).2 (hestu t ht u hu) (hcmp x u).1
