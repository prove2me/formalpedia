-- Prove2me | Definitions.Def_OAIQ115N005
-- name    : OAIQ115N005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T00:27:19.507085+00:00
-- url     : https://prove2.me/theorems/93501efe-2985-4a27-b36a-26a24fd1589e
-- title:
--   Definitions bundle OAIQ115N005 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 73 declarations of OpenAI's Lean: 9 definitions, 3 instances and 61 theorems. The definitions and types are `OAI.NaimarkZFC.cyclicGNSEquiv`, `OAI.NaimarkZFC.cyclicGNSIsometry`, `OAI.NaimarkZFC.cyclicGNSMap`, `OAI.NaimarkZFC.diagonalHom`, `OAI.NaimarkZFC.diagonalRepresentation`, `OAI.NaimarkZFC.peakingCoefficientsPositive`, `OAI.NaimarkZFC.pureExcisionNet`, `OAI.NaimarkZFC.selfAdjointSubspaceInclusion`, `OAI.NaimarkZFC.vectorNullAlgebra`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_Amalgamation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Amalgamation.lean), [`Naimark_Basic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Basic.lean), [`Naimark_HNN`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/HNN.lean), [`Naimark_Omission`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Omission.lean), [`Naimark_Representations`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Representations.lean), [`Naimark_States`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/States.lean).
--
--   **Imports.** It imports the published bundle `Def_Naimark`; the bundles `OAIQ115N000`, `OAIQ115N001` and `OAIQ115N002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N007`, `OAIQ115N008` and `OAIQ115N009`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark
import Definitions.Def_OAIQ115N000
import Definitions.Def_OAIQ115N001
import Definitions.Def_OAIQ115N002

section
-- module Solutions.OAIQ115_Naimark.Naimark_Basic
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.centeredColumnComplete _root_.OAI.NaimarkZFC.centeredRowComplete _root_.OAI.NaimarkZFC.projectionRowComplete _root_.OAI.NaimarkZFC.traceColumnComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u v w
namespace NaimarkZFC


section GNS

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem state_map_star (f : A →L[ℂ] ℂ) (hf : IsState f) (a : A) :
    f (star a) = star (f a) := map_star (positiveOfSquares f hf.2) a

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_vector_cyclic (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hπ : IsIrreducible π) (x : H) (hx : x ≠ 0) : DenseRange (fun a : A => π a x) := by
  let M := (orbitMap π x).range
  have hm (a : A) : M.map (π a).toLinearMap ≤ M := by
    rintro _ ⟨y, ⟨b, rfl⟩, rfl⟩
    refine ⟨a * b, ?_⟩
    simp [orbitMap, map_mul, mul_apply_eq_comp]
  have hinv (a : A) (y : H) (hy : y ∈ M.topologicalClosure) :
      π a y ∈ M.topologicalClosure := by
    apply Submodule.topologicalClosure_mono (hm a)
    apply Submodule.topologicalClosure_map (π a) M
    exact ⟨y, hy, rfl⟩
  have hxM : x ∈ M := by
    refine ⟨1, ?_⟩
    simp [orbitMap, irreducible_map_one π hπ]
  have hxcl : x ∈ M.topologicalClosure := M.le_topologicalClosure hxM
  have htop : M.topologicalClosure = ⊤ := by
    rcases hπ.2 M.topologicalClosure M.isClosed_topologicalClosure hinv with h | h
    · exact (hx (by simpa [h] using hxcl)).elim
    · exact h
  exact (Submodule.dense_iff_topologicalClosure_eq_top.mpr htop : Dense (M : Set H))

@[simp] theorem vectorFunctional_square (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) (a : A) :
    vectorFunctional π x (star a * a) = (‖π a x‖ : ℂ) ^ 2 := by
  rw [vectorFunctional_apply, map_mul, map_star]
  change ⟪x, (ContinuousLinearMap.adjoint (π a)) ((π a) x)⟫_ℂ = _
  simp [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]

@[simp] theorem vectorFunctional_one (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1) (x : H) :
    vectorFunctional π x 1 = (‖x‖ : ℂ) ^ 2 := by
  simp [hone, inner_self_eq_norm_sq_to_K]

theorem vectorFunctional_add_reducing (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (M : Submodule ℂ H) (hM : ∀ a : A, ∀ x ∈ M, π a x ∈ M)
    (x y : H) (hx : x ∈ M) (hy : y ∈ Mᗮ) :
    vectorFunctional π (x + y) = vectorFunctional π x + vectorFunctional π y := by
  ext a
  simp only [vectorFunctional_apply, map_add, inner_add_left, inner_add_right, add_apply]
  have hxy : ⟪x, π a y⟫_ℂ = 0 := invariant_orthogonal π M hM a y hy x hx
  have hyx : ⟪y, π a x⟫_ℂ = 0 := by
    rw [← inner_conj_symm]
    simp only [hy _ (hM a x hx), map_zero]
  rw [hxy, hyx]
  simp only [add_zero, zero_add]

variable [PartialOrder A] [StarOrderedRing A]

theorem normalized_vector_isState (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1)
    (x : H) (hx : x ≠ 0) :
    IsState ((‖x‖ ^ 2)⁻¹ • vectorFunctional π x) := by
  apply (isState_iff _).mpr
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  constructor
  · rw [smul_apply, vectorFunctional_one π hone, ← Complex.ofReal_pow]
    change (((‖x‖ ^ 2)⁻¹ : ℝ) : ℂ) * ((‖x‖ ^ 2 : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero 2 hn), Complex.ofReal_one]
  · intro a
    rw [smul_apply, vectorFunctional_square]
    simp only [Complex.smul_im, Complex.smul_re, ← Complex.ofReal_pow,
      Complex.ofReal_im, Complex.ofReal_re, smul_eq_mul, mul_zero, true_and]
    positivity

theorem pure_cyclic_irreducible (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1)
    (ξ : H) (hξ : ‖ξ‖ = 1) (hcyc : DenseRange (fun a : A => π a ξ))
    (hpure : IsPureState (vectorFunctional π ξ)) : IsIrreducible π := by
  refine ⟨?_, ?_⟩
  · intro hz
    have h : ξ = 0 := by
      calc
        ξ = π 1 ξ := by rw [hone]; rfl
        _ = 0 := by rw [hz]; rfl
    simp [h] at hξ
  · intro M hclosed hinv
    let : IsClosed (M : Set H) := hclosed
    let u := M.starProjection ξ
    let v := ξ - u
    have huM : u ∈ M := M.starProjection_apply_mem ξ
    have hvM : v ∈ Mᗮ := M.sub_starProjection_mem_orthogonal ξ
    by_cases hu : u = 0
    · left
      apply M.orthogonal_eq_top_iff.mp
      apply cyclic_closed_invariant_top π ξ hcyc Mᗮ M.isClosed_orthogonal
        (invariant_orthogonal π M hinv)
      simpa only [v, hu, sub_zero] using hvM
    by_cases hv : v = 0
    · right
      apply cyclic_closed_invariant_top π ξ hcyc M hclosed hinv
      have h : ξ = u := sub_eq_zero.mp hv
      rwa [h]
    have ha : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
    have hb : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
    have hab : ‖u‖ ^ 2 + ‖v‖ ^ 2 = 1 := by
      have h := Submodule.norm_sq_eq_add_norm_sq_starProjection ξ M
      rw [hξ, one_pow, Submodule.starProjection_orthogonal_val] at h
      exact h.symm
    have huv : u + v = ξ := by dsimp [v]; abel
    have hseg : vectorFunctional π ξ ∈ openSegment ℝ
        ((‖u‖ ^ 2)⁻¹ • vectorFunctional π u)
        ((‖v‖ ^ 2)⁻¹ • vectorFunctional π v) := by
      refine ⟨‖u‖ ^ 2, ‖v‖ ^ 2, ha, hb, hab, ?_⟩
      rw [smul_smul, smul_smul, mul_inv_cancel₀ (ne_of_gt ha),
        mul_inv_cancel₀ (ne_of_gt hb), one_smul, one_smul]
      rw [← vectorFunctional_add_reducing π M hinv u v huM hvM, huv]
    have huf : (‖u‖ ^ 2)⁻¹ • vectorFunctional π u = vectorFunctional π ξ :=
      (((mem_extremePoints.mp hpure).2 _ (normalized_vector_isState π hone u hu)
        _ (normalized_vector_isState π hone v hv) hseg).1)
    have hgu : vectorFunctional π u = ‖u‖ ^ 2 • vectorFunctional π ξ := by
      rw [← huf, smul_smul, mul_inv_cancel₀ (ne_of_gt ha), one_smul]
    have hPu : M.starProjection u = u := Submodule.starProjection_eq_self_iff.mpr huM
    have coeff (a : A) : ⟪u, π a ξ⟫_ℂ = ⟪(‖u‖ ^ 2) • ξ, π a ξ⟫_ℂ := by
      calc
        ⟪u, π a ξ⟫_ℂ = ⟪u, M.starProjection (π a ξ)⟫_ℂ := by
          rw [← M.inner_starProjection_left_eq_right, hPu]
        _ = vectorFunctional π u a := by
          rw [invariant_starProjection_commute π M hinv]
          rfl
        _ = (‖u‖ ^ 2) • ⟪ξ, π a ξ⟫_ℂ := by rw [hgu]; rfl
        _ = ⟪(‖u‖ ^ 2) • ξ, π a ξ⟫_ℂ := (inner_smul_left_eq_smul _ _ _).symm
    have hscalar : u = (‖u‖ ^ 2) • ξ := by
      apply ext_inner_right ℂ
      have h := hcyc.equalizer
        (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
        (funext coeff)
      exact congrFun h
    have hscale : (‖u‖ ^ 2 : ℝ) • u = u := by
      calc
        (‖u‖ ^ 2 : ℝ) • u = M.starProjection ((‖u‖ ^ 2 : ℝ) • ξ) := by
          exact ((M.starProjection.restrictScalars ℝ).map_smul (‖u‖ ^ 2) ξ).symm
        _ = M.starProjection u := by rw [← hscalar]
        _ = u := hPu
    have hnorm := congrArg norm hscale
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha] at hnorm
    have hn := norm_pos_iff.mpr hu
    exfalso
    have h1 : ‖u‖ ^ 2 = 1 := by nlinarith
    linarith

theorem pure_gns_irreducible (f : A →L[ℂ] ℂ) (hf : IsState f) (hfp : IsPureState f) :
    IsIrreducible (positiveOfSquares f hf.2).gnsNonUnitalStarAlgHom := by
  let g := positiveOfSquares f hf.2
  have hone : g 1 = 1 := ((isState_iff f).mp hf).1
  have hcoeff : vectorFunctional g.gnsNonUnitalStarAlgHom (gnsVector g) = f := by
    ext a
    exact gnsVector_coefficient g a
  apply pure_cyclic_irreducible g.gnsNonUnitalStarAlgHom
    (show g.gnsStarAlgHom 1 = 1 from map_one _) (gnsVector g)
    (gnsVector_norm_eq_one g hone) (gnsVector_cyclic g)
  rwa [hcoeff]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_commutant_selfAdjoint_scalar
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (hcomm : ∀ a : A, Commute T (π a)) :
    ∃ r : ℝ, T = r • (1 : H →L[ℂ] H) := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · exact ⟨0, Subsingleton.elim _ _⟩
  let : Nontrivial H := hH
  obtain ⟨r, hr⟩ := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) T hT
  refine ⟨r, ?_⟩
  have unique (x y : ℝ) (hx : x ∈ spectrum ℝ T) (hy : y ∈ spectrum ℝ T) : ¬ x < y := by
    intro hxy
    let c := (x + y) / 2
    let f : ℝ → ℝ := fun t => max (t - c) 0
    let g : ℝ → ℝ := fun t => max (c - t) 0
    have hf : Continuous f := (continuous_id.sub continuous_const).max continuous_const
    have hg : Continuous g := (continuous_const.sub continuous_id).max continuous_const
    have hfg (t : ℝ) : f t * g t = 0 := by
      dsimp [f, g]
      by_cases h : t ≤ c
      · rw [max_eq_right (sub_nonpos.mpr h), zero_mul]
      · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h)), mul_zero]
    have hzero : cfc f T * cfc g T = 0 := by
      rw [← cfc_mul f g T hf.continuousOn hg.continuousOn]
      rw [cfc_congr (g := fun _ : ℝ => 0) (fun t _ => hfg t), cfc_const_zero]
    rcases commutant_mul_eq_zero π hπ (cfc f T) (cfc g T)
      (fun a => hT.commute_cfc (hcomm a) g) hzero with hz | hz
    · have heq : cfc f T = cfc (fun _ : ℝ => 0) T := by
        simpa only [cfc_const_zero] using hz
      have hval := eqOn_of_cfc_eq_cfc heq hf.continuousOn continuousOn_const hT hy
      dsimp [f, c] at hval
      have hpos : 0 < y - (x + y) / 2 := by linarith
      rw [max_eq_left (le_of_lt hpos)] at hval
      linarith
    · have heq : cfc g T = cfc (fun _ : ℝ => 0) T := by
        simpa only [cfc_const_zero] using hz
      have hval := eqOn_of_cfc_eq_cfc heq hg.continuousOn continuousOn_const hT hx
      dsimp [g, c] at hval
      have hpos : 0 < (x + y) / 2 - x := by linarith
      rw [max_eq_left (le_of_lt hpos)] at hval
      linarith
  have hspec : spectrum ℝ T ⊆ {r} := by
    intro t ht
    exact le_antisymm (not_lt.mp (unique r t hr ht)) (not_lt.mp (unique t r ht hr))
  simpa [Algebra.algebraMap_eq_smul_one] using
    CFC.eq_algebraMap_of_spectrum_subset_singleton T r hspec hT

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

@[simp] theorem cyclicPreGNS_apply (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ) (a : A) :
    cyclicPreGNS f π ξ hcoeff (f.toPreGNS a) = π a ξ := rfl

def cyclicGNSMap (f : A →ₚ[ℂ] ℂ) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ) : f.GNS →L[ℂ] H :=
  (cyclicPreGNS f π ξ hcoeff).toContinuousLinearMap.fromCompletion

@[simp] theorem cyclicGNSMap_apply (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ) (a : A) :
    cyclicGNSMap f π ξ hcoeff (f.toPreGNS a : f.GNS) = π a ξ := by
  simp [cyclicGNSMap]

theorem cyclicGNSMap_norm (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ) (x : f.GNS) :
    ‖cyclicGNSMap f π ξ hcoeff x‖ = ‖x‖ := by
  have heq : (fun y : f.GNS => ‖cyclicGNSMap f π ξ hcoeff y‖) = fun y => ‖y‖ := by
    apply Completion.denseRange_coe.equalizer (by fun_prop) (by fun_prop)
    funext y
    change ‖(cyclicPreGNS f π ξ hcoeff).toContinuousLinearMap.fromCompletion (y : f.GNS)‖ = ‖(y : f.GNS)‖
    rw [ContinuousLinearMap.fromCompletion_apply_coe, Completion.norm_coe]
    exact (cyclicPreGNS f π ξ hcoeff).norm_map y
  exact congrFun heq x

def cyclicGNSIsometry (f : A →ₚ[ℂ] ℂ) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ) : f.GNS →ₗᵢ[ℂ] H where
  toLinearMap := (cyclicGNSMap f π ξ hcoeff).toLinearMap
  norm_map' := cyclicGNSMap_norm f π ξ hcoeff

theorem cyclicGNSIsometry_surjective (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ)
    (hcyclic : DenseRange (fun a : A => π a ξ)) :
    Function.Surjective (cyclicGNSIsometry f π ξ hcoeff) := by
  have hrange : IsClosed (Set.range (cyclicGNSIsometry f π ξ hcoeff)) :=
    (cyclicGNSIsometry f π ξ hcoeff).isometry.isClosedEmbedding.isClosed_range
  have htop : Set.range (cyclicGNSIsometry f π ξ hcoeff) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hcyclic.closure_range]
    apply closure_minimal _ hrange
    rintro _ ⟨a, rfl⟩
    exact ⟨(f.toPreGNS a : f.GNS), cyclicGNSMap_apply f π ξ hcoeff a⟩
  exact Set.range_eq_univ.mp htop

def cyclicGNSEquiv (f : A →ₚ[ℂ] ℂ) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ)
    (hcyclic : DenseRange (fun a : A => π a ξ)) : f.GNS ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective (cyclicGNSIsometry f π ξ hcoeff)
    (cyclicGNSIsometry_surjective f π ξ hcoeff hcyclic)

theorem cyclicGNSEquiv_intertwines (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ)
    (hcyclic : DenseRange (fun a : A => π a ξ)) (a : A) (x : f.GNS) :
    cyclicGNSEquiv f π ξ hcoeff hcyclic (f.gnsNonUnitalStarAlgHom a x) =
      π a (cyclicGNSEquiv f π ξ hcoeff hcyclic x) := by
  change cyclicGNSMap f π ξ hcoeff (f.gnsStarAlgHom a x) =
    π a (cyclicGNSMap f π ξ hcoeff x)
  have heq : (fun y : f.GNS => cyclicGNSMap f π ξ hcoeff (f.gnsStarAlgHom a y)) =
      fun y => π a (cyclicGNSMap f π ξ hcoeff y) := by
    apply (gnsVector_cyclic f).equalizer (by fun_prop) (by fun_prop)
    funext b
    simp only [Function.comp_apply, gns_apply_vector, gns_apply_coe, cyclicGNSMap_apply,
      map_mul, mul_apply_eq_comp]
  exact congrFun heq x

end GNS

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_States
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

variable {A : Type*} [CStarAlgebra A] (e : A) (he : IsStarProjection e)

open scoped ComplexOrder InnerProductSpace
open UniformSpace
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def selfAdjointSubspaceInclusion (S : StarSubalgebra ℂ A) :
    selfAdjointSubspace S →L[ℝ] S :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟨a.val, a.property.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (fun a => by simp [one_mul])

omit [PartialOrder A] [StarOrderedRing A] in

theorem character_isState (φ : WeakDual.characterSpace ℂ A) :
    IsState (WeakDual.toStrongDual (φ : WeakDual ℂ A)) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  apply (isState_iff _).mpr
  refine ⟨map_one φ, fun a => ?_⟩
  change (φ (star a * a)).im = 0 ∧ 0 ≤ (φ (star a * a)).re
  rw [map_mul, map_star]
  have h := star_mul_self_nonneg (φ a)
  exact ⟨h.2.symm, h.1⟩

open scoped ComplexOrder InnerProductSpace ComplexStarModule
open UniformSpace

open scoped Topology
open Filter

variable {A : Type*} [CStarAlgebra A] {ι : Type*}

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped ComplexOrder MatrixOrder CStarAlgebra
open Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology
open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem nontrivial_of_state (f : A →L[ℂ] ℂ) (hf : IsState f) : Nontrivial A := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have he := (isState_iff f).mp hf |>.1
  rw [← h, map_zero] at he
  exact zero_ne_one he

theorem state_corner_bound (f : A →L[ℂ] ℂ) (hf : IsState f)
    (p : A) (hp : IsStarProjection p) (a : A) :
    ‖f (p * a * p)‖ ≤ (f p).re * ‖a‖ := by
  have hpos : ∀ x : A, ((cornerFunctional f p) (star x * x)).im = 0 ∧
      0 ≤ ((cornerFunctional f p) (star x * x)).re := by
    intro x
    have he : p * (star x * x) * p = star (x * p) * (x * p) := by
      rw [star_mul, hp.isSelfAdjoint.star_eq]
      noncomm_ring
    simpa only [cornerFunctional_apply, he] using hf.2 (x * p)
  have hh := positive_norm_apply_le (positiveOfSquares (cornerFunctional f p) hpos) a
  simpa only [positiveOfSquares_apply, cornerFunctional_apply, mul_one,
    hp.isIdempotentElem.eq] using hh

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Representations
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.centeredColumnComplete _root_.OAI.NaimarkZFC.centeredRowComplete _root_.OAI.NaimarkZFC.omittedAlgebra_isClosed _root_.OAI.NaimarkZFC.projectionRowComplete _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_isClosed _root_.OAI.NaimarkZFC.traceColumnComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped ComplexStarModule InnerProductSpace
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_commutant_scalar
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (T : H →L[ℂ] H) (hcomm : ∀ a : A, Commute T (π a)) :
    ∃ z : ℂ, T = z • (1 : H →L[ℂ] H) := by
  have hstar (a : A) : Commute (star T) (π a) := by
    change star T * π a = π a * star T
    have hh := congrArg star (hcomm (star a)).eq
    simpa only [star_mul, ← map_star, star_star] using hh.symm
  have hr (a : A) : Commute (realPart T : H →L[ℂ] H) (π a) := by
    rw [realPart_apply_coe]
    exact ((hcomm a).add_left (hstar a)).smul_left _
  have hi (a : A) : Commute (imaginaryPart T : H →L[ℂ] H) (π a) := by
    rw [imaginaryPart_apply_coe]
    exact (((hcomm a).sub_left (hstar a)).smul_left _).smul_left _
  obtain ⟨r, hr⟩ := irreducible_commutant_selfAdjoint_scalar π hπ
    (realPart T) (realPart T).property hr
  obtain ⟨s, hs⟩ := irreducible_commutant_selfAdjoint_scalar π hπ
    (imaginaryPart T) (imaginaryPart T).property hi
  refine ⟨r + Complex.I * s, ?_⟩
  rw [← realPart_add_I_smul_imaginaryPart T, hr, hs]
  simp only [← Complex.coe_smul, smul_smul, add_smul]

variable {ι : Type*} [Fintype ι]

def diagonalHom : (H →L[ℂ] H) →⋆ₐ[ℂ]
    (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) where
  toFun := diagonalOperator
  map_one' := by ext x i; rfl
  map_mul' T S := by ext x i; rfl
  map_zero' := by ext x i; rfl
  map_add' T S := by ext x i; rfl
  commutes' z := by ext x i; rfl
  map_star' T := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change ⟪y, diagonalOperator (ContinuousLinearMap.adjoint T) x⟫_ℂ =
      ⟪y, (ContinuousLinearMap.adjoint (diagonalOperator T)) x⟫_ℂ
    rw [ContinuousLinearMap.adjoint_inner_right]
    simp only [PiLp.inner_apply, diagonalOperator_apply,
      ContinuousLinearMap.adjoint_inner_right]

def diagonalRepresentation (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    A →⋆ₙₐ[ℂ] (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) :=
  diagonalHom.toNonUnitalStarAlgHom.comp π

omit [CompleteSpace H] in

theorem sum_coordinateInclusion [DecidableEq ι] (x : PiLp 2 (fun _ : ι => H)) :
    ∑ i, coordinateInclusion i (x i) = x := by
  ext j
  simp [coordinateInclusion_apply]

omit [CompleteSpace H] in
theorem amplificationBlock_sum [DecidableEq ι]
    (P : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H))
    (x : PiLp 2 (fun _ : ι => H)) (i : ι) :
    P x i = ∑ j, amplificationBlock P i j (x j) := by
  have hh := congrArg (fun z : PiLp 2 (fun _ : ι => H) => (P z) i)
    (sum_coordinateInclusion x)
  simpa only [map_sum, amplificationBlock_apply, WithLp.ofLp_sum, Finset.sum_apply] using hh.symm

theorem amplified_commutant_commute
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (P : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H))
    (hP : ∀ a, Commute P (diagonalOperator (π a))) (T : H →L[ℂ] H) :
    Commute P (diagonalOperator T) := by
  classical
  have hc (i j : ι) (a : A) : Commute (amplificationBlock P i j) (π a) := by
    change amplificationBlock P i j * π a = π a * amplificationBlock P i j
    ext x
    have hh := congrArg (fun Q : PiLp 2 (fun _ : ι => H) →L[ℂ]
        PiLp 2 (fun _ : ι => H) => Q (coordinateInclusion j x) i) (hP a).eq
    simpa only [mul_apply_eq_comp, diagonalOperator_coordinateInclusion,
      diagonalOperator_apply, amplificationBlock_apply] using hh
  have hs (i j : ι) := irreducible_commutant_scalar π hπ
    (amplificationBlock P i j) (hc i j)
  change P * diagonalOperator T = diagonalOperator T * P
  ext x i
  simp only [mul_apply_eq_comp, diagonalOperator_apply]
  rw [amplificationBlock_sum P _ i, amplificationBlock_sum P x i, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  obtain ⟨z, hz⟩ := hs i j
  simp only [diagonalOperator_apply, hz, smul_apply, one_apply_eq_self, map_smul]

theorem irreducible_finite_strong_density
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (x : PiLp 2 (fun _ : ι => H)) (T : H →L[ℂ] H) :
    diagonalOperator T x ∈ closure (Set.range fun a : A => diagonalOperator (π a) x) := by
  let ρ : A →⋆ₙₐ[ℂ] (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) :=
    diagonalRepresentation π
  let M := (orbitMap ρ x).range
  have hm (a : A) : M.map (ρ a).toLinearMap ≤ M := by
    rintro _ ⟨y, ⟨b, rfl⟩, rfl⟩
    refine ⟨a * b, ?_⟩
    simp [orbitMap, map_mul, mul_apply_eq_comp]
  have hinv (a : A) (y : PiLp 2 (fun _ : ι => H)) (hy : y ∈ M.topologicalClosure) :
      ρ a y ∈ M.topologicalClosure := by
    apply Submodule.topologicalClosure_mono (hm a)
    apply Submodule.topologicalClosure_map (ρ a) M
    exact ⟨y, hy, rfl⟩
  let : IsClosed (M.topologicalClosure : Set (PiLp 2 (fun _ : ι => H))) :=
    M.isClosed_topologicalClosure
  have hx : x ∈ M.topologicalClosure := by
    apply M.le_topologicalClosure
    refine ⟨1, ?_⟩
    change diagonalOperator (π 1) x = x
    rw [irreducible_map_one π hπ]
    ext i
    rfl
  have hc (a : A) : Commute M.topologicalClosure.starProjection (diagonalOperator (π a)) := by
    change M.topologicalClosure.starProjection * ρ a = ρ a * M.topologicalClosure.starProjection
    apply ContinuousLinearMap.ext
    intro y
    exact invariant_starProjection_commute ρ M.topologicalClosure hinv a y
  have hp := amplified_commutant_commute π hπ M.topologicalClosure.starProjection hc T
  have he := congrArg (fun Q : PiLp 2 (fun _ : ι => H) →L[ℂ]
    PiLp 2 (fun _ : ι => H) => Q x) hp.eq
  simp only [mul_apply_eq_comp, Submodule.starProjection_eq_self_iff.mpr hx] at he
  show diagonalOperator T x ∈ M.topologicalClosure
  rw [← he]
  exact M.topologicalClosure.starProjection_apply_mem _

theorem irreducible_selfAdjoint_strong_density
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (x : PiLp 2 (fun _ : ι => H)) (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    diagonalOperator T x ∈ closure
      ((fun a : A => diagonalOperator (π a) x) '' {a | IsSelfAdjoint a}) := by
  classical
  let D := PiLp 2 (fun _ : ι => H)
  let : InnerProductSpace ℝ D := InnerProductSpace.rclikeToReal ℂ D
  let ρ : A →⋆ₙₐ[ℂ] (D →L[ℂ] D) := diagonalRepresentation π
  let L : A →ₗ[ℝ] D := (orbitMap ρ x).restrictScalars ℝ
  let M : Submodule ℝ D := (selfAdjoint.submodule ℝ A).map L
  show diagonalOperator T x ∈ M.topologicalClosure
  rw [← M.orthogonal_orthogonal_eq_closure]
  apply (Mᗮ.mem_orthogonal' _).mpr
  intro y hy
  have hz (a : A) : (⟪y, diagonalOperator (π (realPart a : A)) x⟫_ℂ).re = 0 := by
    change ⟪y, diagonalOperator (π (realPart a : A)) x⟫_ℝ = 0
    exact M.inner_left_of_mem_orthogonal
      (show diagonalOperator (π (realPart a : A)) x ∈ M from
        ⟨(realPart a : A), (realPart a).property, rfl⟩) hy
  let z : PiLp 2 (fun _ : ι ⊕ ι => H) := WithLp.toLp 2 (Sum.elim x y)
  let Φ : PiLp 2 (fun _ : ι ⊕ ι => H) → ℝ := fun w =>
    ∑ i, ((⟪y i, w (Sum.inl i)⟫_ℂ).re + (⟪w (Sum.inr i), x i⟫_ℂ).re)
  have hΦ : Continuous Φ := by
    apply continuous_finsetSum
    intro i _
    apply Continuous.add
    · exact Complex.continuous_re.comp
        ((continuous_const.inner (𝕜 := ℂ) (PiLp.continuous_apply 2 (fun _ : ι ⊕ ι => H)
          (Sum.inl i))))
    · exact Complex.continuous_re.comp
        (((PiLp.continuous_apply 2 (fun _ : ι ⊕ ι => H) (Sum.inr i)).inner
          (𝕜 := ℂ) continuous_const))
  have hΦa (a : A) : Φ (diagonalOperator (π a) z) = 0 := by
    change (∑ i, ((⟪y i, π a (x i)⟫_ℂ).re + (⟪π a (y i), x i⟫_ℂ).re)) = 0
    simp_rw [← inner_realPart_operator, ← map_realPart π a]
    rw [← Finset.mul_sum]
    have hh := hz a
    simp only [D, PiLp.inner_apply, Complex.re_sum, diagonalOperator_apply] at hh
    rw [hh, mul_zero]
  have hclosed : IsClosed {w | Φ w = 0} := isClosed_eq hΦ continuous_const
  have hΦT : Φ (diagonalOperator T z) = 0 :=
    (closure_minimal (by rintro _ ⟨a, rfl⟩; exact hΦa a) hclosed)
      (irreducible_finite_strong_density π hπ z T)
  change (⟪diagonalOperator T x, y⟫_ℂ).re = 0
  suffices hs : (⟪y, diagonalOperator T x⟫_ℂ).re = 0 by
    exact (inner_re_symm (𝕜 := ℂ) (diagonalOperator T x) y).trans hs
  have hself : (realPart T : H →L[ℂ] H) = T := hT.coe_realPart
  have he : 2 * (⟪y, diagonalOperator T x⟫_ℂ).re = 0 := by
    change (∑ i, ((⟪y i, T (x i)⟫_ℂ).re + (⟪T (y i), x i⟫_ℂ).re)) = 0 at hΦT
    have hi (i : ι) : 2 * (⟪y i, T (x i)⟫_ℂ).re =
        (⟪y i, T (x i)⟫_ℂ).re + (⟪T (y i), x i⟫_ℂ).re := by
      simpa only [hself] using inner_realPart_operator T (x i) (y i)
    simp_rw [← hi] at hΦT
    simpa only [D, PiLp.inner_apply, Complex.re_sum, diagonalOperator_apply,
      Finset.mul_sum] using hΦT
  linarith

open scoped ComplexStarModule CStarAlgebra
variable {A : Type*} [CStarAlgebra A]

theorem saResolvent_inverse (a : A) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : z.im ≠ 0) :
    (a - algebraMap ℂ A z) * saResolvent a z = 1 ∧
    saResolvent a z * (a - algebraMap ℂ A z) = 1 := by
  let u := cfcUnits (fun t : ℂ => t - z) a (sa_spectrum_sub_ne_zero a ha z hz)
    (continuous_id.sub continuous_const).continuousOn ha.isStarNormal
  have hu : (u : A) = a - algebraMap ℂ A z := by
    change cfc (fun t : ℂ => t - z) a = a - algebraMap ℂ A z
    rw [cfc_sub (fun t : ℂ => t) (fun _ : ℂ => z) a (continuous_id.continuousOn) (continuous_const.continuousOn), cfc_id' ℂ a ha.isStarNormal, cfc_const z a ha.isStarNormal]
  have hv : (↑u⁻¹ : A) = saResolvent a z := rfl
  constructor
  · rw [← hu, ← hv]; exact u.val_inv
  · rw [← hu, ← hv]; exact u.inv_val

theorem saResolvent_norm_le (a : A) (ha : IsSelfAdjoint a)
    (z : ℂ) (hz : z.im ≠ 0) : ‖saResolvent a z‖ ≤ |z.im|⁻¹ := by
  apply norm_cfc_le (inv_nonneg.mpr (abs_nonneg _))
  intro t ht
  rw [norm_inv]
  rw [← one_div, ← one_div]
  apply one_div_le_one_div_of_le (abs_pos.mpr hz)
  have hh := Complex.abs_im_le_norm (t - z)
  simpa only [Complex.sub_im, ha.im_eq_zero_of_mem_spectrum ht, zero_sub, abs_neg] using hh

theorem saResolvent_star (a : A) (ha : IsSelfAdjoint a) (z : ℂ) :
    star (saResolvent a z) = saResolvent a (star z) := by
  rw [saResolvent, ← cfc_star]
  apply cfc_congr
  intro t ht
  have ht' : star t = t := by
    rw [ha.mem_spectrum_eq_re ht]
    simp
  simp only [star_inv₀, star_sub, ht']

theorem saBoundedTransform_selfAdjoint (a : A) (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (saBoundedTransform a) := by
  change star (saBoundedTransform a) = saBoundedTransform a
  simp only [saBoundedTransform, star_add, saResolvent_star a ha, star_neg,
    Complex.star_def, Complex.conj_I, neg_neg, add_comm]

theorem saBoundedTransform_norm_le (a : A) (ha : IsSelfAdjoint a) :
    ‖saBoundedTransform a‖ ≤ 2 := by
  have hp := saResolvent_norm_le a ha Complex.I (by simp)
  have hm := saResolvent_norm_le a ha (-Complex.I) (by simp)
  simp only [Complex.I_im, Complex.neg_im, abs_neg, abs_one, inv_one] at hp hm
  exact (norm_add_le _ _).trans (by linarith)

theorem saBoundedTransform_eq_cfc (a : A) (ha : IsSelfAdjoint a) :
    saBoundedTransform a = cfc (fun t : ℝ => 2 * t / (1 + t ^ 2)) a := by
  rw [cfc_real_eq_complex _ ha]
  rw [saBoundedTransform, saResolvent, saResolvent, ← cfc_add (a := a) _ _
    (saResolvent_continuousOn a ha Complex.I (by simp))
    (saResolvent_continuousOn a ha (-Complex.I) (by simp))]
  apply cfc_congr
  intro t ht
  rw [ha.mem_spectrum_eq_re ht]
  simpa only [Complex.ofReal_re] using resolvent_sum_real t.re

theorem rationalPreimage_rightInverse (t : ℝ) (ht : |t| ≤ 1) :
    2 * rationalPreimage t / (1 + rationalPreimage t ^ 2) = t := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [sq_abs t, abs_nonneg t]
  have hs := Real.sq_sqrt (show 0 ≤ 1 - t ^ 2 by linarith)
  have hp : 0 < 1 + Real.sqrt (1 - t ^ 2) := by positivity
  have hd : 0 < 1 + rationalPreimage t ^ 2 := by positivity
  apply (div_eq_iff (ne_of_gt hd)).mpr
  dsimp [rationalPreimage]
  field_simp
  linear_combination -t * hs

theorem saBoundedTransform_preimage (a : A) (ha : IsSelfAdjoint a) (hn : ‖a‖ ≤ 1) :
    ∃ b : A, IsSelfAdjoint b ∧ saBoundedTransform b = a := by
  let b : A := cfc rationalPreimage a
  have hb : IsSelfAdjoint b := cfc_predicate _ _
  refine ⟨b, hb, ?_⟩
  rw [saBoundedTransform_eq_cfc b hb]
  change cfc (fun t : ℝ => 2 * t / (1 + t ^ 2)) (cfc rationalPreimage a) = a
  have hf : Continuous (fun t : ℝ => 2 * t / (1 + t ^ 2)) :=
    (continuous_const.mul continuous_id).div
      (continuous_const.add (continuous_id.pow 2)) (fun t => ne_of_gt (by positivity))
  rw [← cfc_comp' (fun t : ℝ => 2 * t / (1 + t ^ 2)) rationalPreimage a
    (hf := rationalPreimage_continuous.continuousOn) (hg := hf.continuousOn)]
  calc
    _ = cfc (fun t : ℝ => t) a := by
      apply cfc_congr
      intro t ht
      have ht' : |t| ≤ ‖a‖ := by
        simpa only [Real.norm_eq_abs, mul_one] using
          (spectrum.norm_le_norm_mul_of_mem ht).trans
            (mul_le_mul_of_nonneg_left ((IsStarProjection.one A).norm_le _) (norm_nonneg a))
      exact rationalPreimage_rightInverse t (ht'.trans hn)
    _ = a := cfc_id' ℝ a ha

theorem saResolvent_sub (a b : A) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (z : ℂ) (hz : z.im ≠ 0) :
    saResolvent a z - saResolvent b z =
      saResolvent a z * (b - a) * saResolvent b z := by
  have ha' := (saResolvent_inverse a ha z hz).2
  have hb' := (saResolvent_inverse b hb z hz).1
  symm
  calc
    _ = saResolvent a z * ((b - algebraMap ℂ A z) - (a - algebraMap ℂ A z)) *
        saResolvent b z := by congr 2; abel
    _ = saResolvent a z * ((b - algebraMap ℂ A z) * saResolvent b z) -
        (saResolvent a z * (a - algebraMap ℂ A z)) * saResolvent b z := by noncomm_ring
    _ = _ := by rw [ha', hb']; simp

theorem map_saBoundedTransform {B : Type*} [CStarAlgebra B] (π : A →⋆ₐ[ℂ] B)
    (a : A) (ha : IsSelfAdjoint a) :
    π (saBoundedTransform a) = saBoundedTransform (π a) := by
  simp only [saBoundedTransform, map_add, saResolvent]
  rw [π.map_cfc _ _ (saResolvent_continuousOn a ha Complex.I (by simp))
      (hφ := map_continuous π) (ha := ha.isStarNormal) (hφa := (ha.map π).isStarNormal),
    π.map_cfc _ _ (saResolvent_continuousOn a ha (-Complex.I) (by simp))
      (hφ := map_continuous π) (ha := ha.isStarNormal) (hφa := (ha.map π).isStarNormal)]

theorem saResolvent_eval_sub_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (a b : H →L[ℂ] H) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (z : ℂ) (hz : z.im ≠ 0) (x : H) :
    ‖(saResolvent a z - saResolvent b z) x‖ ≤
      |z.im|⁻¹ * ‖(b - a) (saResolvent b z x)‖ := by
  rw [saResolvent_sub a b ha hb z hz]
  simpa only [mul_apply_eq_comp] using
    ((saResolvent a z).le_opNorm ((b - a) (saResolvent b z x))).trans
      (mul_le_mul_of_nonneg_right (saResolvent_norm_le a ha z hz) (norm_nonneg _))

open scoped InnerProductSpace ComplexStarModule
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_bounded_strong_density
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    {ι : Type*} [Fintype ι] (x : ι → H)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (hn : ‖T‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 2 ∧ ∀ i, ‖π a (x i) - T (x i)‖ < ε := by
  classical
  obtain ⟨S, hS, hST⟩ := saBoundedTransform_preimage T hT hn
  let y : PiLp 2 (fun _ : Sum ι ι => H) := WithLp.toLp 2 (Sum.elim
    (fun i => saResolvent S Complex.I (x i))
    (fun i => saResolvent S (-Complex.I) (x i)))
  have hd := irreducible_selfAdjoint_strong_density π hπ y S hS
  obtain ⟨v, ⟨a, ha, rfl⟩, hv⟩ := Metric.mem_closure_iff.mp hd (ε / 2) (half_pos hε)
  have hv' : ‖diagonalOperator S y - diagonalOperator (π a) y‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hv
  have hc (i : Sum ι ι) : ‖(S - π a) (y i)‖ < ε / 2 := by
    have hh := (PiLp.norm_apply_le (diagonalOperator S y - diagonalOperator (π a) y) i).trans_lt hv'
    simpa only [WithLp.ofLp_sub, Pi.sub_apply, diagonalOperator_apply, sub_apply] using hh
  refine ⟨saBoundedTransform a, saBoundedTransform_selfAdjoint a ha,
    saBoundedTransform_norm_le a ha, ?_⟩
  intro i
  have hp := (saResolvent_eval_sub_le (π a) S (ha.map π) hS Complex.I (by simp) (x i)).trans_lt
    (show |Complex.I.im|⁻¹ * ‖(S - π a) (saResolvent S Complex.I (x i))‖ < ε / 2 by
      simpa [y] using hc (Sum.inl i))
  have hm := (saResolvent_eval_sub_le (π a) S (ha.map π) hS (-Complex.I) (by simp) (x i)).trans_lt
    (show |(-Complex.I).im|⁻¹ * ‖(S - π a) (saResolvent S (-Complex.I) (x i))‖ < ε / 2 by
      simpa [y] using hc (Sum.inr i))
  change ‖irreducibleUnitalRepresentation π hπ (saBoundedTransform a) (x i) - T (x i)‖ < ε
  rw [map_saBoundedTransform _ a ha, ← hST]
  change ‖(saResolvent (π a) Complex.I (x i) + saResolvent (π a) (-Complex.I) (x i)) -
    (saResolvent S Complex.I (x i) + saResolvent S (-Complex.I) (x i))‖ < ε
  rw [show (saResolvent (π a) Complex.I (x i) + saResolvent (π a) (-Complex.I) (x i)) -
      (saResolvent S Complex.I (x i) + saResolvent S (-Complex.I) (x i)) =
      ((saResolvent (π a) Complex.I - saResolvent S Complex.I) (x i)) +
      ((saResolvent (π a) (-Complex.I) - saResolvent S (-Complex.I)) (x i)) by
        simp only [sub_apply]; abel]
  exact (norm_add_le _ _).trans_lt (by linarith)

theorem irreducible_bounded_strong_density_scaled
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    {ι : Type*} [Fintype ι] (x : ι → H)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 2 * ‖T‖ ∧
      ∀ i, ‖π a (x i) - T (x i)‖ < ε := by
  by_cases h0 : T = 0
  · subst T
    refine ⟨0, IsSelfAdjoint.zero _, by simp, ?_⟩
    intro i
    simpa using hε
  have hn : 0 < ‖T‖ := norm_pos_iff.mpr h0
  let S : H →L[ℂ] H := (‖T‖⁻¹ : ℝ) • T
  have hS : IsSelfAdjoint S := (IsSelfAdjoint.all (‖T‖⁻¹ : ℝ)).smul hT
  have hSn : ‖S‖ ≤ 1 := by
    simp [S, norm_smul, inv_mul_cancel₀ (ne_of_gt hn)]
  obtain ⟨a, ha, hab, hap⟩ := irreducible_bounded_strong_density π hπ x S hS hSn
    (ε / ‖T‖) (div_pos hε hn)
  refine ⟨(‖T‖ : ℝ) • a, (IsSelfAdjoint.all (‖T‖ : ℝ)).smul ha, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hn]
    nlinarith
  · intro i
    have he : T = (‖T‖ : ℝ) • S := by
      dsimp [S]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hn), one_smul]
    have hmap : π ((‖T‖ : ℝ) • a) = (‖T‖ : ℝ) • π a := by
      rw [← Complex.coe_smul, map_smul, Complex.coe_smul]
    rw [hmap]
    nth_rw 2 [he]
    rw [smul_apply, smul_apply, ← smul_sub]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hn]
    have hh := mul_lt_mul_of_pos_left (hap i) hn
    simpa only [mul_div_cancel₀ _ (ne_of_gt hn)] using hh

open scoped InnerProductSpace ComplexStarModule
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_selfAdjoint_correction
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (M : Submodule ℂ H) [FiniteDimensional ℂ M]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    ∃ (a : A) (S : H →L[ℂ] H), IsSelfAdjoint a ∧ IsSelfAdjoint S ∧
      ‖a‖ ≤ 2 * ‖T‖ ∧ ‖S‖ ≤ (1 / 2 : ℝ) * ‖T‖ ∧
      ∀ x ∈ M, (π a + S) x = T x := by
  classical
  by_cases h0 : T = 0
  · subst T
    refine ⟨0, 0, IsSelfAdjoint.zero _, IsSelfAdjoint.zero _, by simp, by simp, ?_⟩
    simp
  have hn : 0 < ‖T‖ := norm_pos_iff.mpr h0
  let b := stdOrthonormalBasis ℂ M
  let n := Module.finrank ℂ M
  let ε : ℝ := ‖T‖ / (6 * (n + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨a, ha, han, hap⟩ := irreducible_bounded_strong_density_scaled π hπ
    (fun i => (b i : H)) T hT ε hε
  let S := symmetricCompression M.starProjection (T - π a)
  have hS : IsSelfAdjoint S := symmetricCompression_selfAdjoint _ _
    (isSelfAdjoint_starProjection M) (hT.sub (ha.map π))
  have hb : ‖(T - π a) * M.starProjection‖ ≤ n * ε := by
    calc
      _ ≤ ∑ i, ‖(T - π a) (b i : H)‖ := norm_mul_starProjection_le_sum b _
      _ ≤ ∑ _ : Fin n, ε := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [sub_apply, norm_sub_rev] using (hap i).le
      _ = n * ε := by simp
  have hεeq : ε * (6 * (n + 1)) = ‖T‖ := by
    exact div_mul_cancel₀ _ (by positivity)
  have hnS : ‖S‖ ≤ (1 / 2 : ℝ) * ‖T‖ := by
    have hh := symmetricCompression_norm_le M.starProjection (T - π a)
      (isSelfAdjoint_starProjection M) (hT.sub (ha.map π)) M.starProjection_norm_le
    change ‖S‖ ≤ 3 * ‖(T - π a) * M.starProjection‖ at hh
    nlinarith
  refine ⟨a, S, ha, hS, han, hnS, ?_⟩
  intro x hx
  have hh := symmetricCompression_apply_of_mem (T - π a) hx
  change S x = (T - π a) x at hh
  simp only [add_apply, hh, sub_apply]
  abel

open scoped InnerProductSpace ComplexStarModule
open Filter Topology
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_selfAdjoint_transitivity
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (M : Submodule ℂ H) [FiniteDimensional ℂ M]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 4 * ‖T‖ ∧
      ∀ x ∈ M, π a x = T x := by
  classical
  have hc (S : selfAdjoint (H →L[ℂ] H)) :=
    irreducible_selfAdjoint_correction π hπ M S.val S.property
  choose a S ha hS han hSn heq using hc
  let r : selfAdjoint (H →L[ℂ] H) → selfAdjoint (H →L[ℂ] H) := fun t => ⟨S t, hS t⟩
  let R (n : ℕ) : selfAdjoint (H →L[ℂ] H) := r^[n] ⟨T, hT⟩
  let u (n : ℕ) : A := a (R n)
  have R0 : (R 0 : H →L[ℂ] H) = T := rfl
  have Rsucc (n : ℕ) : (R (n + 1) : H →L[ℂ] H) = S (R n) := by
    exact congrArg Subtype.val (Function.iterate_succ_apply' r n ⟨T, hT⟩)
  have hRn (n : ℕ) : ‖(R n : H →L[ℂ] H)‖ ≤ (1 / 2 : ℝ) ^ n * ‖T‖ := by
    induction n with
    | zero => simp only [R0, pow_zero, one_mul, le_rfl]
    | succ n ih =>
      rw [Rsucc]
      apply (hSn (R n)).trans
      rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left ih (by norm_num)
  have hun (n : ℕ) : ‖u n‖ ≤ (1 / 2 : ℝ) ^ n * (2 * ‖T‖) := by
    apply (han (R n)).trans
    calc
      2 * ‖(R n : H →L[ℂ] H)‖ ≤ 2 * ((1 / 2 : ℝ) ^ n * ‖T‖) := by gcongr; exact hRn n
      _ = _ := by ring
  have sNu : Summable (fun n => ‖u n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hun
      (summable_geometric_two.mul_right (2 * ‖T‖))
  have su : Summable u := sNu.of_norm
  have hua : IsSelfAdjoint (∑' n, u n) := by
    change star (∑' n, u n) = ∑' n, u n
    rw [tsum_star]
    exact tsum_congr (fun n => (ha (R n)).star_eq)
  have hub : ‖∑' n, u n‖ ≤ 4 * ‖T‖ := by
    calc
      _ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm sNu
      _ ≤ ∑' n, (1 / 2 : ℝ) ^ n * (2 * ‖T‖) :=
        sNu.tsum_le_tsum hun (summable_geometric_two.mul_right _)
      _ = 4 * ‖T‖ := by rw [tsum_mul_right, tsum_geometric_two]; ring
  refine ⟨∑' n, u n, hua, hub, ?_⟩
  intro x hx
  have hs (n : ℕ) : π (∑ i ∈ Finset.range n, u i) x = T x - (R n : H →L[ℂ] H) x := by
    induction n with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, map_zero, zero_apply, R0, sub_self]
    | succ n ih =>
      rw [Finset.sum_range_succ, map_add, add_apply, ih, Rsucc]
      have hh := heq (R n) x hx
      change π (u n) x + S (R n) x = (R n : H →L[ℂ] H) x at hh
      rw [← hh]
      abel
  have hlimR : Tendsto (fun n => (R n : H →L[ℂ] H) x) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hbound (n : ℕ) : ‖(R n : H →L[ℂ] H) x‖ ≤
        (1 / 2 : ℝ) ^ n * (‖T‖ * ‖x‖) := by
      calc
        _ ≤ ‖(R n : H →L[ℂ] H)‖ * ‖x‖ := (R n : H →L[ℂ] H).le_opNorm x
        _ ≤ ((1 / 2 : ℝ) ^ n * ‖T‖) * ‖x‖ :=
          mul_le_mul_of_nonneg_right (hRn n) (norm_nonneg x)
        _ = _ := by ring
    apply squeeze_zero (fun n => norm_nonneg _) hbound
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)).mul_const (‖T‖ * ‖x‖)
    simpa only [zero_mul] using hh
  have hlim := ((orbitCLM π x).continuous.tendsto (∑' n, u n)).comp su.hasSum.tendsto_sum_nat
  change Tendsto (fun n => π (∑ i ∈ Finset.range n, u i) x) atTop (𝓝 (π (∑' n, u n) x)) at hlim
  simp only [hs] at hlim
  have hlim' : Tendsto (fun n => T x - (R n : H →L[ℂ] H) x) atTop (𝓝 (T x)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hlimR
  exact tendsto_nhds_unique hlim hlim'

open scoped InnerProductSpace ComplexStarModule CStarAlgebra
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
universe u v w

variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

variable [PartialOrder A] [StarOrderedRing A]

theorem cyclic_representation_equivalent (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hc : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ)
    (hd : DenseRange (fun a : A => π a ξ)) :
    UnitarilyEquivalent f.gnsNonUnitalStarAlgHom π :=
  ⟨cyclicGNSEquiv f π ξ hc hd, cyclicGNSEquiv_intertwines f π ξ hc hd⟩

theorem irreducible_equivalent_of_coefficients
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hρ : IsIrreducible ρ)
    (ξ : H) (η : K) (hξ : ξ ≠ 0) (hη : η ≠ 0)
    (hc : ∀ a : A, ⟪ξ, π a ξ⟫_ℂ = ⟪η, ρ a η⟫_ℂ) :
    UnitarilyEquivalent π ρ := by
  let f : A →ₚ[ℂ] ℂ := positiveOfSquares (vectorFunctional π ξ)
    (fun a => by
      rw [vectorFunctional_square, ← Complex.ofReal_pow]
      exact ⟨rfl, sq_nonneg _⟩)
  have hfc (a : A) : f a = ⟪ξ, π a ξ⟫_ℂ := rfl
  exact (cyclic_representation_equivalent f π ξ hfc
    (irreducible_vector_cyclic π hπ ξ hξ)).symm.trans
    (cyclic_representation_equivalent f ρ η (fun a => (hfc a).trans (hc a))
      (irreducible_vector_cyclic ρ hρ η hη))

open scoped InnerProductSpace ComplexStarModule
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_adjoint_transitivity
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (M : Submodule ℂ H) [FiniteDimensional ℂ M] (T : H →L[ℂ] H) :
    ∃ a : A, ‖a‖ ≤ 8 * ‖T‖ ∧ ∀ x ∈ M,
      π a x = T x ∧ π (star a) x = star T x := by
  obtain ⟨b, hb, hbn, hbM⟩ := irreducible_selfAdjoint_transitivity π hπ M
    (realPart T) (realPart T).property
  obtain ⟨c, hc, hcn, hcM⟩ := irreducible_selfAdjoint_transitivity π hπ M
    (imaginaryPart T) (imaginaryPart T).property
  refine ⟨b + Complex.I • c, ?_, ?_⟩
  · have hbr := realPart.norm_le T
    have hci := imaginaryPart.norm_le T
    calc
      _ ≤ ‖b‖ + ‖Complex.I • c‖ := norm_add_le _ _
      _ = ‖b‖ + ‖c‖ := by rw [norm_smul, Complex.norm_I, one_mul]
      _ ≤ 8 * ‖T‖ := by
        change ‖(realPart T : H →L[ℂ] H)‖ ≤ ‖T‖ at hbr
        change ‖(imaginaryPart T : H →L[ℂ] H)‖ ≤ ‖T‖ at hci
        linarith
  · intro x hx
    constructor
    · rw [map_add, map_smul, add_apply, smul_apply, hbM x hx, hcM x hx]
      exact congrArg (fun S : H →L[ℂ] H => S x) (realPart_add_I_smul_imaginaryPart T)
    · simp only [star_add, star_smul, hb.star_eq, hc.star_eq, Complex.star_def,
        Complex.conj_I, map_add, map_smul, add_apply, smul_apply, hbM x hx, hcM x hx]
      have hh := congrArg star (realPart_add_I_smul_imaginaryPart T)
      simp only [star_add, star_smul, (realPart T).property.star_eq,
        (imaginaryPart T).property.star_eq, Complex.star_def, Complex.conj_I] at hh
      exact congrArg (fun S : H →L[ℂ] H => S x) hh

theorem irreducible_null_decomposition
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1) (a : A) (ha : ⟪ξ, π a ξ⟫_ℂ = 0) :
    ∃ b c : A, π b ξ = 0 ∧ π c ξ = 0 ∧ a = b + star c := by
  let T := InnerProductSpace.rankOne ℂ ξ (π a ξ)
  obtain ⟨c, _, hc⟩ := irreducible_adjoint_transitivity π hπ
    (Submodule.span ℂ {ξ}) T
  have hξM : ξ ∈ Submodule.span ℂ {ξ} := Submodule.subset_span (Set.mem_singleton ξ)
  have hc0 : π c ξ = 0 := by
    rw [(hc ξ hξM).1]
    simp [T, InnerProductSpace.rankOne_apply, inner_eq_zero_symm.mp ha]
  have hcstar : π (star c) ξ = π a ξ := by
    rw [(hc ξ hξM).2]
    simp [T, ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne,
      InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, hξ]
  refine ⟨a - star c, c, ?_, hc0, (sub_add_cancel _ _).symm⟩
  rw [map_sub, sub_apply, hcstar, sub_self]

open scoped CStarAlgebra InnerProductSpace ComplexStarModule
open Filter Topology
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorNullAlgebra (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    NonUnitalStarSubalgebra ℂ A where
  carrier := {a | π a ξ = 0 ∧ π (star a) ξ = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    simp [map_add, add_apply, star_add, ha, hb, ha', hb']
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    simp [map_mul, mul_apply_eq_comp, star_mul, hb, ha']
  smul_mem' := by
    rintro z a ⟨ha, ha'⟩
    simp [map_smul, smul_apply, star_smul, ha, ha']
  star_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by simpa only [star_star] using ha⟩

instance vectorNullAlgebra_closed (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    IsClosed (vectorNullAlgebra π ξ : Set A) := by
  have hp : Continuous (fun a : A => π a ξ) :=
    (ContinuousLinearMap.apply ℂ H ξ).continuous.comp (map_continuous π)
  exact (isClosed_eq hp continuous_const).inter
    (isClosed_eq (hp.comp continuous_star) continuous_const)

instance (priority := 1100) vectorNullAlgebra_order (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    PartialOrder (vectorNullAlgebra π ξ) := CStarAlgebra.spectralOrder _

instance (priority := 1100) vectorNullAlgebra_starOrdered (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    StarOrderedRing (vectorNullAlgebra π ξ) := CStarAlgebra.spectralOrderedRing _

theorem star_mul_self_mem_vectorNullAlgebra (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (ξ : H) {a : A} (ha : π a ξ = 0) : star a * a ∈ vectorNullAlgebra π ξ := by
  constructor <;> simp [map_mul, star_mul, mul_apply_eq_comp, ha]

variable [PartialOrder A] [StarOrderedRing A]

open scoped InnerProductSpace ComplexStarModule CStarAlgebra
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule
open Filter Topology
variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [PartialOrder A] [StarOrderedRing A] in

theorem nullAlgebra_vector_coefficient
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hone : ρ 1 = 1)
    (η : K) (hη : ‖η‖ = 1)
    (hnull : ∀ e : vectorNullAlgebra π ξ, ρ (e : A) η = 0) :
    ∀ a : A, ⟪ξ, π a ξ⟫_ℂ = ⟪η, ρ a η⟫_ℂ := by
  have hL (b : A) (hb : π b ξ = 0) : ρ b η = 0 := by
    have hh := hnull ⟨star b * b, star_mul_self_mem_vectorNullAlgebra π ξ hb⟩
    have hi : ⟪ρ b η, ρ b η⟫_ℂ = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
        ← map_star, ← mul_apply_eq_comp, ← map_mul, hh, inner_zero_right]
    exact inner_self_eq_zero.mp hi
  intro a
  let a₀ := a - ⟪ξ, π a ξ⟫_ℂ • (1 : A)
  have ha₀ : ⟪ξ, π a₀ ξ⟫_ℂ = 0 := by
    simp [a₀, map_sub, map_smul, sub_apply, smul_apply, irreducible_map_one π hπ,
      one_apply_eq_self, inner_self_eq_norm_sq_to_K, hξ]
  obtain ⟨b, c, hb, hc, hbc⟩ := irreducible_null_decomposition π hπ ξ hξ a₀ ha₀
  have hzero : ⟪η, ρ a₀ η⟫_ℂ = 0 := by
    rw [hbc, map_add, add_apply, inner_add_right, hL b hb, inner_zero_right,
      zero_add, map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, hL c hc, inner_zero_left]
  dsimp only [a₀] at hzero
  simp only [map_sub, map_smul, sub_apply, smul_apply, hone, one_apply_eq_self,
    inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hη,
    ] at hzero
  norm_num at hzero
  exact (sub_eq_zero.mp hzero).symm

theorem inequivalent_nullAlgebra_common_kernel
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hρ : IsIrreducible ρ)
    (hne : ¬ UnitarilyEquivalent π ρ) (η : K)
    (hnull : ∀ e : vectorNullAlgebra π ξ, ρ (e : A) η = 0) : η = 0 := by
  by_contra hη
  let ζ : K := ‖η‖⁻¹ • η
  have hζ : ‖ζ‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hη)]
  have hζ0 : ζ ≠ 0 := by intro h; simp only [h, norm_zero, zero_ne_one] at hζ
  have hξ0 : ξ ≠ 0 := by intro h; simp only [h, norm_zero, zero_ne_one] at hξ
  have hznull (e : vectorNullAlgebra π ξ) : ρ (e : A) ζ = 0 := by
    change (ρ (e : A)) (‖η‖⁻¹ • η) = 0
    rw [ContinuousLinearMap.map_smul_of_tower, hnull, smul_zero]
  exact hne (irreducible_equivalent_of_coefficients π hπ ρ hρ ξ ζ hξ0 hζ0
    (nullAlgebra_vector_coefficient π hπ ξ hξ ρ (irreducible_map_one ρ hρ) ζ hζ hznull))

open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology

namespace ExcisionIndex
variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem tendsto_coe : Tendsto (fun e : ExcisionIndex B => e.val) atTop
    (CStarAlgebra.approximateUnit B) := by
  rw [(CStarAlgebra.hasBasis_approximateUnit B).tendsto_right_iff]
  intro b hb
  filter_upwards [eventually_ge_atTop (⟨b, hb⟩ : ExcisionIndex B)] with e he
  exact ⟨he, by simpa using e.property.2.le⟩

end ExcisionIndex

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def pureExcisionNet (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (e : ExcisionIndex (vectorNullAlgebra π ξ)) : A := 1 - (e.val : A)

open scoped InnerProductSpace ComplexStarModule
open Filter Topology
variable {B : Type*} [NonUnitalCStarAlgebra B]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {ι : Type*} {l : Filter ι}

theorem excision_inequivalent_strong
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π) (ξ : H) (hξ : ‖ξ‖ = 1)
    (x : ι → A) (hx : ∀ i, 0 ≤ x i) (hxn : ∀ i, ‖x i‖ ≤ 1)
    (hexc : ∀ a : A, Tendsto (fun i => x i * (a - ⟪ξ, π a ξ⟫_ℂ • (1 : A)) * x i)
      l (𝓝 0))
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hρ : IsIrreducible ρ)
    (hne : ¬ UnitarilyEquivalent π ρ) (η : K) :
    Tendsto (fun i => ρ (x i) η) l (𝓝 0) := by
  let j := NonUnitalStarSubalgebraClass.subtype (vectorNullAlgebra π ξ)
  apply strong_zero_of_nondegenerate (fun i => ρ (x i))
    (fun i => (NonUnitalStarAlgHom.norm_apply_le ρ _).trans (hxn i)) (ρ.comp j)
    (fun η hη => inequivalent_nullAlgebra_common_kernel π hπ ξ hξ ρ hρ hne η hη)
  intro b ζ
  have ht := excision_null_mul_tendsto π ξ x hx hexc b.val b.property.2
  have hc : Continuous (fun a : A => ρ a ζ) :=
    (ContinuousLinearMap.apply ℂ K ζ).continuous.comp (map_continuous ρ)
  simpa only [Function.comp_def, map_mul, mul_apply_eq_comp, map_zero, zero_apply,
    NonUnitalStarAlgHom.comp_apply, j, NonUnitalStarSubalgebraClass.coe_subtype] using
    (hc.tendsto 0).comp ht

omit [PartialOrder A] [StarOrderedRing A] in

theorem irreducible_nullAlgebra_fixes_orthogonal
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π) (ξ : H) (hξ : ‖ξ‖ = 1)
    (η : H) (horth : ⟪ξ, η⟫_ℂ = 0) :
    ∃ b : vectorNullAlgebra π ξ, π (b : A) η = η := by
  let M := Submodule.span ℂ ({ξ, η} : Set H)
  let : FiniteDimensional ℂ M := FiniteDimensional.span_of_finite ℂ ((Set.finite_singleton η).insert ξ)
  let T : H →L[ℂ] H := 1 - InnerProductSpace.rankOne ℂ ξ ξ
  have hT : IsSelfAdjoint T := by
    change star T = T
    simp only [T, star_sub, star_one, ContinuousLinearMap.star_eq_adjoint,
      InnerProductSpace.adjoint_rankOne]
  obtain ⟨b, hb, _, hbM⟩ := irreducible_selfAdjoint_transitivity π hπ M T hT
  have hbξ : π b ξ = 0 := by
    rw [hbM ξ (Submodule.subset_span (by simp))]
    simp [T, sub_apply, InnerProductSpace.rankOne_apply, one_apply_eq_self,
      inner_self_eq_norm_sq_to_K, hξ]
  refine ⟨⟨b, hbξ, by simpa only [hb.star_eq] using hbξ⟩, ?_⟩
  rw [hbM η (Submodule.subset_span (by simp))]
  simp [T, sub_apply, InnerProductSpace.rankOne_apply, one_apply_eq_self, horth]

theorem excision_orthogonal_strong
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π) (ξ : H) (hξ : ‖ξ‖ = 1)
    (x : ι → A) (hx : ∀ i, 0 ≤ x i)
    (hexc : ∀ a : A, Tendsto (fun i => x i * (a - ⟪ξ, π a ξ⟫_ℂ • (1 : A)) * x i)
      l (𝓝 0)) (η : H) (horth : ⟪ξ, η⟫_ℂ = 0) :
    Tendsto (fun i => π (x i) η) l (𝓝 0) := by
  obtain ⟨b, hbη⟩ := irreducible_nullAlgebra_fixes_orthogonal π hπ ξ hξ η horth
  have ht := excision_null_mul_tendsto π ξ x hx hexc b.val b.property.2
  have hc : Continuous (fun a : A => π a η) :=
    (ContinuousLinearMap.apply ℂ H η).continuous.comp (map_continuous π)
  simpa only [Function.comp_def, map_mul, mul_apply_eq_comp, hbη,
    map_zero, zero_apply] using (hc.tendsto 0).comp ht

open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology
open scoped ComplexOrder

open Filter Topology
open scoped ComplexOrder ComplexStarModule OnePoint InnerProductSpace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (hp0 : p 0 = 1)
variable (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ n, 0 < (τ (peakAtom p n)).re)

def peakingCoefficientsPositive : A →ₚ[ℂ] SequenceDiagonal :=
  PositiveLinearMap.mk₀ (peakingCoefficients hp τ hτ hpos).toLinearMap (fun a ha t => by
    induction t using OnePoint.rec with
    | infty => exact (positiveOfSquares f hp.2.2.1.2).map_nonneg ha
    | coe n => exact (positiveOfSquares _
        (cornerState_isState τ hτ _ (hp.peakAtom_projection n) (hpos n)).2).map_nonneg ha)

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {ι : Type*} {l : Filter ι}

theorem peaking_endpoint_decay [Preorder ι]
    {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re)
    (x : ι → A) (hx : ∀ i, 0 ≤ x i) (hxn : ∀ i, ‖x i‖ ≤ 1) (hm : Antitone x)
    (htrace : Tendsto (fun i => τ (x i)) atTop (𝓝 0)) (a : A)
    (hinfty : Tendsto (fun i => f (star a*x i*a)) atTop (𝓝 0)) :
    Tendsto (fun i => peakingCoefficients hp τ hτ hpos (star a*(x i*x i)*a)) atTop (𝓝 0) := by
  let E := peakingCoefficientsPositive hp τ hτ hpos
  have hE (i : ι) : 0 ≤ E (star a*x i*a) :=
    E.map_nonneg (star_left_conjugate_nonneg (hx i) a)
  have hmono : Antitone (fun i => E (star a*x i*a)) := by
    intro i j hij
    exact E.monotone (star_left_conjugate_le_conjugate (hm hij) a)
  have ht : Tendsto (fun i => E (star a*x i*a)) atTop (𝓝 0) := by
    apply positive_dini _ hE hmono
    intro t
    induction t using OnePoint.rec with
    | infty => exact hinfty
    | coe n =>
      have hh := trace_sandwich_tendsto (positiveOfSquares τ hτ.2) htr x hx htrace (a*peakAtom p n)
      have he (i : ι) :
          E (star a*x i*a) n = (τ (peakAtom p n)).re⁻¹ •
            τ (star (a*peakAtom p n)*x i*(a*peakAtom p n)) := by
        change cornerState τ (peakAtom p n) (star a*x i*a) = _
        rw [cornerState_apply, star_mul, (hp.peakAtom_projection n).isSelfAdjoint.star_eq]
        simp only [mul_assoc]
      simp_rw [he]
      simpa only [smul_zero, positiveOfSquares_apply] using hh.const_smul (τ (peakAtom p n)).re⁻¹
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (g := fun i => ‖E (star a*x i*a)‖) (fun i => norm_nonneg _)
  · intro i
    exact CStarAlgebra.norm_le_norm_of_nonneg_of_le (hab :=
      (E.monotone (star_left_conjugate_le_conjugate
        (positive_contraction_square_le (hx i) (hxn i)) a)))
      (E.map_nonneg (star_left_conjugate_nonneg
        (by simpa only [(IsSelfAdjoint.of_nonneg (hx i)).star_eq] using
          star_mul_self_nonneg (x i)) a))
  · simpa only [norm_zero] using ht.norm

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open Filter Topology
open scoped ComplexOrder ComplexStarModule InnerProductSpace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {ι : Type*} {l : Filter ι}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem peaking_endpoint_of_excision [Preorder ι]
    {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (h : A →L[ℂ] ℂ) (hh : IsPureState h)
    (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re)
    (x : ι → A) (hx : ∀ i, 0 ≤ x i) (hxn : ∀ i, ‖x i‖ ≤ 1) (hm : Antitone x)
    (htrace : Tendsto (fun i => τ (x i)) atTop (𝓝 0))
    (hexc : ∀ b : A, Tendsto (fun i => x i*(b-h b • (1:A))*x i) atTop (𝓝 0))
    (a : A) (hcase : ¬ UnitarilyEquivalent (pureGNS h hh) (pureGNS f hp.isPureState) ∨
      h = f ∧ f a = 0) :
    Tendsto (fun i => peakingCoefficients hp τ hτ hpos (star a*(x i*x i)*a)) atTop (𝓝 0) := by
  apply peaking_endpoint_decay hp τ hτ htr hpos x hx hxn hm htrace a
  let g := positiveOfSquares f hp.2.2.1.2
  let ρ := g.gnsNonUnitalStarAlgHom
  let ξ := gnsVector g
  have hρ : IsIrreducible ρ := pure_gns_irreducible f hp.2.2.1 hp.isPureState
  have hξ : ‖ξ‖ = 1 := gnsVector_norm_eq_one g ((isState_iff f).mp hp.2.2.1).1
  have hcoeff (b : A) : ⟪ξ, ρ b ξ⟫_ℂ = f b := gnsVector_coefficient g b
  have ht : Tendsto (fun i => ρ (x i) (ρ a ξ)) atTop (𝓝 0) := by
    rcases hcase with hine | ⟨rfl, ha⟩
    · let g' := positiveOfSquares h hh.1.2
      let π := g'.gnsNonUnitalStarAlgHom
      let η := gnsVector g'
      have hπ : IsIrreducible π := pure_gns_irreducible h hh.1 hh
      have hη : ‖η‖ = 1 := gnsVector_norm_eq_one g' ((isState_iff h).mp hh.1).1
      have hcoeff' (b : A) : ⟪η, π b η⟫_ℂ = h b := gnsVector_coefficient g' b
      apply excision_inequivalent_strong π hπ η hη x hx hxn
        (fun b => ?_) ρ hρ hine (ρ a ξ)
      simpa only [hcoeff'] using hexc b
    · refine excision_orthogonal_strong ρ hρ ξ hξ x hx ?_ (ρ a ξ) ?_
      · intro b
        simpa only [hcoeff] using hexc b
      · simpa only [hcoeff] using ha
  simpa only [hcoeff] using
    vector_sandwich_tendsto ρ ξ x a ht

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Amalgamation
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

attribute [local instance] Classical.propDecidable

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter
open scoped Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem trace_projection_right_strong_zero (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    {ι : Type*} (l : Filter ι) (p : ι → A) (hp : ∀ i, IsStarProjection (p i))
    (hlim : Tendsto (fun i => (τ (p i)).re) l (𝓝 0)) (x : τ.GNS) :
    Tendsto (fun i => gnsRight τ hτ (p i) x) l (𝓝 0) := by
  have hvac : Tendsto (fun i => (τ.toPreGNS (p i) : τ.GNS)) l (𝓝 0) := by
    simpa only [traceVacuum_left] using trace_projection_strong_zero τ hτ l p hp hlim (traceVacuum τ)
  apply tendsto_zero_of_dense_contractives l (fun i => gnsRight τ hτ (p i))
    (fun i => (NonUnitalStarAlgHom.norm_apply_le (gnsRightStarAlgHom τ hτ)
      (MulOpposite.op (p i))).trans ((hp i).norm_le _))
    (fun a : A => (τ.toPreGNS a : τ.GNS))
    (Completion.denseRange_coe.comp τ.toPreGNS.surjective.denseRange (Completion.continuous_coe _))
    _ x
  intro a
  have h := (τ.gnsStarAlgHom a).continuous.continuousAt.tendsto.comp hvac
  simpa [Function.comp_def] using h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter
open scoped Topology
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped InnerProductSpace
variable {V : Type*} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace
variable {V A H : Type*} [CStarAlgebra A] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace lp

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem columnUnit_inner_action (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) (a : A) :
    inner ℂ (columnUnit τ hτ q) (traceColumnRepresentation τ hτ q a (columnUnit τ hτ q)) =
      (((Real.sqrt (τ q.1).re)⁻¹ : ℂ) ^ 2) * τ (q.1 * a * q.1) := by
  rw [columnUnit, map_smul]
  rw [inner_smul_left (𝕜 := ℂ) (columnVacuum τ hτ q) _]
  rw [inner_smul_right (𝕜 := ℂ) (columnVacuum τ hτ q) _]
  have hv : inner ℂ (columnVacuum τ hτ q)
      (traceColumnRepresentation τ hτ q a (columnVacuum τ hτ q)) = τ (q.1 * a * q.1) := by
    change inner ℂ (columnVacuum τ hτ q : τ.GNS)
      (traceColumnRepresentation τ hτ q a (columnVacuum τ hτ q) : τ.GNS) = _
    rw [columnVacuum_action]
    change inner ℂ (τ.toPreGNS q.1 : τ.GNS) (τ.toPreGNS (a * q.1) : τ.GNS) = _
    simp only [Completion.inner_coe, PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS, q.property.isSelfAdjoint.star_eq, mul_assoc]
  rw [hv]
  simp only [map_inv₀, Complex.conj_ofReal]
  ring

theorem columnUnit_action_norm_sq (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) (ht : 0 < (τ q.1).re) (a : A) :
    ‖traceColumnRepresentation τ hτ q a (columnUnit τ hτ q)‖ ^ 2 =
      (τ (q.1 * (star a * a) * q.1)).re / (τ q.1).re := by
  let π := traceColumnRepresentation τ hτ q
  let ξ := columnUnit τ hτ q
  have h : inner ℂ (π a ξ) (π a ξ) = inner ℂ ξ (π (star a * a) ξ) := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    have hs : (π a).adjoint = π (star a) := (map_star π a).symm
    rw [hs]
    rw [map_mul]
    rfl
  have hr := congrArg Complex.re h
  have hn : (inner ℂ (π a ξ) (π a ξ)).re = ‖π a ξ‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (π a ξ)).symm
  rw [hn] at hr
  rw [columnUnit_inner_action] at hr
  simp only [← Complex.ofReal_inv, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hr
  have hs : (Real.sqrt (τ q.1).re) ^ 2 = (τ q.1).re := Real.sq_sqrt ht.le
  simpa only [inv_pow, hs, div_eq_mul_inv, mul_comm] using hr

open Filter Topology
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem traceRightAtoms_jointKernel (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re)
    (x : τ.GNS) (hx : ∀ l, gnsRight τ hτ (e l).1 x = 0) : x = 0 := by
  classical
  let p : Finset V → A := fun s => 1 - ∑ l ∈ s, (e l).1
  have hp : ∀ s, IsStarProjection (p s) := fun s => (finiteAtomSum_projection e horth s).one_sub
  have hlim : Tendsto (fun s => (τ (p s)).re) atTop (𝓝 0) := by
    simpa only [p, map_sub, map_sum, Complex.sub_re, Complex.re_sum, sub_self] using
      (tendsto_const_nhds (x := (τ 1).re) (f := (atTop : Filter (Finset V)))).sub hmass
  have hstrong := trace_projection_right_strong_zero τ hτ atTop p hp hlim x
  have he (s : Finset V) : gnsRight τ hτ (p s) x = x := by
    change gnsRightStarAlgHom τ hτ (MulOpposite.op (p s)) x = x
    simp only [p, MulOpposite.op_sub, MulOpposite.op_one, Finset.op_sum,
      map_sub, map_one, map_sum, sub_apply, one_apply_eq_self, sum_apply]
    change x - ∑ l ∈ s, gnsRight τ hτ (e l).1 x = x
    simp only [hx, Finset.sum_const_zero, sub_zero]
  simp only [he] at hstrong
  exact tendsto_nhds_unique tendsto_const_nhds hstrong

open Filter Topology
open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem trace_hasSum_atom_corners (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re) (a : A) :
    HasSum (fun r => τ ((e r).1 * a * (e r).1)) (τ a) := by
  classical
  let p : Finset V → A := fun s => 1 - ∑ r ∈ s, (e r).1
  have hp : ∀ s, IsStarProjection (p s) := fun s => (finiteAtomSum_projection e horth s).one_sub
  have hlim : Tendsto (fun s => (τ (p s)).re) atTop (𝓝 0) := by
    simpa only [p, map_sub, map_sum, Complex.sub_re, Complex.re_sum, sub_self] using
      (tendsto_const_nhds (x := (τ 1).re) (f := (atTop : Filter (Finset V)))).sub hmass
  have hstrong := trace_projection_right_strong_zero τ hτ atTop p hp hlim
    (τ.toPreGNS a : τ.GNS)
  have hz := ((innerSL ℂ (traceVacuum τ)).continuous.tendsto 0).comp hstrong
  have hc (r : V) : τ (a * (e r).1) = τ ((e r).1 * a * (e r).1) := by
    rw [hτ ((e r).1 * a) (e r).1, ← mul_assoc, (e r).property.isIdempotentElem.eq,
      hτ (e r).1 a]
  have he (s : Finset V) : inner ℂ (traceVacuum τ)
      (gnsRight τ hτ (p s) (τ.toPreGNS a : τ.GNS)) =
        τ a - ∑ r ∈ s, τ ((e r).1 * a * (e r).1) := by
    rw [gnsRight_coe]
    simp only [traceVacuum, Completion.inner_coe, PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul, p, mul_sub,
      mul_one, Finset.mul_sum, map_sub, map_sum, hc]
  simp only [map_zero] at hz
  change Tendsto (fun s => inner ℂ (traceVacuum τ)
    (gnsRight τ hτ (p s) (τ.toPreGNS a : τ.GNS))) atTop (𝓝 0) at hz
  simp only [he] at hz
  have ht := (tendsto_const_nhds (x := τ a) (f := (atTop : Filter (Finset V)))).sub hz
  simpa only [HasSum, SummationFilter.unconditional_filter, sub_sub_cancel, sub_zero] using ht

attribute [local instance] Classical.propDecidable

open scoped InnerProductSpace ENNReal lp

variable {ι κ : Type*} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

variable {ι : Type*} {J : ι → Type*} {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, CompleteSpace (H i)]

open scoped InnerProductSpace ENNReal lp

variable {ι : Type*} {H K : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedAddCommGroup (K i)]
  [∀ i, InnerProductSpace ℂ (H i)] [∀ i, InnerProductSpace ℂ (K i)]

variable [∀ i, CompleteSpace (H i)] [∀ i, CompleteSpace (K i)]

variable {A : Type*} [CStarAlgebra A]

open scoped InnerProductSpace ENNReal lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]

open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]

open scoped InnerProductSpace lp
variable {V J : Type*}

open scoped InnerProductSpace ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section

variable {V B : Type*} [Ring B] [Algebra ℂ B]

variable (q : V → B)
variable (hq : ∀ r, q r * q r = q r)
variable (ho : ∀ r t, r ≠ t → q r * q t = 0)

omit [Algebra ℂ B] in
include hq ho in
lemma sum_mul_atom [DecidableEq V] (s : Finset V) (r : V) :
    (∑ t ∈ s, q t) * q r = if r ∈ s then q r else 0 := by
  rw [Finset.sum_mul]
  by_cases hr : r ∈ s
  · rw [ite_eq_left hr, Finset.sum_eq_single r]
    · exact hq r
    · intro t _ ht
      exact ho t r ht
    · exact fun hn => (hn hr).elim
  · rw [ite_eq_right hr]
    exact Finset.sum_eq_zero fun t ht => ho t r (by rintro rfl; exact hr ht)

variable (φ : B →ₗ[ℂ] ℂ)

include hq ho in
theorem finiteAtomExpectation_atom [DecidableEq V] (s : Finset V) (a : B) (r : V) :
    q r * finiteAtomExpectation q φ s a * q r =
      if r ∈ s then (φ (q r * a * q r) / φ (q r)) • q r else 0 := by
  simp only [finiteAtomExpectation, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc]
  by_cases hr : r ∈ s
  · rw [ite_eq_left hr, Finset.sum_eq_single r]
    · rw [hq, hq]
    · intro t _ ht
      rw [ho r t ht.symm, zero_mul, smul_zero]
    · exact fun hn => (hn hr).elim
  · rw [ite_eq_right hr]
    apply Finset.sum_eq_zero
    intro t ht
    rw [ho r t (by rintro rfl; exact hr ht), zero_mul, smul_zero]

end

open Filter Topology
open scoped lp

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_HNN
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra Matrix

open scoped CStarAlgebra

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra

open scoped InnerProductSpace lp

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra

open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule

open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder

open scoped ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace
open UniformSpace
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem gns_vector_zero_of_square_zero (f : A →ₚ[ℂ] ℂ) (a : A)
    (ha : f (star a*a) = 0) : f.gnsStarAlgHom a (gnsVector f) = 0 := by
  apply norm_eq_zero.mp
  rw [gns_apply_vector,Completion.norm_coe,PositiveLinearMap.preGNS_norm_def,
    PositiveLinearMap.ofPreGNS_toPreGNS,ha,Complex.zero_re,Real.sqrt_zero]

theorem gns_kills_ideal (f : A →ₚ[ℂ] ℂ) (J : TwoSidedIdeal A)
    (hf : ∀ a ∈ J, f (star a*a) = 0) (a : A) (ha : a ∈ J) :
    f.gnsStarAlgHom a = 0 := by
  apply DFunLike.coe_injective
  apply (gnsVector_cyclic f).equalizer ((f.gnsStarAlgHom a).continuous) (by fun_prop)
  funext b
  change f.gnsStarAlgHom a (f.gnsStarAlgHom b (gnsVector f)) = 0
  rw [← mul_apply_eq_comp,← map_mul]
  exact gns_vector_zero_of_square_zero f (a*b) (hf _ (J.mul_mem_right a b ha))

end

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open Topology

open scoped CStarAlgebra ComplexOrder

open Topology

open Topology

open Topology

open Filter Topology
open scoped InnerProductSpace ComplexOrder ComplexStarModule CStarAlgebra

open Topology

open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Omission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology
section
universe u v
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A]

lemma generatedFamily_reindex {J : Type u} {K : Type v}
    (base : Set A) (z : K → A) (e : J → K) (S : Set J) :
    generatedFamily base (z ∘ e) S = generatedFamily base z (e '' S) := by
  unfold generatedFamily
  rw [Set.image_image]
  rfl

end

open Cardinal Topology TopologicalSpace

open Cardinal Topology TopologicalSpace

end NaimarkZFC

end

end OAI
end


