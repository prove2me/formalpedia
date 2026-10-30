-- Prove2me | Definitions.Def_OAIQ115N011
-- name    : OAIQ115N011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T00:37:24.651082+00:00
-- url     : https://prove2.me/theorems/f63a4139-fd81-4ff1-bf75-dac43f0a7754
-- title:
--   Definitions bundle OAIQ115N011 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 1 definition and 47 theorems. The definitions and types are `OAI.NaimarkZFC.KOS.matrixConst`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_Amalgamation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Amalgamation.lean), [`Naimark_Operators`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Operators.lean), [`Naimark_Representations`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Representations.lean).
--
--   **Imports.** It imports the published bundle `Def_Naimark`; the bundles `OAIQ115N007`, `OAIQ115N008` and `OAIQ115N009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N012` and `OAIQ115N013`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark
import Definitions.Def_OAIQ115N007
import Definitions.Def_OAIQ115N008
import Definitions.Def_OAIQ115N009

section
-- module Solutions.OAIQ115_Naimark.Naimark_Representations
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.constructionIndex_nonempty _root_.OAI.NaimarkZFC.omittedAlgebra_isClosed _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_isClosed
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

variable {ι : Type*} [Fintype ι]

open scoped ComplexStarModule CStarAlgebra
variable {A : Type*} [CStarAlgebra A]

open scoped InnerProductSpace ComplexStarModule
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule
open Filter Topology
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule CStarAlgebra
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_unitary_vector
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ η : H) (heq : ‖ξ‖ = ‖η‖) :
    ∃ u : unitary A, π u ξ = η := by
  by_cases h : ξ = η
  · refine ⟨1, ?_⟩
    simpa only [OneMemClass.coe_one, irreducible_map_one π hπ, one_apply_eq_self] using h
  have hd : ξ - η ≠ 0 := sub_ne_zero.mpr h
  have hi : (⟪ξ - η, Complex.I • (ξ + η)⟫_ℂ).im = 0 := by
    rw [inner_smul_right, inner_sub_left, inner_add_right, inner_add_right]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add,
      Complex.sub_re, Complex.add_re, inner_self_eq_norm_sq_to_K]
    have hh := inner_re_symm (𝕜 := ℂ) ξ η
    change (⟪ξ, η⟫_ℂ).re = (⟪η, ξ⟫_ℂ).re at hh
    rw [hh, heq]
    ring
  obtain ⟨a, ha, hact⟩ := irreducible_selfAdjoint_vector π hπ
    (ξ - η) (Complex.I • (ξ + η)) hd hi
  have hre : π (a - Complex.I • (1 : A)) ξ =
      π (a - (-Complex.I) • (1 : A)) η := by
    simp only [map_sub, map_smul, sub_apply, smul_apply,
      irreducible_map_one π hπ, one_apply_eq_self]
    simp only [map_sub, smul_add] at hact
    rw [neg_smul]
    apply sub_eq_iff_eq_add.mpr
    rw [sub_neg_eq_add]
    have hh := sub_eq_iff_eq_add.mp hact
    rw [hh]
    abel
  refine ⟨⟨saCayley a, saCayley_unitary a ha⟩, ?_⟩
  change π (saCayley a) ξ = η
  rw [saCayley_eq a ha, map_mul, mul_apply_eq_comp, hre, ← mul_apply_eq_comp, ← map_mul]
  rw [← Algebra.algebraMap_eq_smul_one, (saResolvent_inverse a ha (-Complex.I) (by simp)).2,
    irreducible_map_one π hπ, one_apply_eq_self]

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
universe u v w

variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

variable [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in

theorem equivalent_vector_states_unitary
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K))
    (he : UnitarilyEquivalent π ρ) (ξ : H) (η : K)
    (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) :
    ∃ u : unitary A, ∀ a : A,
      ⟪η, ρ a η⟫_ℂ = ⟪ξ, π (star (u : A) * a * (u : A)) ξ⟫_ℂ := by
  obtain ⟨U, hU⟩ := he
  obtain ⟨u, hu⟩ := irreducible_unitary_vector π hπ ξ (U.symm η)
    (by rw [hξ, U.symm.norm_map, hη])
  refine ⟨u, fun a => ?_⟩
  calc
    ⟪η, ρ a η⟫_ℂ = ⟪U (π u ξ), ρ a (U (π u ξ))⟫_ℂ := by rw [hu, U.apply_symm_apply]
    _ = ⟪U (π u ξ), U (π a (π u ξ))⟫_ℂ :=
      congrArg (fun z => ⟪U (π u ξ), z⟫_ℂ) (hU a (π u ξ)).symm
    _ = ⟪π u ξ, π a (π u ξ)⟫_ℂ := U.inner_map_map _ _
    _ = _ := by
      simp only [map_mul, map_star, mul_apply_eq_comp,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

open scoped InnerProductSpace ComplexStarModule
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped CStarAlgebra InnerProductSpace ComplexStarModule
open Filter Topology
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [PartialOrder A] [StarOrderedRing A]

open scoped InnerProductSpace ComplexStarModule CStarAlgebra
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_vector_excision
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1) (a : A) :
    Tendsto (fun e : vectorNullAlgebra π ξ =>
      (1 - (e : A)) * (a - ⟪ξ, π a ξ⟫_ℂ • (1 : A)) * (1 - (e : A)))
      (CStarAlgebra.approximateUnit (vectorNullAlgebra π ξ)) (𝓝 0) := by
  let a₀ := a - ⟪ξ, π a ξ⟫_ℂ • (1 : A)
  have ha₀ : ⟪ξ, π a₀ ξ⟫_ℂ = 0 := by
    simp [a₀, map_sub, map_smul, sub_apply, smul_apply, irreducible_map_one π hπ,
      one_apply_eq_self, inner_self_eq_norm_sq_to_K, hξ]
  obtain ⟨b, c, hb, hc, hbc⟩ := irreducible_null_decomposition π hπ ξ hξ a₀ ha₀
  have hbL := vectorNull_approximateUnit_annihilates π ξ hb
  have hcL := vectorNull_approximateUnit_annihilates π ξ hc
  have hnL : Tendsto (fun e : vectorNullAlgebra π ξ =>
      ‖b * (1 - (e : A))‖ + ‖c * (1 - (e : A))‖)
      (CStarAlgebra.approximateUnit (vectorNullAlgebra π ξ)) (𝓝 0) := by
    simpa only [norm_zero, zero_add] using hbL.norm.add hcL.norm
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hnL
  filter_upwards [vectorNull_complement_properties π (irreducible_map_one π hπ) ξ]
    with e he
  let x : A := 1 - (e : A)
  have hx : IsSelfAdjoint x := IsSelfAdjoint.of_nonneg he.1
  have hxn : ‖x‖ ≤ 1 := he.2.1
  change ‖x * a₀ * x‖ ≤ ‖b * x‖ + ‖c * x‖
  rw [hbc, mul_add, add_mul]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · calc
      _ = ‖x * (b * x)‖ := by rw [mul_assoc]
      _ ≤ ‖x‖ * ‖b * x‖ := norm_mul_le _ _
      _ ≤ 1 * ‖b * x‖ := by gcongr
      _ = _ := one_mul _
  · calc
      _ ≤ ‖x * star c‖ * ‖x‖ := norm_mul_le _ _
      _ ≤ ‖x * star c‖ * 1 := by gcongr
      _ = ‖c * x‖ := by rw [mul_one, ← norm_star (c * x), star_mul, hx.star_eq]

open scoped InnerProductSpace ComplexStarModule
open Filter Topology
variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma pureExcisionNet_excision (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1) (a : A) :
    Tendsto (fun e => pureExcisionNet π ξ e * (a - ⟪ξ, π a ξ⟫_ℂ • (1 : A)) *
      pureExcisionNet π ξ e) atTop (𝓝 0) :=
  (irreducible_vector_excision π hπ ξ hξ a).comp ExcisionIndex.tendsto_coe

theorem pureExcisionNet_cross
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hρ : IsIrreducible ρ)
    (η : K) (hη : ‖η‖ = 1) (hne : ¬ UnitarilyEquivalent π ρ) (a : A) :
    Tendsto (fun ij : ExcisionIndex (vectorNullAlgebra π ξ) ×
        ExcisionIndex (vectorNullAlgebra ρ η) =>
      pureExcisionNet π ξ ij.1 * a * pureExcisionNet ρ η ij.2) atTop (𝓝 0) := by
  apply cross_excision_tendsto (pureExcisionNet π ξ) (pureExcisionNet ρ η)
    (fun b => ⟪ξ, π b ξ⟫_ℂ) (pureExcisionNet_nonneg π ξ) (pureExcisionNet_norm π ξ)
    (pureExcisionNet_nonneg ρ η) (pureExcisionNet_norm ρ η) (pureExcisionNet_antitone ρ η)
    (pureExcisionNet_excision π hπ ξ hξ) a
  have hs := pureExcisionNet_inequivalent_strong ρ hρ η hη π hπ
    (fun h => hne h.symm) (π (star a) ξ)
  have ht := Filter.Tendsto.inner (𝕜 := ℂ)
    (tendsto_const_nhds (x := π (star a) ξ)) hs
  simpa only [map_mul, map_star, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
    inner_zero_right] using ht

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

open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology
open scoped ComplexOrder

open Filter Topology
open scoped ComplexOrder ComplexStarModule OnePoint InnerProductSpace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (hp0 : p 0 = 1)
variable (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ n, 0 < (τ (peakAtom p n)).re)

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {ι : Type*} {l : Filter ι}

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma irreducible_small_projection_value_one
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (τ : A →L[ℂ] ℂ) (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (p : A) (hp : IsStarProjection p) (hne : π p ≠ 0) :
    ∃ q : A, IsStarProjection q ∧ ⟪ξ, π q ξ⟫_ℂ = 1 ∧ τ q = τ p := by
  obtain ⟨η, hη, hpη⟩ := projection_exists_unit_fixed (hp.map π) hne
  obtain ⟨u, hu⟩ := irreducible_unitary_vector π hπ ξ η (hξ.trans hη.symm)
  let q : A := (Unitary.conjStarAlgAut ℂ A u).symm p
  refine ⟨q, hp.map _, ?_, ?_⟩
  · change ⟪ξ, π (star (u : A) * p * (u : A)) ξ⟫_ℂ = 1
    rw [map_mul, map_mul, map_star, mul_apply_eq_comp, mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
      hu, hpη, inner_self_eq_norm_sq_to_K, hη]
    norm_num
  · change τ (star (u : A) * p * (u : A)) = τ p
    rw [htr _ (u : A), ← mul_assoc, u.property.2, one_mul]

theorem pureExcisionNet_trace_null
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ p : A, IsStarProjection p ∧ π p ≠ 0 ∧ (τ p).re < ε) :
    Tendsto (fun i => τ (pureExcisionNet π ξ i)) atTop (𝓝 0) := by
  apply excision_trace_null_of_small_projections (pureExcisionNet π ξ)
    (fun a => ⟪ξ, π a ξ⟫_ℂ) (pureExcisionNet_nonneg π ξ) (pureExcisionNet_norm π ξ)
    (pureExcisionNet_excision π hπ ξ hξ) τ hτ htr
  intro ε hε
  obtain ⟨p, hp, hpne, hpt⟩ := hsmall ε hε
  obtain ⟨q, hq, hqv, hqt⟩ := irreducible_small_projection_value_one π hπ ξ hξ τ htr p hp hpne
  exact ⟨q, hq, hqv, hqt ▸ hpt⟩

open Filter Topology
open scoped ComplexOrder ComplexStarModule InnerProductSpace

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

open Filter Topology
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology
open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

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

section
open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]
variable (π : ∀ i r, A i →⋆ₐ[ℂ]
  (ℓ²(ColumnIndex L i r, ℂ) →L[ℂ] ℓ²(ColumnIndex L i r, ℂ)))

theorem atomicFock_creation_norm (i : I) (a : A i) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ r, ‖π i r a (lp.single 2 none 1)‖ ≤ C)
    (x : AtomicFockSpace L) (hx : FockAway L i x) :
    ‖atomicFockRepresentation L π i a x‖ ≤ C * ‖x‖ := by
  classical
  let U := fockBlockUnitary L i
  rw [← U.symm.norm_map (atomicFockRepresentation L π i a x)]
  calc
    ‖U.symm (atomicFockRepresentation L π i a x)‖ ≤ ‖C • U.symm x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro t
      have hb : U.symm (atomicFockRepresentation L π i a x) t =
          x t.1 • π i t.1.2.1 a (lp.single 2 none 1) := by
        ext c
        change (fockBlockUnitary L i).symm _ t c = _
        rw [fockBlockUnitary_symm_apply, atomicFock_creation L π i a x hx]
        rfl
      rw [hb, norm_smul]
      change _ ≤ ‖C • ((fockBlockUnitary L i).symm x t)‖
      rw [fockBlockUnitary_symm_away L i x hx, norm_smul,
        lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞)), Real.norm_eq_abs, abs_of_nonneg hC]
      simpa only [mul_comm C] using mul_le_mul_of_nonneg_left (ha t.1.2.1) (norm_nonneg _)
    _ = C * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC, U.symm.norm_map]

end

section
open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

theorem fockStartProjection_complement_away (i : I) (x : AtomicFockSpace L) :
    FockAway L i ((1 - fockStartProjection L i) x) := by
  intro j hj
  simp [hj]

theorem fockStartProjection_starts (i : I) (x : AtomicFockSpace L) :
    FockStarts L i (fockStartProjection L i x) := by
  intro j hj
  simp [hj]

theorem fockStartProjection_fix (i : I) (x : AtomicFockSpace L)
    (hx : FockStarts L i x) : fockStartProjection L i x = x := by
  ext j
  rw [fockStartProjection_apply]
  split_ifs with hj
  · rfl
  · exact (hx j hj).symm

end

open scoped InnerProductSpace lp
variable {V J : Type*}

section
open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]
  {A : I → Type*} [∀ i, CStarAlgebra (A i)]
variable (π : ∀ i r, A i →⋆ₐ[ℂ]
  (ℓ²(ColumnIndex L i r, ℂ) →L[ℂ] ℓ²(ColumnIndex L i r, ℂ)))

theorem atomicFock_zero_column (i : I) (a : A i)
    (ha : atomicFockRepresentation L π i a = 0) (r : V) :
    π i r a (lp.single 2 none 1) = 0 := by
  classical
  let x : AtomicFockSpace L := lp.single 2 ⟨none, r, .nil r⟩ 1
  have hx : FockAway L i x := by
    intro j hj
    have hn : j ≠ ⟨none, r, .nil r⟩ := by
      intro he
      have hf := congrArg (fun j : FockIndex L => j.1) he
      change j.1 = none at hf
      rw [hj] at hf
      cases hf
    simp only [x, lp.single_apply, Pi.single_eq_of_ne hn]
  let t : FockTail L i := ⟨⟨none, r, .nil r⟩, by simp⟩
  ext c
  have hb := atomicFock_creation L π i a x hx t c
  rw [ha] at hb
  simpa [x, t, fockVacuumIndex, zero_apply] using hb.symm

end

open scoped InnerProductSpace ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem operatorVectorFunctional_faithful (B : StarSubalgebra ℂ (H →L[ℂ] H))
    (ξ : H) (hcyc : DenseRange (fun T : B => (T : H →L[ℂ] H) ξ))
    (htr : ∀ S T : B, operatorVectorFunctional ξ ((S : H →L[ℂ] H) * T) =
      operatorVectorFunctional ξ ((T : H →L[ℂ] H) * S))
    (S : B) (hS : operatorVectorFunctional ξ (star (S : H →L[ℂ] H) * S) = 0) : S = 0 := by
  have hz : ∀ T : B, (T : H →L[ℂ] H) ξ = 0 → (star (T : H →L[ℂ] H)) ξ = 0 := by
    intro T hT
    have ht := htr (star T) T
    simp only [StarMemClass.coe_star] at ht
    rw [operatorVectorFunctional_star_mul] at ht
    have hstar := operatorVectorFunctional_star_mul ξ (star (T : H →L[ℂ] H))
    simp only [star_star] at hstar
    rw [hstar, hT, norm_zero, zero_pow (by decide)] at ht
    exact norm_eq_zero.mp (by have hh := congrArg Complex.re ht; simp only [Complex.ofReal_re] at hh; nlinarith [norm_nonneg ((star (T : H →L[ℂ] H)) ξ)])
  have ha : (S : H →L[ℂ] H) ξ = 0 := by
    rw [operatorVectorFunctional_star_mul] at hS
    have hh := congrArg Complex.re hS
    simp only [Complex.ofReal_re, Complex.zero_re] at hh
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg ((S : H →L[ℂ] H) ξ)])
  have hs := hz S ha
  have he : ∀ T : B, (S : H →L[ℂ] H) ((T : H →L[ℂ] H) ξ) = 0 := by
    intro T
    have hh : ((star (S * T) : B) : H →L[ℂ] H) ξ = 0 := by
      simp [star_mul, hs]
    have h := hz (star (S * T)) hh
    simpa using h
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact hcyc.induction_on x (isClosed_eq S.1.continuous continuous_const) he

section
open scoped InnerProductSpace lp

variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V)

variable [DecidableEq I]

theorem atomicLeft_away_norm (i : I) (a : A i) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ r, ((d i).trace (((d i).atom r).1 * (star a * a) * ((d i).atom r).1)).re ≤
      C ^ 2 * ((d i).trace ((d i).atom r).1).re)
    (x : AtomicHilbertSpace d) (hx : FockAway (AtomicLetters d) i x) :
    ‖atomicLeft d i a x‖ ≤ C * ‖x‖ := by
  apply atomicFock_creation_norm (AtomicLetters d) (atomicColumnReps d) i a C hC _ x hx
  intro r
  apply (sq_le_sq₀ (norm_nonneg _) hC).mp
  rw [atomicColumnReps, indexedColumnRepresentation_vacuum_norm]
  exact (div_le_iff₀ ((d i).positive r)).mpr (ha r)

theorem atomicLeft_injective (i : I) : Function.Injective (atomicLeft d i) := by
  classical
  have hk : ∀ a : A i, atomicLeft d i a = 0 → a = 0 := by
    intro a ha
    let τ := (d i).trace
    have hx : (τ.toPreGNS a : τ.GNS) = 0 := by
      apply traceRightAtoms_jointKernel τ (d i).tracial (d i).atom
        (d i).orthogonal (d i).mass
      intro r
      let : ∀ l, DecidableEq (AtomicLetters d i l r) := fun _ => Classical.decEq _
      have hc := atomicFock_zero_column (AtomicLetters d) (atomicColumnReps d) i a ha r
      change indexedColumnRepresentation (d i).trace (d i).tracial (d i).atom
        (d i).orthogonal (d i).mass (d i).positive r a (lp.single 2 none 1) = 0 at hc
      let basis := tracialColumnBasis (d i).trace (d i).tracial (d i).atom
        (d i).orthogonal (d i).mass (d i).positive r
      have vector_zero :=
        (indexedColumnRepresentation_vacuum_vector (d i).trace (d i).tracial (d i).atom
          (d i).orthogonal (d i).mass (d i).positive r a).symm.trans hc
      have hv : traceColumnRepresentation (d i).trace (d i).tracial ((d i).atom r)
          a (columnUnit (d i).trace (d i).tracial ((d i).atom r)) = 0 :=
        basis.repr.injective (vector_zero.trans (map_zero basis.repr).symm)
      rw [columnUnit, map_smul] at hv
      have hn : (((Real.sqrt (τ ((d i).atom r).1).re)⁻¹ : ℂ)) ≠ 0 := by
        exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ((d i).positive r)).ne')
      have hv' := (smul_eq_zero.mp hv).resolve_left hn
      have hv'' := congrArg Subtype.val hv'
      rw [columnVacuum_action] at hv''
      simpa [gnsRight_coe, τ] using hv''
    apply (d i).faithful a
    have hh : inner ℂ (τ.toPreGNS a : τ.GNS) (τ.toPreGNS a : τ.GNS) = 0 := by simp [hx]
    simpa only [Completion.inner_coe, PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS] using hh
  intro a b hab
  apply sub_eq_zero.mp
  apply hk
  rw [map_sub, hab, sub_self]

end

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]

open Filter Topology
open scoped lp
variable {J V : Type*} [DecidableEq V]

variable [DecidableEq J]

section
open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

theorem fock_single_away (i : I) (t : FockTail L i) :
    FockAway L i (lp.single 2 t.1 1) := by
  classical
  intro j hj
  have hne : j ≠ t.1 := by
    rintro rfl
    exact t.2 hj
  simp [lp.single_apply, hne]

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]
variable (π : ∀ i r, A i →⋆ₐ[ℂ]
  (ℓ²(ColumnIndex L i r, ℂ) →L[ℂ] ℓ²(ColumnIndex L i r, ℂ)))

theorem fockColumn_action (i : I) (t : FockTail L i) (a : A i) :
    atomicFockRepresentation L π i a (lp.single 2 t.1 1) =
      l2Embed (fockColumnIndexEmbedding L i t) (π i t.1.2.1 a (lp.single 2 none 1)) := by
  classical
  ext j
  obtain ⟨⟨u,c⟩, rfl⟩ := (fockBlockEquiv L i).surjective j
  change atomicFockRepresentation L π i a (lp.single 2 t.1 1)
    (fockJoin L i ⟨u,c⟩) =
      l2Embed (fockColumnIndexEmbedding L i t)
        (π i t.1.2.1 a (lp.single 2 none 1)) (fockJoin L i ⟨u,c⟩)
  rw [atomicFock_creation L π i a _ (fock_single_away L i t) u c]
  by_cases hu : u = t
  · subst u
    change _ = l2Embed (fockColumnIndexEmbedding L i t) _
      (fockColumnIndexEmbedding L i t c)
    rw [l2Embed_apply]
    simp
  · rw [l2Embed_apply_of_not_mem _ _ _ (fockColumnIndexEmbedding_ne L t u hu c)]
    have hne : u.1 ≠ t.1 := fun h => hu (Subtype.ext h)
    simp [lp.single_apply, hne]

theorem fock_cyclic_total
    (hcol : ∀ i r, DenseRange (fun a : A i => π i r a (lp.single 2 none 1)))
    (C : Submodule ℂ (AtomicFockSpace L)) (hC : IsClosed (C : Set (AtomicFockSpace L)))
    (hinv : ∀ i (a : A i) x, x ∈ C → atomicFockRepresentation L π i a x ∈ C)
    (hvac : ∀ r, lp.single 2 (fockVacuumIndex L r) 1 ∈ C) : C = ⊤ := by
  classical
  have hblock (i : I) (t : FockTail L i) (ht : lp.single 2 t.1 1 ∈ C)
      (z : ℓ²(ColumnIndex L i t.1.2.1, ℂ)) :
      l2Embed (fockColumnIndexEmbedding L i t) z ∈ C := by
    refine (hcol i t.1.2.1).induction_on
      (p := fun z => l2Embed (fockColumnIndexEmbedding L i t) z ∈ C) z ?_ ?_
    · exact hC.preimage (l2Embed (fockColumnIndexEmbedding L i t)).continuous
    intro a
    rw [← fockColumn_action L π i t a]
    exact hinv i a _ ht
  have hsingle (j : FockIndex L) : lp.single 2 j 1 ∈ C := by
    rcases j with ⟨i,l,p⟩
    induction p with
    | nil r => exact hvac r
    | cons i l r a j p hn ih =>
      let t : FockTail L i := ⟨⟨j,r,p⟩, hn.symm⟩
      have hh := hblock i t ih (lp.single 2 (some ⟨l,a⟩) 1)
      rw [l2Embed_single] at hh
      exact hh
  apply top_unique
  rw [← (l2Basis (FockIndex L)).dense_span]
  have hh : Submodule.span ℂ (Set.range (l2Basis (FockIndex L))) ≤ C := by
    apply Submodule.span_le.mpr
    rintro x ⟨j,rfl⟩
    rw [l2Basis_apply]
    exact hsingle j
  exact (Submodule.topologicalClosure_mono hh).trans_eq hC.submodule_topologicalClosure_eq

end

section
open Filter Topology
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I]

omit [DecidableEq I] in

theorem atomicColumnReps_cyclic (i : I) (r : V) :
    DenseRange (fun a : A i => atomicColumnReps d i r a (lp.single 2 none 1)) := by
  let b := tracialColumnBasis (d i).trace (d i).tracial (d i).atom
    (d i).orthogonal (d i).mass (d i).positive r
  have hd := b.repr.surjective.denseRange.comp
    (traceColumn_unit_cyclic (d i).trace (d i).tracial ((d i).atom r) ((d i).positive r))
    b.repr.continuous
  have functions_eq : (fun a : A i => atomicColumnReps d i r a (lp.single 2 none 1)) =
      fun a => b.repr (traceColumnRepresentation (d i).trace (d i).tracial
        ((d i).atom r) a (columnUnit (d i).trace (d i).tracial ((d i).atom r))) :=
    funext (indexedColumnRepresentation_vacuum_vector (d i).trace (d i).tracial
      (d i).atom (d i).orthogonal (d i).mass (d i).positive r)
  rw [functions_eq]
  exact hd

theorem atomicCommonAtom_vacuum (k : I) (r : V) :
    atomicCommonAtom d k r (atomicVacuum d k) =
      (Real.sqrt (((d k).trace ((d k).atom r).1).re) : ℂ) •
        lp.single 2 (fockVacuumIndex (AtomicLetters d) r) 1 := by
  classical
  ext j
  rw [atomicCommonAtom_apply]
  rcases j with ⟨i,l,p⟩
  cases p with
  | nil l =>
    simp only [atomicVacuum, fockVacuum_apply_nil, atomicWeightVector_apply,
      lp.coeFn_smul, Pi.smul_apply, lp.single_apply]
    by_cases h : r = l
    · subst l
      change _ = (Real.sqrt (((d k).trace ((d k).atom r).1).re) : ℂ) *
        (Pi.single (fockVacuumIndex (AtomicLetters d) r) (1 : ℂ) :
          FockIndex (AtomicLetters d) → ℂ) (fockVacuumIndex (AtomicLetters d) r)
      rw [Pi.single_eq_same, mul_one, ite_eq_left rfl]
    · have hn : (⟨none,l,ReducedPath.nil l⟩ : FockIndex (AtomicLetters d)) ≠
          fockVacuumIndex (AtomicLetters d) r := by
        intro he
        exact h (congrArg (fun j : FockIndex (AtomicLetters d) => j.2.1) he).symm
      simp only [ite_eq_right h, Pi.single_eq_of_ne hn, smul_zero]
  | cons i l t a j p hn =>
    have hz : atomicVacuum d k ⟨some i,l,.cons i l t a j p hn⟩ = 0 :=
      fockVacuum_away (AtomicLetters d) _ i _ rfl
    have hne : (⟨some i,l,ReducedPath.cons i l t a j p hn⟩ : FockIndex (AtomicLetters d)) ≠
        fockVacuumIndex (AtomicLetters d) r := by
      intro h
      have hh := congrArg (fun j : FockIndex (AtomicLetters d) => j.1) h
      cases hh
    simp only [hz, ite_self, lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_eq_of_ne hne, smul_zero]

theorem atomicAlgebra_cyclic (k : I) : DenseRange (atomicEval d k) := by
  let M := LinearMap.range (atomicEval d k)
  let C := M.topologicalClosure
  have hclosed : IsClosed (C : Set (AtomicHilbertSpace d)) := isClosed_closure
  have hinv (i : I) (a : A i) (x : AtomicHilbertSpace d) (hx : x ∈ C) :
      atomicLeft d i a x ∈ C := by
    apply map_mem_closure (atomicLeft d i a).continuous hx
    rintro y ⟨T,rfl⟩
    exact ⟨⟨atomicLeft d i a * T.1,
      (atomicAlgebra d).mul_mem (atomicLeft_mem_algebra d i a) T.2⟩, rfl⟩
  have hvac (r : V) : lp.single 2 (fockVacuumIndex (AtomicLetters d) r) 1 ∈ C := by
    have he : atomicCommonAtom d k r (atomicVacuum d k) ∈ M :=
      ⟨⟨atomicCommonAtom d k r, atomicLeft_mem_algebra d k ((d k).atom r).1⟩, rfl⟩
    rw [atomicCommonAtom_vacuum] at he
    have hn : (Real.sqrt (((d k).trace ((d k).atom r).1).re) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ((d k).positive r)).ne'
    exact M.le_topologicalClosure ((M.smul_mem_iff (s :=
      (Real.sqrt (((d k).trace ((d k).atom r).1).re) : ℂ)) hn).mp he)
  have htotal : C = ⊤ := fock_cyclic_total (AtomicLetters d) (atomicColumnReps d)
    (atomicColumnReps_cyclic d) C hclosed hinv hvac
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr htotal

theorem atomicCStar_cyclic (k : I) :
    DenseRange (fun T : AtomicCStar d => (T : AtomicOperators d) (atomicVacuum d k)) := by
  apply (atomicAlgebra_cyclic d k).mono
  rintro x ⟨T,rfl⟩
  exact ⟨⟨T.1,subset_closure T.2⟩,rfl⟩

end

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem operatorCompression_norm_le (M : Submodule ℂ H) [CompleteSpace M]
    (T : H →L[ℂ] H) : ‖operatorCompression M T‖ ≤ ‖T‖ := by
  apply (operatorCompression M T).opNorm_le_bound (norm_nonneg T)
  intro x
  exact (M.norm_orthogonalProjectionOnto_apply_le _).trans (T.le_opNorm (x : H))

variable [CompleteSpace H]

variable {A : Type*} [CStarAlgebra A]

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : Type*} [CStarAlgebra A]

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (B : StarSubalgebra ℂ (H →L[ℂ] H))
variable {I : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
variable (ι : ∀ i, A i →⋆ₐ[ℂ] B) (ξ : H)

theorem factorCompression_norm_le (i : I) (b : B) :
    ‖factorCompression B ι ξ i b‖ ≤ ‖b‖ := by
  change ‖operatorCompression (cyclicSpan (ambientFactor B ι i) ξ) (b : H →L[ℂ] H)‖ ≤ ‖(b : H →L[ℂ] H)‖
  exact operatorCompression_norm_le _ (b : H →L[ℂ] H)

theorem factorCompression_mul_factor (i : I) (b : B) (a : A i) :
    factorCompression B ι ξ i (b * ι i a) =
      factorCompression B ι ξ i b * cyclicRepresentation (ambientFactor B ι i) ξ a := by
  ext x
  rfl

theorem factorCompression_factor_mul (i : I) (a : A i) (b : B) :
    factorCompression B ι ξ i (ι i a * b) =
      cyclicRepresentation (ambientFactor B ι i) ξ a * factorCompression B ι ξ i b := by
  apply star_injective
  rw [← factorCompression_star, star_mul, ← map_star, factorCompression_mul_factor,
    map_star (cyclicRepresentation (ambientFactor B ι i) ξ), factorCompression_star]
  exact (star_mul (cyclicRepresentation (ambientFactor B ι i) ξ a)
    (factorCompression B ι ξ i b)).symm

theorem factorCompression_vector (i : I) (b : B) :
    inner ℂ (⟨ξ,cyclicSpan_vector_mem (ambientFactor B ι i) ξ⟩ : cyclicSpan (ambientFactor B ι i) ξ)
      (factorCompression B ι ξ i b ⟨ξ,cyclicSpan_vector_mem (ambientFactor B ι i) ξ⟩) =
      restrictedVectorFunctional B ξ b := by
  change inner ℂ _ (operatorCompression (cyclicSpan (ambientFactor B ι i) ξ) (b : H →L[ℂ] H) _) =
    inner ℂ ξ ((b : H →L[ℂ] H) ξ)
  exact operatorCompression_inner (cyclicSpan (ambientFactor B ι i) ξ) (b : H →L[ℂ] H) _ _

end

open scoped CStarAlgebra

section
open scoped InnerProductSpace ComplexOrder CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem operatorCompression_nonneg (M : Submodule ℂ H) [CompleteSpace M]
    (T : H →L[ℂ] H) (hT : 0 ≤ T) : 0 ≤ operatorCompression M T := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  apply (ContinuousLinearMap.isPositive_iff' _).mpr
  refine ⟨?_, fun x => ?_⟩
  · change star (operatorCompression M T) = operatorCompression M T
    rw [← operatorCompression_star, (IsSelfAdjoint.of_nonneg hT).star_eq]
  · rw [← inner_conj_symm, operatorCompression_inner]
    exact star_nonneg_iff.mpr ((ContinuousLinearMap.nonneg_iff_isPositive (f := T)).mp hT |>.inner_nonneg_right x)

end

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
-- module Solutions.OAIQ115_Naimark.Naimark_Operators
attribute [-instance] _root_.OAI.NaimarkZFC.constructionIndex_nonempty _root_.OAI.NaimarkZFC.omittedAlgebra_isClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped BigOperators InnerProductSpace ComplexOrder
open Filter Topology
namespace KOS
variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]
variable {ι : Type*} [fintypeι : Fintype ι] [decidableEqι : DecidableEq ι]

def matrixConst (a : A) : CStarMatrix ι ι A :=
  matrixDiagonalHom (fun _ => StarAlgHom.id ℂ A) (fun _ => a)

omit partialOrderA starOrderedRingA in
@[simp] lemma matrixConst_apply [PartialOrder A] [StarOrderedRing A] (a : A) (i j : ι) :
    matrixConst (ι:=ι) a i j = if i=j then a else 0 := by simp [matrixConst]

lemma matrixConst_norm (a : A) : ‖matrixConst (ι:=ι) a‖ ≤ ‖a‖ := by
  exact (NonUnitalStarAlgHom.norm_apply_le
    (matrixDiagonalHom (fun _ : ι => StarAlgHom.id ℂ A)) (fun _ => a)).trans (pi_norm_le_iff_of_nonneg (norm_nonneg a) |>.mpr (fun _ => le_rfl))

@[simp] lemma matrixConst_star (a : A) : star (matrixConst (ι:=ι) a) = matrixConst (star a) := by
  ext i j
  simp only [CStarMatrix.star_apply,matrixConst_apply,apply_ite star,star_zero]
  split_ifs <;> simp_all

omit partialOrderA starOrderedRingA in
@[simp] lemma matrixConst_mul [PartialOrder A] [StarOrderedRing A] (a b : A) : matrixConst (ι:=ι) a*matrixConst (ι:=ι) b=matrixConst (ι:=ι) (a*b) := by
  exact (map_mul (matrixDiagonalHom (fun _ : ι => StarAlgHom.id ℂ A)) (fun _ => a) (fun _ => b)).symm

lemma matrixRow_average (r : ι) (x : ι → A) (a : A) :
    (matrixRow r x*matrixConst (ι:=ι) a*star (matrixRow r x)) r r = rowAverage x a := by
  simp only [CStarMatrix.mul_apply,CStarMatrix.star_apply,matrixRow_apply,matrixConst_apply,ite_true, if_true]
  simp [rowAverage]

lemma matrixRow_average_norm (r : ι) (x : ι → A) (a : A) :
    ‖rowAverage x a‖ ≤ ‖matrixRow r x‖^2*‖a‖ := by
  rw [← matrixRow_average r x a]
  exact (CStarMatrix.norm_entry_le_norm).trans ((norm_mul_le _ _).trans
    ((mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left (matrixConst_norm a) (norm_nonneg _))) (norm_nonneg _)).trans_eq
      (by rw [norm_star]; ring)))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [completeSpaceH : CompleteSpace H]

lemma matrixScalar_mul_const (M : CStarMatrix ι ι ℂ) (a : A) (i j : ι) :
    (matrixScalar (A:=A) M*matrixConst (ι:=ι) a) i j = M i j • a := by
  simp only [CStarMatrix.mul_apply,matrixScalar_apply,matrixConst_apply,mul_ite,mul_zero]
  simp

lemma excision_matrix_gram_tendsto
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖=1) (r : ι) (c : ι → A) :
    Tendsto (fun e =>
      star (matrixRow r (fun i => c i*pureExcisionNet π ξ e)) *
        matrixRow r (fun i => c i*pureExcisionNet π ξ e) -
      matrixScalar (scalarGram (fun i => π (c i) ξ)) *
        matrixConst (pureExcisionNet π ξ e*pureExcisionNet π ξ e)) atTop (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hs : ⟪ξ,π (star (c i)*c j) ξ⟫_ℂ = ⟪π (c i) ξ,π (c j) ξ⟫_ℂ := by
    simp only [map_mul,map_star,mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
  have he := pureExcisionNet_excision π hπ ξ hξ (star (c i)*c j)
  convert he using 1
  · funext e
    simp only [CStarMatrix.sub_apply,matrixRow_gram,matrixScalar_mul_const,scalarGram,
      star_mul,
      (IsSelfAdjoint.of_nonneg (pureExcisionNet_nonneg π ξ e)).star_eq,hs]
    change _ - ⟪π (c i) ξ,π (c j) ξ⟫_ℂ • _ = _
    simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one,mul_assoc]
  · rfl

lemma excision_matrix_row_norm
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖=1) (r : ι) (c : ι → A) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ e in atTop,
      ‖matrixRow r (fun i => c i*pureExcisionNet π ξ e)‖ <
        ‖columnMap (fun i => π (c i) ξ)‖+δ := by
  have ht := (excision_matrix_gram_tendsto π hπ ξ hξ r c).norm
  have he := ht.eventually (gt_mem_nhds (by simpa using sq_pos_of_pos hδ))
  filter_upwards [he] with e he
  apply norm_lt_of_gram_approx _
    (matrixScalar (A:=A) (scalarGram (fun i => π (c i) ξ)))
    (matrixConst (pureExcisionNet π ξ e*pureExcisionNet π ξ e)) _ δ
    (norm_nonneg _) hδ ?_ ?_ he
  · apply (matrixConst_norm _).trans
    apply (norm_mul_le _ _).trans
    nlinarith [pureExcisionNet_norm π ξ e,norm_nonneg (pureExcisionNet π ξ e)]
  · exact (matrixScalar_norm _).trans_eq (scalarGram_norm _)

end KOS

open scoped InnerProductSpace BigOperators

open scoped BigOperators

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open scoped BigOperators InnerProductSpace

open scoped BigOperators
namespace KOS
variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixConst_mul_entry (b : A) (X : CStarMatrix ι ι A) (i j : ι) :
    (matrixConst (ι:=ι) b*X) i j = b*X i j := by
  simp only [CStarMatrix.mul_apply,matrixConst_apply,ite_mul,zero_mul]
  simp

lemma matrix_mulConst_entry (b : A) (X : CStarMatrix ι ι A) (i j : ι) :
    (X*matrixConst (ι:=ι) b) i j = X i j*b := by
  simp only [CStarMatrix.mul_apply,matrixConst_apply,mul_ite,mul_zero]
  simp

lemma scalar_const_commute (B : CStarMatrix ι ι ℂ) (a : A) :
    Commute (matrixScalar (A:=A) B) (matrixConst (ι:=ι) a) := by
  change matrixScalar (A:=A) B*matrixConst (ι:=ι) a = matrixConst a*matrixScalar B
  ext i j
  simp only [matrixConst_mul_entry,matrix_mulConst_entry,matrixScalar_apply,
    smul_mul_assoc,mul_smul_comm,mul_one,one_mul]

lemma matrixRow_defect (r : ι) (x : ι → A) (b e : A) (B : CStarMatrix ι ι ℂ) :
    matrixConst b*matrixRow r (fun i => x i*e) -
      matrixRow r (fun i => x i*e)*matrixScalar B =
    matrixRow r (fun j => (b*x j-∑ i, B i j • x i)*e) := by
  rw [matrixRow_mul_scalar]
  ext i j
  simp only [CStarMatrix.sub_apply,matrixConst_mul_entry,matrixRow_apply]
  split_ifs with h
  · simp only [sub_mul,Finset.sum_mul,smul_mul_assoc,mul_assoc]
  · simp

lemma rowAverage_commutator_norm (r : ι) (x : ι → A) (b e a : A)
    (hb : IsSelfAdjoint b) (B : CStarMatrix ι ι ℂ) (hB : IsSelfAdjoint B) :
    ‖b*rowAverage (fun i => x i*e) a-rowAverage (fun i => x i*e) a*b‖ ≤
      2*‖matrixRow r (fun j => (b*x j-∑ i, B i j • x i)*e)‖*
        ‖matrixRow r (fun i => x i*e)‖*‖a‖ := by
  let X := matrixRow r (fun i => x i*e)
  have hb' : IsSelfAdjoint (matrixConst (ι:=ι) b) := by
    change star _ = _
    rw [matrixConst_star,hb.star_eq]
  have hB' : IsSelfAdjoint (matrixScalar (A:=A) B) := hB.map _
  have hn := commutator_factorization_norm (matrixConst b) X (matrixConst a)
    (matrixScalar B) hb' hB' (scalar_const_commute B a)
  rw [matrixRow_defect] at hn
  have he : b*rowAverage (fun i => x i*e) a-rowAverage (fun i => x i*e) a*b =
      ((matrixConst (ι:=ι) b*(X*matrixConst a*star X)-(X*matrixConst a*star X)*matrixConst b) : CStarMatrix ι ι A) r r := by
    simp only [CStarMatrix.sub_apply,matrixConst_mul_entry,matrix_mulConst_entry,
      X,matrixRow_average]
  rw [he]
  exact CStarMatrix.norm_entry_le_norm.trans (hn.trans
    (mul_le_mul_of_nonneg_left (matrixConst_norm a) (by positivity)))

end KOS

open scoped InnerProductSpace BigOperators
open Filter Topology
namespace KOS
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma pureExcisionNet_strong
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖=1) (η : H) :
    Tendsto (fun e => π (pureExcisionNet π ξ e) η) atTop (𝓝 (⟪ξ,η⟫_ℂ • ξ)) := by
  have horth : ⟪ξ,η-⟪ξ,η⟫_ℂ • ξ⟫_ℂ = 0 := by
    simp [inner_self_eq_norm_sq_to_K,hξ]
  have ht := excision_orthogonal_strong π hπ ξ hξ (pureExcisionNet π ξ)
    (pureExcisionNet_nonneg π ξ) (pureExcisionNet_excision π hπ ξ hξ) _ horth
  have he (e : ExcisionIndex (vectorNullAlgebra π ξ)) :
      π (pureExcisionNet π ξ e) η = π (pureExcisionNet π ξ e) (η-⟪ξ,η⟫_ℂ • ξ) + ⟪ξ,η⟫_ℂ • ξ := by
    rw [map_sub,map_smul,pureExcisionNet_fixes π (irreducible_map_one π hπ) ξ]
    abel
  simpa only [he,zero_add] using ht.add_const (⟪ξ,η⟫_ℂ • ξ)

lemma pureExcisionNet_squared_strong
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖=1) (η : H) :
    Tendsto (fun e => π (pureExcisionNet π ξ e*pureExcisionNet π ξ e) η) atTop
      (𝓝 (⟪ξ,η⟫_ℂ • ξ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := ((pureExcisionNet_strong π hπ ξ hξ η).sub_const (⟪ξ,η⟫_ℂ • ξ)).norm
  apply squeeze_zero (fun _ => norm_nonneg _) ?_ (by simpa using ht)
  intro e
  have he : π (pureExcisionNet π ξ e*pureExcisionNet π ξ e) η-⟪ξ,η⟫_ℂ • ξ =
      π (pureExcisionNet π ξ e) (π (pureExcisionNet π ξ e) η-⟪ξ,η⟫_ℂ • ξ) := by
    simp only [map_mul,mul_apply_eq_comp,map_sub,map_smul,
      pureExcisionNet_fixes π (irreducible_map_one π hπ) ξ]
  rw [he]
  exact ((π (pureExcisionNet π ξ e)).le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _) ((NonUnitalStarAlgHom.norm_apply_le π _).trans
      (pureExcisionNet_norm π ξ e)))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma excision_rowAverage_vector_tendsto
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖=1) (c : ι → A) :
    Tendsto (fun e => π (rowAverage (fun i => c i*pureExcisionNet π ξ e) 1) ξ) atTop
      (𝓝 ((columnMap (fun i => π (c i) ξ))
        ((columnMap (fun i => π (c i) ξ)).adjoint ξ))) := by
  have hin (i : ι) : ⟪ξ,π (star (c i)) ξ⟫_ℂ = ⟪π (c i) ξ,ξ⟫_ℂ := by
    simp only [map_star,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  have ht (i : ι) := (π (c i)).continuous.tendsto _ |>.comp
    (pureExcisionNet_squared_strong π hπ ξ hξ (π (star (c i)) ξ))
  have hs := tendsto_finsetSum Finset.univ (fun i _ => ht i)
  convert hs using 1
  · funext e
    simp only [rowAverage,map_sum,sum_apply,star_mul,
      (IsSelfAdjoint.of_nonneg (pureExcisionNet_nonneg π ξ e)).star_eq,
      mul_one,mul_assoc,map_mul,mul_apply_eq_comp,Function.comp_def]
  · congr 1
    simp only [columnMap_apply,columnMap_adjoint_apply,hin,map_smul]

end KOS

open scoped BigOperators InnerProductSpace
open Filter Topology
namespace KOS
variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem approximate_matrix_rows_selfAdjoint
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖=1) (F : Finset A) (hF : ∀ b ∈ F, IsSelfAdjoint b)
    (δ : ℝ) (hδ : 0<δ) :
    ∃ (n : ℕ) (x : Fin n → A),
      (∀ a : A, ‖rowAverage x a‖ ≤ 4*‖a‖) ∧
      ‖π (rowAverage x 1) ξ-ξ‖ ≤ δ ∧
      ∀ b ∈ F, ∀ a : A, 0≤a → a≤1 → ‖b*rowAverage x a-rowAverage x a*b‖ ≤ δ := by
  classical
  let t : ℝ := min (1/2) (δ/8)
  have ht : 0<t := lt_min (by norm_num) (by positivity)
  have ht1 : t ≤ 1/2 := min_le_left _ _
  have htδ : 8*t ≤ δ := by have := min_le_right (1/2:ℝ) (δ/8); dsimp [t]; linarith
  obtain ⟨n,hn,w,B,hw,hfix,hcomm⟩ := finite_quasicentral_columns (F.image π)
    (by intro b hb; obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb; exact (hF a ha).map π)
    ξ hξ t ht
  choose v hv using fun i : Fin n => irreducible_vector_lift π hπ ξ hξ (w i)
  let r : Fin n := ⟨0,hn⟩
  have hfe := (excision_rowAverage_vector_tendsto π hπ ξ hξ v)
  simp only [hv,hfix] at hfe
  have hef : ∀ᶠ e in atTop,
      ‖π (rowAverage (fun i => v i*pureExcisionNet π ξ e) 1) ξ-ξ‖ < δ := by
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp hfe δ hδ)
  have her : ∀ᶠ e in atTop, ‖matrixRow r (fun i => v i*pureExcisionNet π ξ e)‖ < 2 := by
    filter_upwards [excision_matrix_row_norm π hπ ξ hξ r v t ht] with e he
    simp only [hv] at he
    linarith
  let d := fun b : A => fun j : Fin n => b*v j-∑ i, B (π b) i j • v i
  have hd (b : A) (j : Fin n) : π (d b j) ξ = π b (w j)-∑ i, B (π b) i j • w i := by
    simp only [d,map_sub,sub_apply,map_sum,sum_apply,map_smul,smul_apply,map_mul,mul_apply_eq_comp,hv]
  have heD : ∀ᶠ e in atTop, ∀ b ∈ F,
      ‖matrixRow r (fun j => d b j*pureExcisionNet π ξ e)‖ < 2*t := by
    apply F.eventually_all.mpr
    intro b hb
    have hcb := (hcomm (π b) (Finset.mem_image.mpr ⟨b,hb,rfl⟩)).2
    filter_upwards [excision_matrix_row_norm π hπ ξ hξ r (d b) t ht] with e he
    simp only [hd] at he
    linarith
  obtain ⟨e,hef,her,heD⟩ := (hef.and (her.and heD)).exists
  refine ⟨n,fun i => v i*pureExcisionNet π ξ e,?_,hef.le,?_⟩
  · intro a
    apply (matrixRow_average_norm r _ a).trans
    exact mul_le_mul_of_nonneg_right (by nlinarith [norm_nonneg (matrixRow r (fun i => v i*pureExcisionNet π ξ e))]) (norm_nonneg a)
  · intro b hb a ha ha1
    have hB := (hcomm (π b) (Finset.mem_image.mpr ⟨b,hb,rfl⟩)).1
    have han : ‖a‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg a ha).mpr ha1
    have hn := rowAverage_commutator_norm r v b (pureExcisionNet π ξ e) a (hF b hb) (B (π b)) hB
    have hDb := (heD b hb).le
    change ‖matrixRow r (fun j => (b*v j-∑ i, B (π b) i j • v i)*pureExcisionNet π ξ e)‖ ≤ 2*t at hDb
    apply hn.trans
    calc
      _ ≤ 2*(2*t)*2*1 := by gcongr
      _ ≤ δ := by linarith

end KOS

open scoped BigOperators InnerProductSpace ComplexStarModule
namespace KOS
variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma approximate_matrix_rows
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖=1) (F : Finset A) (δ : ℝ) (hδ : 0<δ) :
    ∃ (n : ℕ) (x : Fin n → A),
      (∀ a : A, ‖rowAverage x a‖ ≤ 4*‖a‖) ∧
      ‖π (rowAverage x 1) ξ-ξ‖ ≤ δ ∧
      ∀ b ∈ F, ∀ a : A, 0≤a → a≤1 → ‖b*rowAverage x a-rowAverage x a*b‖ ≤ δ := by
  classical
  let E := F.image (fun b => (realPart b:A)) ∪ F.image (fun b => (imaginaryPart b:A))
  have hE : ∀ b ∈ E, IsSelfAdjoint b := by
    intro b hb
    rcases Finset.mem_union.mp hb with hr|hi
    · obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hr
      exact (realPart a).property
    · obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hi
      exact (imaginaryPart a).property
  obtain ⟨n,x,hn,hfix,hcomm⟩ := approximate_matrix_rows_selfAdjoint π hπ ξ hξ E hE (δ/2) (by positivity)
  refine ⟨n,x,hn,by linarith,?_⟩
  intro b hb a ha ha1
  apply (commutator_real_imaginary_norm b (rowAverage x a)).trans
  have hr := hcomm (realPart b) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩)) a ha ha1
  have hi := hcomm (imaginaryPart b) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩)) a ha ha1
  linarith

end KOS

end NaimarkZFC

end

end OAI
end


