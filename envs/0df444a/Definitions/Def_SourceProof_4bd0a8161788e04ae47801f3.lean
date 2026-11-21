-- Prove2me | Definitions.Def_SourceProof_4bd0a8161788e04ae47801f3
-- name    : SourceProof_4bd0a8161788e04ae47801f3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:20:24.666101+00:00
-- url     : https://prove2.me/theorems/888d29ae-89b4-45f8-a159-2434b8473be6
-- title:
--   LevyStochCalc source module: SourceProof_4bd0a8161788e04ae47801f3
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.SimpleProfile.exists_refinement` comes from the `LevyStochCalc.Poisson.CompensatedProduct` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProduct_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated product of two mark profiles over a step

For a mark profile `f : E → ℝ` write `J(f)` for its compensated integral over the step `(a, b]`
against a Poisson random measure `N` with intensity `ν` (`compensatedProfile`). The compensated
product of two mark profiles `f, g` over the step is

  `Q(f, g) = J(f) J(g) − J(f g) − (b − a) ∫ f g dν`.

For bounded square-integrable profiles the product `f g` is again bounded and square integrable,
so each term is a compensated integral of a square-integrable profile.

This file treats simple profiles. The functions of finitely many simple mark profiles are carried
by the mark sets of one simple profile, however the mark sets of different profiles overlap. On
such a common family `A_k`, with coefficient vectors `c, c'`, the compensated product is almost
surely the quadratic element

  `(∑ c_k Ñ(B_k)) (∑ c'_k Ñ(B_k)) − ∑ c_k c'_k N(B_k)`

of the strips `B_k = (a, b] ×ˢ A_k` (`markedSecondChaos`), whose mean, Gram and orthogonality to
the compensated counts come from `Poisson/SecondChaos.lean` and `Poisson/SimpleChaos.lean`. So at
simple profiles `Q` is square integrable and centred, it is orthogonal in `L²(P)` to the
compensated integral of every simple profile, and, with `⟨u, v⟩ = ∫ u v dν`,

  `E[Q(u₁, u₂) Q(u₃, u₄)] = (b − a)² (⟨u₁, u₃⟩ ⟨u₂, u₄⟩ + ⟨u₁, u₄⟩ ⟨u₂, u₃⟩)`.

The profiles need not have disjoint supports, so their compensated integrals need not be
independent. `Poisson/CompensatedProductMoments.lean` extends the identities to bounded
square-integrable profiles.

## Main definitions

* `LevyStochCalc.Poisson.compensatedProduct` — the compensated product of two mark profiles over
  a step.
* `LevyStochCalc.Poisson.SimpleProfile.withCoeff` — the simple profile on the mark sets of a given
  one carrying new coefficients.

## Main statements

* `LevyStochCalc.Poisson.SimpleProfile.exists_refinement` — a common refinement of finitely many
  simple mark profiles.
* `LevyStochCalc.Poisson.SimpleProfile.compensatedProduct_withCoeff_ae_eq` — on a common family
  the compensated product is the quadratic element of the strips.
* `LevyStochCalc.Poisson.SimpleProfile.memLp_compensatedProduct`,
  `LevyStochCalc.Poisson.SimpleProfile.integral_compensatedProduct` — square integrability and the
  mean at simple profiles.
* `LevyStochCalc.Poisson.SimpleProfile.integral_compensatedProduct_mul` — the Gram at simple
  profiles.
* `LevyStochCalc.Poisson.SimpleProfile.integral_compensatedProduct_mul_compensatedProfile` —
  orthogonality to the first chaos at simple profiles.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

namespace SimpleProfile

omit [SigmaFinite ν] in

theorem _root_.Prove2MeSourceProof.h_4bd0a8161788e04ae47801f3 {ι : Type*} [Finite ι] (G : ι → SimpleProfile E ν) :
    ∃ (H : SimpleProfile E ν) (d : ι → Fin H.K → ℝ),
      ∀ i e, (H.withCoeff (d i)).toFun e = (G i).toFun e := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  let U : Set E := ⋃ i, ⋃ k, (G i).B k
  let pat : E → ((i : ι) → Fin (G i).K → Bool) := fun e i k => decide (e ∈ (G i).B k)
  let A : ((i : ι) → Fin (G i).K → Bool) → Set E := fun σ => pat ⁻¹' {σ} ∩ U
  have hUm : MeasurableSet U :=
    MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun k => (G i).B_measurable k
  have hAm : ∀ σ, MeasurableSet (A σ) := by
    intro σ
    refine MeasurableSet.inter ?_ hUm
    have hpre : pat ⁻¹' {σ} = ⋂ i, ⋂ k, {e | decide (e ∈ (G i).B k) = σ i k} := by
      ext e
      simp [pat, funext_iff]
    rw [hpre]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun k => ?_
    cases σ i k
    · have hset : {e | decide (e ∈ (G i).B k) = false} = ((G i).B k)ᶜ := by
        ext e
        simp
      rw [hset]
      exact ((G i).B_measurable k).compl
    · have hset : {e | decide (e ∈ (G i).B k) = true} = (G i).B k := by
        ext e
        simp
      rw [hset]
      exact (G i).B_measurable k
  have hAfin : ∀ σ, ν (A σ) ≠ ⊤ := by
    intro σ
    by_cases h : ∃ i k, σ i k = true
    · obtain ⟨i, k, hik⟩ := h
      refine ne_top_of_le_ne_top ((G i).B_finite k) (measure_mono fun e he => ?_)
      have h1 : pat e i k = σ i k := by rw [he.1]
      simpa [pat, hik] using h1
    · simp only [not_exists] at h
      have hA0 : A σ = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun e he => ?_
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 he.2
        obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hi
        have h1 : pat e i k = σ i k := by rw [he.1]
        simp [pat, hk, h i k] at h1
      rw [hA0, measure_empty]
      exact ENNReal.zero_ne_top
  have hAd : Pairwise fun σ τ => Disjoint (A σ) (A τ) := fun σ τ hστ =>
    Set.disjoint_left.2 fun e he he' => hστ ((he.1 : pat e = σ).symm.trans he'.1)
  let eqv := Fintype.equivFin ((i : ι) → Fin (G i).K → Bool)
  let H : LevyStochCalc.Poisson.SimpleProfile E ν :=
    { K := Fintype.card ((i : ι) → Fin (G i).K → Bool)
      B := fun j => A (eqv.symm j)
      B_measurable := fun j => hAm _
      B_disjoint := fun j j' hjj' => hAd (eqv.symm.injective.ne hjj')
      B_finite := fun j => hAfin _
      c := fun _ => 0 }
  let F : ι → ((i : ι) → Fin (G i).K → Bool) → ℝ :=
    fun i σ => ∑ k, (G i).c k * (if σ i k then 1 else 0)
  refine ⟨H, fun i j => F i (eqv.symm j), fun i e => ?_⟩
  by_cases he : e ∈ U
  · have hmem : e ∈ (H.withCoeff fun j => F i (eqv.symm j)).B (eqv (pat e)) := by
      change e ∈ A (eqv.symm (eqv (pat e)))
      rw [Equiv.symm_apply_apply]
      exact ⟨rfl, he⟩
    rw [LevyStochCalc.Poisson.SimpleProfile.toFun_of_mem _ hmem]
    change F i (eqv.symm (eqv (pat e))) = _
    rw [Equiv.symm_apply_apply, LevyStochCalc.Poisson.SimpleProfile.toFun]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : e ∈ (G i).B k <;> simp [pat, hk]
  · have h1 : ∀ j, e ∉ (H.withCoeff fun j => F i (eqv.symm j)).B j :=
      fun j hj => he hj.2
    rw [LevyStochCalc.Poisson.SimpleProfile.toFun_of_notMem _ h1, LevyStochCalc.Poisson.SimpleProfile.toFun_of_notMem]
    intro k hk
    exact he (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨k, hk⟩⟩)
/-! ### The compensated product on a common family -/

/-! ### The compensated product of simple profiles -/

end SimpleProfile

end LevyStochCalc.Poisson


