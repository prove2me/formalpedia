-- Prove2me | Definitions.Def_OAIQ11Fg017
-- name    : OAIQ11Fg017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T10:34:36.774823+00:00
-- url     : https://prove2.me/theorems/5f3e809b-8852-4c52-a757-01d1c5e53159
-- title:
--   Definitions bundle OAIQ11Fg017 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 53 declarations of OpenAI's Lean: 13 definitions, 2 instances and 38 theorems. The definitions and types are `OAI.Generator.Tracial.SuccessiveCoordinateHaar.firstOrderTerm`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbationMap`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbedUnitary`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbedWord`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbingUnitary`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.retainedUnitary`, `OAI.Generator.Tracial.TraceFreeHilbert`, `OAI.Generator.Tracial.traceFreeInclusion`, `OAI.Generator.Tracial.traceFreeInnerCore`, `OAI.Generator.Tracial.traceFreeLeftAction`, `OAI.Generator.Tracial.traceFreeLeftOnPreHilbert`, `OAI.Generator.Tracial.traceFreeTrace`, `OAI.Generator.Tracial.traceHilbertOperatorCStar`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_CoordinatePerturbation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/CoordinatePerturbation.lean), [`FactorGeneration_LocalizedStates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/LocalizedStates.lean), [`FactorGeneration_NormalDimension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/NormalDimension.lean), [`FactorGeneration_NormalTrace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/NormalTrace.lean), [`FactorGeneration_PerturbationBounds`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/PerturbationBounds.lean), [`FactorGeneration_TraceHilbert`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/TraceHilbert.lean), [`FactorGeneration_WordCorrelation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/WordCorrelation.lean).
--
--   **Imports.** It imports the bundles `OAIQ11Fg022` and `OAIQ11Fg023` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ11Fg018`; the statements `OAI_Generator_Tracial_HaarEndpoints_inv`, `OAI_Generator_Tracial_HaarEndpoints_negative_conjugate_correlation`, `OAI_Generator_Tracial_HaarEndpoints_positive_conjugate_correlation`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.exponential_product_correlation`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.exponential_product_eq_word`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.linearized_correlation`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbation_remainder`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.select_perturbation_coordinate`, `OAI_Generator_Tracial_conjugate_reduced_word_zero`, `OAI_Generator_Tracial_cornerEmbedding_ordered_moment`, `OAI_Generator_Tracial_exists_varying_corner_partial_independence` and `OAI_Generator_Tracial_successive_reduced_word_zero`; the proofs of `OAI_Generator_Tracial_HaarEndpoints_inv`, `OAI_Generator_Tracial_HaarEndpoints_negative_conjugate_correlation`, `OAI_Generator_Tracial_HaarEndpoints_positive_conjugate_correlation`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.commonPerturbation_norm`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.exponential_product_correlation`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.exponential_product_eq_word`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.linearized_correlation`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbation_remainder`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.select_perturbation_coordinate`, `OAI_Generator_Tracial_conjugate_reduced_word_zero`, `OAI.Generator.Tracial.represented_relative_generation` and `OAI_Generator_Tracial_successive_reduced_word_zero`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ11Fg022
import Definitions.Def_OAIQ11Fg023

section
-- module Solutions.OAIQ11_FG.FactorGeneration_CoordinatePerturbation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Group-ring maps from actual bounded unitary coordinates, with quotient
transport and coordinate Gram limits. -/

/-! Prefix labels and conjugate-word Gram identities for free-group perturbations. -/

/-! The literal bounded coordinate model of the finite-prefix free group.
The t_j sequences are the witnesses retained by the successive construction. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def SuccessiveCoordinateHaar.perturbationMap (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) :
    MonoidAlgebra ℂ (FreeGroup (PrefixLabel ell)) →ₐ[ℂ] Sequences M :=
  coordinateGroupRing (F.coordinateConjugates τ ω u z ell)

end

/-! The one literal bounded skew-adjoint perturbation K = i h. Every formal
row is its conjugate by the corresponding actual coordinate prefix. -/
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def SuccessiveCoordinateHaar.perturbingUnitary (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (α : ℝ) : unitary (Sequences M) :=
  ⟨NormedSpace.exp (F.commonPerturbation τ ω u z ell α),
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
      (show F.commonPerturbation τ ω u z ell α ∈ skewAdjoint (Sequences M) from
        skewAdjoint.mem_iff.mpr (F.commonPerturbation_skew τ ω u z ell α))⟩

def SuccessiveCoordinateHaar.perturbedUnitary (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (α : ℝ) : unitary (Sequences M) :=
  F.perturbingUnitary τ ω u z ell α*constantSequenceUnitary u

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_NormalDimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Increasing projection suprema and compatible sequential comparison.
The witnesses live in the original algebra; no trace or dimension is used. -/
namespace Tracial

/-! Continuity of the constructed dimension on arbitrary increasing projection
nets. Compatible sequential embeddings are proved first; dimension approximation
then constructs a countable subfamily with the same projection supremum. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
/-- Continuity on sequences follows from compatible embeddings into each
concrete dyadic upper approximant of the real supremum. -/
theorem traceFreeDimension_isLUB_sequence
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (q : ℕ → AlgebraProjection M) (hq : Monotone q)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range q) p) :
    traceFreeDimension hfactor hdiff p =
      sSup (Set.range (fun n => traceFreeDimension hfactor hdiff (q n))) := by
  let c := sSup (Set.range (fun n => traceFreeDimension hfactor hdiff (q n)))
  have hb := traceFreeDimension_range_bddAbove hfactor hdiff q
  have hne := Set.range_nonempty (fun n => traceFreeDimension hfactor hdiff (q n))
  have hqc (n : ℕ) : traceFreeDimension hfactor hdiff (q n) ≤ c := le_csSup hb ⟨n,rfl⟩
  have hc : 0 ≤ c := (traceFreeDimension_nonneg hfactor hdiff (q 0)).trans (hqc 0)
  have hc1 : c ≤ 1 := csSup_le hne (by
    rintro _ ⟨n,rfl⟩; exact traceFreeDimension_le_one hfactor hdiff (q n))
  apply le_antisymm ?_ (csSup_le hne (by
    rintro _ ⟨n,rfl⟩
    exact traceFreeDimension_mono hfactor hdiff (hp.1 ⟨n,rfl⟩)))
  apply le_of_all_dyadic_errors
  intro n
  obtain ⟨r,hcr,hrc⟩ := traceFreeDimension_exists_upper hfactor hdiff hfinite hunit c hc hc1 n
  have hqr (k : ℕ) : (q k).Subequivalent r :=
    (traceFreeDimension_le_iff_subequivalent hfactor hdiff hfinite hunit _ _).mp
      ((hqc k).trans hcr)
  exact (traceFreeDimension_subequivalent hfactor hdiff
    (AlgebraProjection.isLUB_subequivalent_of_sequence hfactor hfinite q hq p hp r hqr)).trans hrc

include hfinite in
/-- Construct an increasing countable subfamily whose supremum dimension is
the real supremum of the entire directed family. No countability is assumed. -/
theorem traceFreeDimension_exists_exhausting_sequence
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (q : I → AlgebraProjection M) (hq : Monotone q) :
    ∃ (a : ℕ → I) (s : AlgebraProjection M), Monotone a ∧
      IsLUB (Set.range (fun n => q (a n))) s ∧
      traceFreeDimension hfactor hdiff s =
        sSup (Set.range (fun i => traceFreeDimension hfactor hdiff (q i))) := by
  classical
  let c := sSup (Set.range (fun i => traceFreeDimension hfactor hdiff (q i)))
  have hb := traceFreeDimension_range_bddAbove hfactor hdiff q
  have hqc (i : I) : traceFreeDimension hfactor hdiff (q i) ≤ c := le_csSup hb ⟨i,rfl⟩
  have hex (n : ℕ) : ∃ i, c-1/2^n < traceFreeDimension hfactor hdiff (q i) := by
    have hn : c-1/2^n < c := sub_lt_self c (by positivity)
    obtain ⟨_,⟨i,rfl⟩,hi⟩ := exists_lt_of_lt_csSup
      (Set.range_nonempty (fun i => traceFreeDimension hfactor hdiff (q i))) hn
    exact ⟨i,hi⟩
  choose f hf using hex
  obtain ⟨a,ha,hfa,_⟩ := exists_monotone_dominating_from f (Classical.choice ‹Nonempty I›)
  obtain ⟨s,hs⟩ := AlgebraProjection.exists_isLUB_monotone (fun n => q (a n)) (hq.comp ha)
  refine ⟨a,s,ha,hs,le_antisymm ?_ ?_⟩
  · rw [traceFreeDimension_isLUB_sequence hfactor hdiff hfinite hunit _ (hq.comp ha) s hs]
    exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨n,rfl⟩; exact hqc (a n))
  · apply le_of_all_dyadic_errors
    intro n
    have hfq := traceFreeDimension_mono hfactor hdiff (hq (hfa n))
    have hqs := traceFreeDimension_mono hfactor hdiff (hs.1 ⟨n,rfl⟩)
    have hfn := hf n
    linarith

include hfinite in
/-- The constructed countable supremum bounds the entire net: adjoining any
one index cannot increase its dimension, so strict increase forces equality. -/
theorem traceFreeDimension_exists_isLUB
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (q : I → AlgebraProjection M) (hq : Monotone q) :
    ∃ p : AlgebraProjection M, IsLUB (Set.range q) p ∧
      traceFreeDimension hfactor hdiff p =
        sSup (Set.range (fun i => traceFreeDimension hfactor hdiff (q i))) := by
  obtain ⟨a,s,ha,hs,hd⟩ := traceFreeDimension_exists_exhausting_sequence
    hfactor hdiff hfinite hunit q hq
  have hupper (i : I) : q i ≤ s := by
    obtain ⟨b,hb,hab,hib⟩ := exists_monotone_dominating_from a i
    obtain ⟨t,ht⟩ := AlgebraProjection.exists_isLUB_monotone (fun n => q (b n)) (hq.comp hb)
    have hst : s ≤ t := hs.2 (by
      rintro _ ⟨n,rfl⟩; exact (hq (hab n)).trans (ht.1 ⟨n,rfl⟩))
    have htd : traceFreeDimension hfactor hdiff t ≤ traceFreeDimension hfactor hdiff s := by
      rw [hd,traceFreeDimension_isLUB_sequence hfactor hdiff hfinite hunit _ (hq.comp hb) t ht]
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨n,rfl⟩
      exact le_csSup (traceFreeDimension_range_bddAbove hfactor hdiff q) ⟨b n,rfl⟩
    have he : s=t := by
      by_contra hne
      exact (not_lt_of_ge htd) (traceFreeDimension_strictMono hfactor hdiff hfinite hunit
        (lt_of_le_of_ne hst hne))
    rw [he]
    exact (hq (hib 0)).trans (ht.1 ⟨0,rfl⟩)
  refine ⟨s,⟨?_,?_⟩,hd⟩
  · rintro _ ⟨i,rfl⟩; exact hupper i
  · intro p hp
    exact hs.2 (by rintro _ ⟨n,rfl⟩; exact hp ⟨a n,rfl⟩)

include hfinite in
/-- Order continuity on arbitrary nonempty directed projection nets. -/
theorem traceFreeDimension_isLUB_monotone
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (q : I → AlgebraProjection M) (hq : Monotone q)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range q) p) :
    traceFreeDimension hfactor hdiff p =
      sSup (Set.range (fun i => traceFreeDimension hfactor hdiff (q i))) := by
  obtain ⟨s,hs,hd⟩ := traceFreeDimension_exists_isLUB hfactor hdiff hfinite hunit q hq
  have he : p=s := le_antisymm (hp.2 hs.1) (hs.2 hp.1)
  rw [he]
  exact hd

end Tracial

/-! Original-factor wrapper for normalized faithful order-continuous projection
dimension. This does not assert the existence of a linear trace functional. -/

/-! Exact prescribed dimensions are attained by actual subprojections.
Chain bounds use the proved arbitrary-net continuity of dimension. -/
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDimension_bounded_chain
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (c : Set (AlgebraProjection M)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (p : AlgebraProjection M) (d : ℝ)
    (hp : ∀ q ∈ c, q ≤ p) (hd : ∀ q ∈ c, traceFreeDimension hfactor hdiff q ≤ d) :
    ∃ q : AlgebraProjection M, (∀ r ∈ c, r ≤ q) ∧ q ≤ p ∧
      traceFreeDimension hfactor hdiff q ≤ d := by
  let : Nonempty c := hne.to_subtype
  let : IsDirected c (· ≤ ·) := ⟨by
    intro u v
    rcases hc.total u.property v.property with h | h
    · exact ⟨v,h,le_rfl⟩
    · exact ⟨u,le_rfl,h⟩⟩
  obtain ⟨q,hq,hD⟩ := traceFreeDimension_exists_isLUB hfactor hdiff hfinite hunit
    (fun r : c => r.val) (fun _ _ h => h)
  refine ⟨q,fun r hr => hq.1 ⟨⟨r,hr⟩,rfl⟩,?_,?_⟩
  · exact hq.2 (by rintro _ ⟨r,rfl⟩; exact hp r.val r.property)
  · rw [hD]
    exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨r,rfl⟩; exact hd r.val r.property)

include hfinite in
theorem traceFreeDimension_exists_maximal_below
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (p : AlgebraProjection M) (d : ℝ) (hd : 0 ≤ d) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ traceFreeDimension hfactor hdiff q ≤ d ∧
      ∀ r : AlgebraProjection M, r ≤ p → traceFreeDimension hfactor hdiff r ≤ d →
        q ≤ r → r ≤ q := by
  let S : Set (AlgebraProjection M) := {q | q ≤ p ∧ traceFreeDimension hfactor hdiff q ≤ d}
  obtain ⟨q,hq⟩ := zorn_le₀ S (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · obtain ⟨q,hcq,hqp,hqd⟩ := traceFreeDimension_bounded_chain hfactor hdiff hfinite hunit
        c hchain hne p d (fun q hq => (hc hq).1) (fun q hq => (hc hq).2)
      exact ⟨q,⟨hqp,hqd⟩,hcq⟩
    · refine ⟨⟨0,IsStarProjection.zero _⟩,⟨mul_zero _,?_⟩,?_⟩
      · have hz := traceFreeDyadicSup_zero hfactor hdiff ⟨1,IsStarProjection.one _⟩
          ⟨0,IsStarProjection.zero _⟩ hunit rfl
        exact hz.le.trans hd
      · intro r hr
        exact (hne ⟨r,hr⟩).elim)
  exact ⟨q,hq.1.1,hq.1.2,fun r hr hrd hqr => hq.2 ⟨hr,hrd⟩ hqr⟩

include hfinite in
/-- Every dimension between zero and D(p) is realized inside p. -/
theorem traceFreeDimension_exists_subprojection
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (p : AlgebraProjection M) (d : ℝ) (hd : 0 ≤ d)
    (hdp : d ≤ traceFreeDimension hfactor hdiff p) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ traceFreeDimension hfactor hdiff q=d := by
  obtain ⟨q,hqp,hqd,hmax⟩ := traceFreeDimension_exists_maximal_below
    hfactor hdiff hfinite hunit p d hd
  refine ⟨q,hqp,le_antisymm hqd ?_⟩
  by_contra hnot
  have hlt : traceFreeDimension hfactor hdiff q < d := lt_of_not_ge hnot
  let r := AlgebraProjection.remainder q p hqp
  have hr : r.val≠0 := by
    change p.val-q.val≠0
    intro hz
    have he : p=q := Subtype.ext (sub_eq_zero.mp hz)
    rw [he] at hdp
    exact (not_lt_of_ge hdp) hlt
  obtain ⟨s,hs,hpos,hsmall⟩ := traceFreeDimension_exists_small_subprojection
    hfactor hdiff hfinite hunit r hr (d-traceFreeDimension hfactor hdiff q) (sub_pos.mpr hlt)
  have ho : q.val*s.val=0 :=
    projection_orthogonal_of_le (AlgebraProjection.remainder_orthogonal q p hqp) le_rfl hs
  let t := orthogonalSum q s ho
  have htp : t ≤ p := orthogonalSum_le ho hqp (hs.trans (AlgebraProjection.remainder_le q p hqp))
  have htD : traceFreeDimension hfactor hdiff t=
      traceFreeDimension hfactor hdiff q+traceFreeDimension hfactor hdiff s :=
    traceFreeDyadicSup_orthogonal_add hfactor hdiff hfinite ⟨1,IsStarProjection.one _⟩ q s
      hunit (one_mul _) (one_mul _) ho
  have htd : traceFreeDimension hfactor hdiff t ≤ d := by rw [htD]; linarith
  have hle : t ≤ q := hmax t htp htd (le_orthogonalSum_left _ _ ho)
  have hmono := traceFreeDimension_mono hfactor hdiff hle
  rw [htD] at hmono
  linarith

end

/-! Finite partitions with prescribed dimensions, and actual equivalent
partitions of arbitrary positive finite size in every corner. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
/-- Every prescribed finite list of nonnegative dimensions summing to D(p)
is realized by pairwise orthogonal actual projections summing to p. -/
theorem traceFreeDimension_exists_partition
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (n : ℕ) (p : AlgebraProjection M) (d : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hsum : ∑ i, d i=traceFreeDimension hfactor hdiff p) :
    ∃ q : Fin n → AlgebraProjection M, (∀ i, q i ≤ p) ∧
      (∀ i j, i≠j → (q i).val*(q j).val=0) ∧
      (∑ i, (q i).val)=p.val ∧ (∀ i, traceFreeDimension hfactor hdiff (q i)=d i) := by
  induction n generalizing p with
  | zero =>
    have hpD : traceFreeDimension hfactor hdiff p=0 := by simpa using hsum.symm
    have hpz : p.val=0 := (traceFreeDyadicSup_eq_zero_iff hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ p hunit).mp hpD
    refine ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i,fun i => Fin.elim0 i,?_,fun i => Fin.elim0 i⟩
    simpa using hpz.symm
  | succ n ih =>
    have hsum' : d 0+∑ i : Fin n, d i.succ=traceFreeDimension hfactor hdiff p := by
      simpa only [Fin.sum_univ_succ] using hsum
    have hdp : d 0 ≤ traceFreeDimension hfactor hdiff p := by
      have hh : 0 ≤ ∑ i : Fin n, d i.succ := Finset.sum_nonneg (fun i _ => hd i.succ)
      linarith
    obtain ⟨q,hqp,hqd⟩ := traceFreeDimension_exists_subprojection
      hfactor hdiff hfinite hunit p (d 0) (hd 0) hdp
    let r := AlgebraProjection.remainder q p hqp
    have hrD : traceFreeDimension hfactor hdiff r=
        traceFreeDimension hfactor hdiff p-d 0 := by
      rw [traceFreeDimension_remainder hfactor hdiff hfinite hunit q p hqp,hqd]
    obtain ⟨b,hbr,hbo,hbs,hbd⟩ := ih r (fun i => d i.succ) (fun i => hd i.succ) (by
      rw [hrD]; linarith)
    let a : Fin (n+1) → AlgebraProjection M := Fin.cons q b
    have hqb (i : Fin n) : q.val*(b i).val=0 :=
      projection_orthogonal_of_le (AlgebraProjection.remainder_orthogonal q p hqp) le_rfl (hbr i)
    refine ⟨a,?_,?_,?_,?_⟩
    · intro i
      refine Fin.cases hqp (fun j => ?_) i
      exact (hbr j).trans (AlgebraProjection.remainder_le q p hqp)
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro k
        refine Fin.cases ?_ (fun l => ?_) k
        · intro h; exact (h rfl).elim
        · intro _; exact hqb l
      · intro k
        refine Fin.cases ?_ (fun l => ?_) k
        · intro _; exact PartialIsometry.orthogonal_reverse q (b j) (hqb j)
        · intro h
          exact hbo j l (fun he => h (congrArg Fin.succ he))
    · rw [Fin.sum_univ_succ]
      change q.val+(∑ i, (b i).val)=p.val
      rw [hbs]
      change q.val+(p.val-q.val)=p.val
      abel
    · intro i
      exact Fin.cases hqd hbd i

include hfinite in
/-- A finite corner partition into n equal dimensions, for every n>0. -/
theorem traceFreeDimension_exists_uniform_partition
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (n : ℕ) (hn : 0<n) (p : AlgebraProjection M) :
    ∃ q : Fin n → AlgebraProjection M, (∀ i, q i ≤ p) ∧
      (∀ i j, i≠j → (q i).val*(q j).val=0) ∧
      (∑ i, (q i).val)=p.val ∧
      (∀ i, traceFreeDimension hfactor hdiff (q i)=traceFreeDimension hfactor hdiff p/n) := by
  apply traceFreeDimension_exists_partition hfactor hdiff hfinite hunit n p
    (fun _ => traceFreeDimension hfactor hdiff p/n)
  · intro i
    exact div_nonneg (traceFreeDimension_nonneg hfactor hdiff p) (Nat.cast_nonneg n)
  · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp

include hfactor hdiff hfinite in
/-- Actual matrix-unit legs for a partition of every positive finite size. -/
theorem traceFreeDimension_exists_equivalent_partition
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (n : ℕ) (hn : 0<n) (p : AlgebraProjection M) :
    Nonempty (EquivalentPartition p (Fin n)) := by
  classical
  obtain ⟨q,hqp,hqo,hqs,hqd⟩ := traceFreeDimension_exists_uniform_partition
    hfactor hdiff hfinite hunit n hn p
  let i₀ : Fin n := ⟨0,hn⟩
  have he (i : Fin n) : (q i₀).Equivalent (q i) :=
    (traceFreeDyadicSup_eq_iff_equivalent hfactor hdiff hfinite ⟨1,IsStarProjection.one _⟩
      (q i₀) (q i) hunit (one_mul _) (one_mul _)).mp ((hqd i₀).trans (hqd i).symm)
  choose v hv ht using he
  exact ⟨{
    base := q i₀
    leg := v
    initial := hv
    cross := fun i j hij => (v i).adjoint.mul_eq_zero (v j) (by
      change (v i).target.val*(v j).target.val=0
      rw [ht i,ht j]; exact hqo i j hij)
    total := by simpa only [ht] using hqs
    bound := fun i => by rw [ht]; exact hqp i }⟩

end Tracial

/-! Actual vector functionals and their continuity on directed projection
suprema. No factor, trace, separability, or dimension hypothesis is used. -/
open Filter
open scoped Topology BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_LocalizedStates
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Localization of actual signed vector/dimension values. Fixed strict
sublevel sets, rather than a limiting strict inequality, supply Zorn bounds. -/
open Filter
open scoped Topology
section
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDimension_tendsto_monotone
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (q : I → AlgebraProjection M) (hq : Monotone q)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range q) p) :
    Tendsto (fun i => traceFreeDimension hfactor hdiff (q i)) atTop
      (𝓝 (traceFreeDimension hfactor hdiff p)) := by
  rw [traceFreeDimension_isLUB_monotone hfactor hdiff hfinite hunit q hq p hp]
  exact tendsto_atTop_isLUB ((traceFreeDimension_mono hfactor hdiff).comp hq)
    (isLUB_csSup (Set.range_nonempty _) (traceFreeDimension_range_bddAbove hfactor hdiff q))

include hfinite in
/-- Concrete localization for a real linear combination of the actual vector
functional and the already constructed dimension; no linear trace is assumed. -/
theorem exists_signed_vector_dimension_corner
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (c d : ℝ) (G : AlgebraProjection M) (hG : G.val≠0)
    (hμG : 0 ≤ c*G.vectorValue ξ+d*traceFreeDimension hfactor hdiff G) :
    ∃ F : AlgebraProjection M, F ≤ G ∧ F.val≠0 ∧
      ∀ p, p ≤ F → 0 ≤ c*p.vectorValue ξ+d*traceFreeDimension hfactor hdiff p := by
  apply AlgebraProjection.exists_nonnegative_corner
    (fun p => c*p.vectorValue ξ+d*traceFreeDimension hfactor hdiff p) ?_ ?_ G hG hμG
  · intro p q ho
    have hν : (orthogonalSum p q ho).vectorValue ξ=p.vectorValue ξ+q.vectorValue ξ := by
      change (inner ℂ ξ (p.val.val ξ+q.val.val ξ)).re=_
      rw [inner_add_right,Complex.add_re]
      rfl
    have hD := traceFreeDyadicSup_orthogonal_add hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ p q hunit (one_mul _) (one_mul _) ho
    change traceFreeDimension hfactor hdiff (orthogonalSum p q ho)=
      traceFreeDimension hfactor hdiff p+traceFreeDimension hfactor hdiff q at hD
    rw [hν,hD]
    ring
  · intro I _ _ _ a ha p hp
    exact ((AlgebraProjection.vectorValue_tendsto_monotone a ha p hp ξ).const_mul c).add
      ((traceFreeDimension_tendsto_monotone hfactor hdiff hfinite hunit a ha p hp).const_mul d)

include hfinite in
theorem exists_vector_dimension_lower_corner
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (G : AlgebraProjection M) (hG : G.val≠0) :
    ∃ F : AlgebraProjection M, F ≤ G ∧ F.val≠0 ∧ ∀ p, p ≤ F →
      G.vectorValue ξ*traceFreeDimension hfactor hdiff p ≤
        p.vectorValue ξ*traceFreeDimension hfactor hdiff G := by
  obtain ⟨F,hFG,hF,h⟩ := exists_signed_vector_dimension_corner hfactor hdiff hfinite hunit
    ξ (traceFreeDimension hfactor hdiff G) (-G.vectorValue ξ) G hG (by nlinarith)
  exact ⟨F,hFG,hF,fun p hp => by have hh := h p hp; nlinarith⟩

include hfinite in
theorem exists_vector_dimension_upper_corner
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (G : AlgebraProjection M) (hG : G.val≠0) :
    ∃ F : AlgebraProjection M, F ≤ G ∧ F.val≠0 ∧ ∀ p, p ≤ F →
      p.vectorValue ξ*traceFreeDimension hfactor hdiff G ≤
        G.vectorValue ξ*traceFreeDimension hfactor hdiff p := by
  obtain ⟨F,hFG,hF,h⟩ := exists_signed_vector_dimension_corner hfactor hdiff hfinite hunit
    ξ (-traceFreeDimension hfactor hdiff G) (G.vectorValue ξ) G hG (by nlinarith)
  exact ⟨F,hFG,hF,fun p hp => by have hh := h p hp; nlinarith⟩

end

/-! Tight multiplicative localization of an actual Hilbert vector functional
against the constructed projection dimension. The corner is constructed. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
/-- An actual unit vector admits a nonzero corner on which every projection
value is between a D(p) and (1+ε)a D(p), with a strictly positive. -/
theorem exists_vector_dimension_localization
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (hξ : ‖ξ‖=1) (ε : ℝ) (hε : 0<ε) :
    ∃ (E : AlgebraProjection M) (a : ℝ), E.val≠0 ∧ 0<a ∧
      ∀ p : AlgebraProjection M, p ≤ E →
        a*traceFreeDimension hfactor hdiff p ≤ (inner ℂ ξ (p.val.val ξ)).re ∧
        (inner ℂ ξ (p.val.val ξ)).re ≤ (1+ε)*a*traceFreeDimension hfactor hdiff p := by
  classical
  let ν := AlgebraProjection.vectorValue (M := M) ξ
  let D := traceFreeDimension hfactor hdiff
  let oneP : AlgebraProjection M := ⟨1,IsStarProjection.one _⟩
  have hν1 : ν oneP=1 := by
    change (inner ℂ ξ ξ).re=1
    rw [inner_self_eq_norm_sq_to_K,hξ]
    norm_num
  have hD1 : D oneP=1 := traceFreeDyadicSup_self hfactor hdiff oneP
  have hDpos (p : AlgebraProjection M) (hp : p.val≠0) : 0<D p :=
    traceFreeDyadicSup_pos hfactor hdiff hfinite oneP p hp
  obtain ⟨F,_,hF,hlo⟩ := exists_vector_dimension_lower_corner
    hfactor hdiff hfinite hunit ξ oneP hunit
  have hFbound (p : AlgebraProjection M) (hp : p ≤ F) : D p ≤ ν p := by
    have hh := hlo p hp
    change ν oneP*D p ≤ ν p*D oneP at hh
    simpa only [hν1,hD1,one_mul,mul_one] using hh
  let R : Set ℝ := {b | ∃ p : AlgebraProjection M, p ≤ F ∧ p.val≠0 ∧ b=ν p/D p}
  have hRne : R.Nonempty := ⟨ν F/D F,F,le_rfl,hF,rfl⟩
  have hRlower : ∀ b ∈ R, 1 ≤ b := by
    rintro b ⟨p,hp,hpn,rfl⟩
    exact (le_div_iff₀ (hDpos p hpn)).mpr (by simpa only [one_mul] using hFbound p hp)
  have hRb : BddBelow R := ⟨1,hRlower⟩
  let a := sInf R
  have ha1 : 1 ≤ a := le_csInf hRne hRlower
  have ha : 0<a := lt_of_lt_of_le (by norm_num) ha1
  have hnear : a < (1+ε)*a := by nlinarith
  obtain ⟨_,⟨r,hrF,hr,hratio⟩,hnearR⟩ := exists_lt_of_csInf_lt hRne hnear
  rw [hratio] at hnearR
  obtain ⟨E,hEr,hE,hhi⟩ := exists_vector_dimension_upper_corner
    hfactor hdiff hfinite hunit ξ r hr
  refine ⟨E,a,hE,ha,?_⟩
  intro p hp
  by_cases hp0 : p.val=0
  · have hν0 : ν p=0 := by
      change (inner ℂ ξ (p.val.val ξ)).re=0
      rw [hp0]
      simp
    have hD0 : D p=0 := traceFreeDyadicSup_zero hfactor hdiff oneP p hunit hp0
    change a*D p ≤ ν p ∧ ν p ≤ (1+ε)*a*D p
    rw [hν0,hD0]
    simp
  · have hDp : 0<D p := hDpos p hp0
    have hpF : p ≤ F := hp.trans (hEr.trans hrF)
    have hap : a ≤ ν p/D p := csInf_le hRb ⟨p,hpF,hp0,rfl⟩
    have hloP : a*D p ≤ ν p := (le_div_iff₀ hDp).mp hap
    have hDr : 0<D r := hDpos r hr
    have hhiP := hhi p hp
    change ν p*D r ≤ ν r*D p at hhiP
    have hratioP : ν p ≤ (ν r/D r)*D p := by
      apply (mul_le_mul_iff_right₀ hDr).mp
      calc D r*ν p = ν p*D r := mul_comm _ _
           _ ≤ ν r*D p := hhiP
           _ = D r*(ν r/D r*D p) := by field_simp
    have hbound : (ν r/D r)*D p ≤ (1+ε)*a*D p :=
      mul_le_mul_of_nonneg_right hnearR.le hDp.le
    exact ⟨hloP,hratioP.trans hbound⟩

end

/-! Positive spectral approximants inside an actual projection corner, and
extension of localized projection inequalities to positive operators. -/
open scoped BigOperators CStarAlgebra

/-! Projection localization yields actual positive-operator inequalities for
bounded linear functionals, and a nearly cyclic functional on the corner. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.localizedCStar
attribute [local instance] OAI.Generator.Tracial.localizedOrder
local instance localizedPreorder_r5f7020_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.localizedLE
attribute [local instance] OAI.Generator.Tracial.localizedStarOrder
/-- Concrete projection and positive-operator localization, with an actual
bounded complex-linear functional and a nonzero constructed corner. -/
theorem exists_localized_vector_functional
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (hξ : ‖ξ‖=1) (ε : ℝ) (hε : 0<ε) :
    ∃ (E : AlgebraProjection M) (a : ℝ), E.val≠0 ∧ 0<a ∧
      ∀ (x : M.toStarSubalgebra) (hx : 0 ≤ x), E.val*x=x →
        a*(dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re ≤
          (vectorFunctional ξ x).re ∧
        (vectorFunctional ξ x).re ≤
          (1+ε)*a*(dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re := by
  obtain ⟨E,a,hE,ha,hp⟩ := exists_vector_dimension_localization hfactor hdiff hfinite hunit ξ hξ ε hε
  refine ⟨E,a,hE,ha,?_⟩
  intro x hx hEx
  exact positive_functional_bounds_of_projection_bounds hfactor hdiff hfinite hunit
    (vectorFunctional ξ) E a ((1+ε)*a) ha.le (mul_nonneg (by linarith) ha.le) hp x hx hEx

end

/-! An actual positive normalized vector functional with arbitrarily small
multiplicative failure of cyclicity on a nonzero corner. No trace is assumed. -/
open scoped CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.cornerStateCStar
attribute [local instance] OAI.Generator.Tracial.cornerStateOrder
local instance cornerStatePreorder_r5f7020_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.cornerStateLE
attribute [local instance] OAI.Generator.Tracial.cornerStateStarOrder
include hfactor hdiff hfinite in
/-- A localized vector functional is nearly cyclic for every element in its
corner. This gives both inequalities by applying the result to x and x*. -/
theorem exists_corner_nearly_cyclic_vector
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (hξ : ‖ξ‖=1) (ε : ℝ) (hε : 0<ε) :
    ∃ E : AlgebraProjection M, E.val≠0 ∧
      (∀ p : AlgebraProjection M, p ≤ E → p.val≠0 → 0<(vectorFunctional ξ p.val).re) ∧
      ∀ x : M.toStarSubalgebra, E.val*x=x → x*E.val=x →
        (vectorFunctional ξ (star x*x)).re ≤ (1+ε)*(vectorFunctional ξ (x*star x)).re := by
  obtain ⟨E,a,hE,ha,h⟩ := exists_localized_vector_functional
    hfactor hdiff hfinite hunit ξ hξ ε hε
  refine ⟨E,hE,?_,?_⟩
  · intro p hp hpn
    have hpstar : star p.val*p.val=p.val := by
      rw [p.property.isSelfAdjoint.star_eq,p.property.isIdempotentElem.eq]
    have hpnonneg : 0 ≤ p.val := hpstar ▸ star_mul_self_nonneg p.val
    have hh := (h p.val hpnonneg hp).1
    rw [dimensionSpectralValue_projection,Complex.ofReal_re] at hh
    exact (mul_pos ha (traceFreeDyadicSup_pos hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ p hpn)).trans_le hh
  intro x hEx hxE
  have hExs : E.val*star x=star x := by
    simpa only [star_mul,E.property.isSelfAdjoint.star_eq] using congrArg star hxE
  have h₁ := h (star x*x) (star_mul_self_nonneg x) (by rw [← mul_assoc,hExs])
  have h₂ := h (x*star x) (mul_star_self_nonneg x) (by rw [← mul_assoc,hEx])
  have he := congrArg Complex.re (dimensionSpectralValue_star_mul_self hfactor hdiff hfinite hunit x)
  have hm := mul_le_mul_of_nonneg_left h₂.1 (by linarith : 0 ≤ 1+ε)
  rw [← he] at hm
  nlinarith [h₁.2]

end

/-! A full finite matrix partition can be rebased into every nonzero corner.
The legs are constructed partial isometries, not assumed matrix units. -/
open scoped BigOperators
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfactor hdiff hfinite in
/-- A partition of 1 with common initial projection inside any given nonzero E. -/
theorem exists_equivalent_partition_base_le
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (E : AlgebraProjection M) (hE : E.val≠0) :
    ∃ (n : ℕ) (_hn : 0<n)
      (Q : EquivalentPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) (Fin n)),
      Q.base ≤ E ∧ Q.base.val≠0 := by
  have hD : 0<traceFreeDimension hfactor hdiff E :=
    traceFreeDyadicSup_pos hfactor hdiff hfinite ⟨1,IsStarProjection.one _⟩ E hE
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hD (by norm_num : (1/2 : ℝ)<1)
  rw [one_div_pow] at hn
  have hn0 : 0<2^n := Nat.two_pow_pos n
  let Q := Classical.choice (traceFreeDimension_exists_equivalent_partition
    hfactor hdiff hfinite hunit (2^n) hn0 ⟨1,IsStarProjection.one _⟩)
  have : Nonempty (Fin (2^n)) := ⟨⟨0,hn0⟩⟩
  have hQ : traceFreeDimension hfactor hdiff Q.base=1/2^n := by
    rw [Q.dimension_base hfactor hdiff hfinite hunit]
    have h1 : traceFreeDimension hfactor hdiff (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M)=1 :=
      traceFreeDyadicSup_self hfactor hdiff ⟨1,IsStarProjection.one _⟩
    rw [h1]
    simp only [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  obtain ⟨v,hv,ht⟩ := (traceFreeDimension_le_iff_subequivalent hfactor hdiff hfinite hunit Q.base E).mp
    (by rw [hQ]; exact hn.le)
  have hvt : v.adjoint.target=Q.base := by
    apply Subtype.ext
    change star v.val*star (star v.val)=Q.base.val
    rw [star_star,v.initial,hv]
  let R := Q.rebase v.adjoint hvt
  exact ⟨2^n,hn0,R,ht,R.base_ne_zero hunit⟩

end

/-! Extension of a vector functional through actual matrix-partition legs.
Finite coefficient identities transfer the corner quadratic inequality. -/
open scoped BigOperators CStarAlgebra

/-! Globally defined positive unital linear functionals with arbitrarily small multiplicative quadratic trace error. -/
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.approxTraceCStar
local instance approxTraceOrder_r5f7020_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance approxTracePreorder_r5f7020_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.approxTraceLE
local instance approxTraceStarOrder_r5f7020_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
include hfactor hdiff hfinite in
/-- A constructed approximate tracial state on the entire original algebra. -/
theorem exists_approximately_tracial_state
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (ε : ℝ) (hε : 0<ε) :
    ∃ φ : M.toStarSubalgebra →L[ℂ] ℂ,
      ‖φ‖ ≤ 1 ∧ φ 1=1 ∧ (∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re) ∧
      ∀ x : M.toStarSubalgebra, (φ (star x*x)).re ≤ (1+ε)*(φ (x*star x)).re := by
  classical
  obtain ⟨ξ,hξ⟩ := exists_unit_vector_of_unit_ne_zero hunit
  obtain ⟨E,hE,hfaith,hcorner⟩ := exists_corner_nearly_cyclic_vector
    hfactor hdiff hfinite hunit ξ hξ ε hε
  obtain ⟨n,hn,Q,hQE,hQ⟩ := exists_equivalent_partition_base_le hfactor hdiff hfinite hunit E hE
  have hbase : 0<(vectorFunctional ξ Q.base.val).re := hfaith Q.base hQE hQ
  let A : ℝ := ∑ i, ‖(Q.leg i).val.val ξ‖^2
  have hi (i : Fin n) : ‖(Q.leg i).val.val ξ‖^2=(vectorFunctional ξ Q.base.val).re := by
    have h := congrArg Complex.re (vectorFunctional_star_mul_self ξ (Q.leg i).val)
    rw [(Q.leg i).initial,Q.initial] at h
    exact_mod_cast h.symm
  have hA : 0<A := by
    apply Finset.sum_pos
    · intro i _
      rw [hi]
      exact hbase
    · exact ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  let F := Q.matrixVectorFunctional ξ
  have hF1 : F 1=(A : ℂ) := Q.matrixVectorFunctional_one ξ
  have hFnorm : ‖F‖ ≤ A := Q.matrixVectorFunctional_norm_le ξ
  have hFpos (x : M.toStarSubalgebra) (hx : 0 ≤ x) : 0 ≤ (F x).re := by
    change 0 ≤ ((∑ i, vectorFunctional ((Q.leg i).val.val ξ)) x).re
    rw [sum_apply,Complex.re_sum]
    exact Finset.sum_nonneg (fun i _ => vectorFunctional_positive _ x hx)
  have hFtrace (x : M.toStarSubalgebra) : (F (star x*x)).re ≤ (1+ε)*(F (x*star x)).re := by
    apply Q.matrixVectorFunctional_nearly_cyclic rfl ξ ε ?_ x
    intro y hly hry
    have hl : E.val*y=y := by
      calc E.val*y = E.val*(Q.base.val*y) := by rw [hly]
           _ = y := by rw [← mul_assoc,show E.val*Q.base.val=Q.base.val from hQE,hly]
    have hr : y*E.val=y := by
      calc y*E.val = (y*Q.base.val)*E.val := by rw [hry]
           _ = y := by rw [mul_assoc,projection_mul_of_le hQE,hry]
    exact hcorner y hl hr
  let φ : M.toStarSubalgebra →L[ℂ] ℂ := ((A⁻¹ : ℝ) : ℂ) • F
  have hφ (x : M.toStarSubalgebra) : (φ x).re=A⁻¹*(F x).re := by
    simp only [φ,smul_apply,smul_eq_mul,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  refine ⟨φ,?_,?_,?_,?_⟩
  · change ‖((A⁻¹ : ℝ) : ℂ) • F‖ ≤ 1
    rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hA.le)]
    exact (mul_le_mul_of_nonneg_left hFnorm (inv_nonneg.mpr hA.le)).trans_eq (inv_mul_cancel₀ hA.ne')
  · change ((A⁻¹ : ℝ) : ℂ)*(F 1)=1
    rw [hF1,← Complex.ofReal_mul,inv_mul_cancel₀ hA.ne',Complex.ofReal_one]
  · intro x hx
    rw [hφ]
    exact mul_nonneg (inv_nonneg.mpr hA.le) (hFpos x hx)
  · intro x
    rw [hφ,hφ]
    have h := mul_le_mul_of_nonneg_left (hFtrace x) (inv_nonneg.mpr hA.le)
    calc A⁻¹*(F (star x*x)).re ≤ A⁻¹*((1+ε)*(F (x*star x)).re) := h
         _ = (1+ε)*(A⁻¹*(F (x*star x)).re) := by ring

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.predualFunctionals_normed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A genuine linear state with exact equality of real quadratic values,
constructed from the original finite factor predicates by scalar compactness. -/
section
open Filter
open scoped Topology CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.quadraticStateCStar
local instance quadraticStateOrder_r5f7020_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance quadraticStatePreorder_r5f7020_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.quadraticStateLE
local instance quadraticStateStarOrder_r5f7020_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
include hfactor hdiff hfinite in
theorem exists_real_quadratic_state (hunit : (1 : M.toStarSubalgebra) ≠ 0) :
    ∃ φ : M.toStarSubalgebra →L[ℂ] ℂ,
      ‖φ‖ ≤ 1 ∧ φ 1=1 ∧ (∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re) ∧
      ∀ x : M.toStarSubalgebra, (φ (star x*x)).re=(φ (x*star x)).re := by
  have hex (n : ℕ) := exists_approximately_tracial_state hfactor hdiff hfinite hunit
    (1/((n : ℝ)+1)) (by positivity)
  choose f hf hfone hfpos hfquad using hex
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  obtain ⟨φ,hφ,ht⟩ := exists_bounded_functional_ultralimit ω f 1 (by norm_num) hf
  have hε : Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) (ω : Filter ℕ) (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left (Ultrafilter.of_le _)
  have hre (x : M.toStarSubalgebra) := (Complex.continuous_re.tendsto (φ x)).comp (ht x)
  have hle (x : M.toStarSubalgebra) : (φ (star x*x)).re ≤ (φ (x*star x)).re := by
    have hr := (hε.const_add 1).mul (hre (x*star x))
    have h := le_of_tendsto_of_tendsto (hre (star x*x)) hr
      (Eventually.of_forall (fun n => hfquad n x))
    simpa only [add_zero,one_mul] using h
  refine ⟨φ,hφ,?_,?_,?_⟩
  · apply tendsto_nhds_unique (ht 1)
    simpa only [hfone] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) (ω : Filter ℕ) (𝓝 1))
  · intro x hx
    exact ge_of_tendsto (hre x) (Eventually.of_forall (fun n => hfpos n x hx))
  · intro x
    exact le_antisymm (hle x) (by simpa only [star_star] using hle (star x))

end

/-! Construction of a tracial state on the original concrete finite diffuse factor without a supplied trace. -/
section
open scoped CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.tracialStateCStar
attribute [local instance] OAI.Generator.Tracial.tracialStateOrder
local instance tracialStatePreorder_r5f7020_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.tracialStateLE
attribute [local instance] OAI.Generator.Tracial.tracialStateStarOrder
include hfactor hdiff hfinite in
theorem exists_tracial_state (hunit : (1 : M.toStarSubalgebra) ≠ 0) :
    ∃ φ : M.toStarSubalgebra →L[ℂ] ℂ,
      ‖φ‖ ≤ 1 ∧ φ 1=1 ∧ (∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re) ∧
      (∀ x : M.toStarSubalgebra, φ (star x)=star (φ x)) ∧
      ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x) := by
  obtain ⟨φ,hφ,h1,hpos,hquad⟩ := exists_real_quadratic_state hfactor hdiff hfinite hunit
  refine ⟨hermitianFunctional φ,(hermitianFunctional_norm_le φ).trans hφ,
    hermitianFunctional_one φ h1,?_,hermitianFunctional_star φ,
    hermitianFunctional_trace φ hquad⟩
  intro x hx
  rw [hermitianFunctional_selfAdjoint φ x hx.isSelfAdjoint,Complex.ofReal_re]
  exact hpos x hx

end

/-! Every positive normalized tracial functional agrees with the dimension on
all projections. Lower and upper dyadic bounds use actual partial isometries. -/

/-! Identification of the actual tracial state with the spectral dimension
value, and unrestricted additivity for noncommuting self-adjoint operators. -/

/-! The constructed faithful normalized trace on the original algebra.
Projection-net continuity is proved explicitly; no general normality or
representation theorem is hidden in the definition. -/
section
open Filter
open scoped Topology CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

attribute [local instance] OAI.Generator.Tracial.traceCStar
attribute [local instance] OAI.Generator.Tracial.traceOrder
local instance tracePreorder_r5f7020_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.traceLE
attribute [local instance] OAI.Generator.Tracial.traceStarOrder
def traceFreeTrace : M.toStarSubalgebra →L[ℂ] ℂ :=
  (exists_tracial_state hfactor hdiff hfinite hunit).choose

theorem traceFreeTrace_spec :
    ‖traceFreeTrace hfactor hdiff hfinite hunit‖ ≤ 1 ∧
    traceFreeTrace hfactor hdiff hfinite hunit 1=1 ∧
    (∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (traceFreeTrace hfactor hdiff hfinite hunit x).re) ∧
    (∀ x : M.toStarSubalgebra, traceFreeTrace hfactor hdiff hfinite hunit (star x)=
      star (traceFreeTrace hfactor hdiff hfinite hunit x)) ∧
    ∀ x y : M.toStarSubalgebra, traceFreeTrace hfactor hdiff hfinite hunit (x*y)=
      traceFreeTrace hfactor hdiff hfinite hunit (y*x) :=
  (exists_tracial_state hfactor hdiff hfinite hunit).choose_spec

theorem traceFreeTrace_projection (p : AlgebraProjection M) :
    traceFreeTrace hfactor hdiff hfinite hunit p.val=(traceFreeDimension hfactor hdiff p : ℂ) := by
  obtain ⟨_,h1,hpos,hstar,htrace⟩ := traceFreeTrace_spec hfactor hdiff hfinite hunit
  exact tracialFunctional_projection_dimension hfactor hdiff hfinite hunit _ h1 hpos hstar htrace p

theorem traceFreeTrace_selfAdjoint (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    traceFreeTrace hfactor hdiff hfinite hunit x=
      dimensionSpectralValue hfactor hdiff hfinite hunit x hx :=
  functional_eq_dimensionSpectralValue hfactor hdiff hfinite hunit _
    (traceFreeTrace_spec hfactor hdiff hfinite hunit).1
    (traceFreeTrace_projection hfactor hdiff hfinite hunit) x hx

theorem traceFreeTrace_faithful (x : M.toStarSubalgebra) (hx : 0 ≤ x) :
    traceFreeTrace hfactor hdiff hfinite hunit x=0 ↔ x=0 := by
  rw [traceFreeTrace_selfAdjoint hfactor hdiff hfinite hunit x hx.isSelfAdjoint]
  exact dimensionSpectralValue_eq_zero_iff_of_nonneg hfactor hdiff hfinite hunit x hx

end

/-! The constructed trace is dominated by a finite sum of concrete vector
functionals. The matrix partition is constructed inside the localized corner. -/

/-! Finite vector-functional representation and actual ultraweak continuity of
the constructed trace. No normality criterion is taken as an axiom. -/
open scoped BigOperators CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_WordCorrelation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Ordered prefix cancellation for the actual common perturbed unitary.
All identities are identities of bounded coordinate sequences. -/
namespace Tracial

section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def SuccessiveCoordinateHaar.perturbedWord (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (α : ℝ) : unitary (Sequences M) :=
  F.haarSequence τ ω 0*((List.range ell).map
    (fun k => F.perturbedUnitary τ ω u z ell α*F.haarSequence τ ω (k+1))).prod

end

/-! The exact first-order trace calculation for the manuscript's prefix labels. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def SuccessiveCoordinateHaar.firstOrderTerm
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary (Q τ ω)) (ell : ℕ) (c : ℂ) : Q τ ω :=
  c • ∑ k : Fin ell,∑ j : Fin ell,
    ((F.conjugateUnitary τ ω u z ell (pairLabel k j) : Q τ ω)-
      star (F.conjugateUnitary τ ω u z ell (pairLabel k j) : Q τ ω))

end

/-! The first-order term is exactly the sum of the mapped formal rows, and
its correlation is the manuscript's alpha/2 coefficient. -/

/-! The uniform trace correlation for the actual product of coordinate
exponentials. Identifying that product with a single-unitary perturbation word
is a separate remaining step. -/

/-! The uniform correlation now belongs to the literal word in one common
perturbed unitary, as required by eq:perturbation-prefix. -/
open UltrapowerBridge

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_PerturbationBounds
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Exact 2 ell signed coefficients in each formal row. In particular the
identity prefix label is still a nonidentity basis letter in the formal group. -/

/-! Exact trace-two-norm of the single common logarithmic perturbation. -/
namespace Tracial

/-! Sharp trace-two-norm displacement of a skew-adjoint exponential, via the
real path t ↦ exp(t K). This proves the scalar-calculus estimate used in the
manuscript without an extra exponential factor. -/

/-! A single coordinate satisfies the size and correlation bounds for the
literal word. Its P-valued unitary letters are the retained construction. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def SuccessiveCoordinateHaar.retainedUnitary (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (j n : ℕ) : unitary N.toStarSubalgebra :=
  ⟨(F.step j).coordinates.val n,(F.step j).unitary_coordinates n⟩

end

/-! The manuscript's two perturbation inequalities, constructed under explicit
faithful vector-trace, irreducibility, diffuseness and trace-vector separability
data. No perturbation endpoint or free-moment premise is assumed. -/
open UltrapowerBridge Filter

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_TraceHilbert
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A separate type with the constructed trace inner product. Its norm is the
trace two-norm; the original concrete algebra retains its operator norm.
Lean's inner product is linear in the second argument. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit
local notation "τ₀" => traceFreeTrace hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

attribute [local instance] OAI.Generator.Tracial.traceHilbertCStar
attribute [local instance] OAI.Generator.Tracial.traceHilbertOrder
attribute [local instance] OAI.Generator.Tracial.traceHilbertStarOrder
@[instance_reducible] def traceFreeInnerCore : InnerProductSpace.Core ℂ E where
  inner x y := τ₀ (star ((copy).symm x) * (copy).symm y)
  conj_inner_symm x y := by
    change star (τ₀ (star ((copy).symm y) * (copy).symm x)) = _
    rw [← (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.2.1]
    simp only [star_mul, star_star]
  re_inner_nonneg x :=
    (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.1 _ (star_mul_self_nonneg _)
  add_left x y z := by simp only [map_add, star_add, add_mul]
  smul_left x y c := by
    simp only [map_smul, star_smul, smul_mul_assoc]
    rfl
  definite x hx := by
    have hz := (traceFreeTrace_faithful hfactor hdiff hfinite hunit _
      (star_mul_self_nonneg ((copy).symm x))).mp hx
    have hx' : (copy).symm x = 0 := (CStarRing.star_mul_self_eq_zero_iff _).mp hz
    exact (copy).symm.injective (hx'.trans (map_zero (copy).symm).symm)

instance traceFreePreHilbertNormedAddCommGroup : NormedAddCommGroup E :=
  (traceFreeInnerCore hfactor hdiff hfinite hunit).toNormedAddCommGroup
instance traceFreePreHilbertInnerProductSpace : InnerProductSpace ℂ E :=
  .ofCore { traceFreeInnerCore hfactor hdiff hfinite hunit with }

@[simp] theorem traceFreeCopy_inner (x y : M.toStarSubalgebra) :
    inner ℂ (copy x) (copy y) = τ₀ (star x*y) := rfl

theorem traceFreeCopy_norm_sq (x : M.toStarSubalgebra) :
    ‖copy x‖^2 = (τ₀ (star x*x)).re := by
  rw [← traceFreeCopy_inner hfactor hdiff hfinite hunit]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) (copy x)).symm

/-- The actual Hilbert completion; no representation is supplied. -/
abbrev TraceFreeHilbert := UniformSpace.Completion E

def traceFreeInclusion : E →ₗᵢ[ℂ] TraceFreeHilbert hfactor hdiff hfinite hunit :=
  UniformSpace.Completion.toComplₗᵢ

@[simp] theorem traceFreeInclusion_inner (x y : M.toStarSubalgebra) :
    inner ℂ (traceFreeInclusion hfactor hdiff hfinite hunit (copy x))
      (traceFreeInclusion hfactor hdiff hfinite hunit (copy y)) = τ₀ (star x*y) :=
  UniformSpace.Completion.inner_coe (𝕜 := ℂ) (copy x) (copy y)

theorem traceFreeInclusion_denseRange :
    DenseRange (traceFreeInclusion hfactor hdiff hfinite hunit) :=
  UniformSpace.Completion.denseRange_coe

end

/-! The trace two-norm bound for left multiplication uses the original
operator norm and positivity of a concrete sandwich. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "τ₀" => traceFreeTrace hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

attribute [local instance] OAI.Generator.Tracial.traceHilbertBoundCStar
attribute [local instance] OAI.Generator.Tracial.traceHilbertBoundOrder
attribute [local instance] OAI.Generator.Tracial.traceHilbertBoundPreorder
attribute [local instance] OAI.Generator.Tracial.traceHilbertBoundLE
attribute [local instance] OAI.Generator.Tracial.traceHilbertBoundStarOrder
theorem traceFreeTrace_mul_square_le (a x : M.toStarSubalgebra) :
    (τ₀ (star (a*x)*(a*x))).re ≤ ‖a‖^2 * (τ₀ (star x*x)).re := by
  have hp : 0 ≤ algebraMap ℝ M.toStarSubalgebra (‖a‖^2)-star a*a :=
    sub_nonneg.mpr (CStarAlgebra.star_mul_le_algebraMap_norm_sq)
  have h := (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.1 _
    (star_left_conjugate_nonneg hp x)
  have he : star x*(algebraMap ℝ M.toStarSubalgebra (‖a‖^2)-star a*a)*x =
      (‖a‖^2) • (star x*x)-star (a*x)*(a*x) := by
    simp only [Algebra.algebraMap_eq_smul_one,mul_sub,sub_mul,mul_smul_comm,
      smul_mul_assoc,mul_one,star_mul,mul_assoc]
  rw [he,map_sub, ContinuousLinearMap.map_smul_of_tower, Complex.sub_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  exact sub_nonneg.mp h

theorem traceFreeCopy_mul_norm_le (a x : M.toStarSubalgebra) :
    ‖copy (a*x)‖ ≤ ‖a‖ * ‖copy x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, traceFreeCopy_norm_sq, traceFreeCopy_norm_sq]
  exact traceFreeTrace_mul_square_le hfactor hdiff hfinite hunit a x

end

/-! Bounded left multiplication on the actual constructed trace Hilbert space.
All representation laws are proved on its dense algebraic subspace. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "ι" => traceFreeInclusion hfactor hdiff hfinite hunit
local instance traceHilbertOperatorCStar : CStarAlgebra (K →L[ℂ] K) := {}

def traceFreeLeftOnPreHilbert (a : M.toStarSubalgebra) : E →L[ℂ] E :=
  LinearMap.mkContinuous (LinearMap.mulLeft ℂ (copy a)) ‖a‖ (by
    intro x
    obtain ⟨x,rfl⟩ := (copy).surjective x
    exact traceFreeCopy_mul_norm_le hfactor hdiff hfinite hunit a x)

@[simp] theorem traceFreeLeftOnPreHilbert_apply (a : M.toStarSubalgebra) (x : E) :
    traceFreeLeftOnPreHilbert hfactor hdiff hfinite hunit a x = copy a*x := rfl

def traceFreeLeftAction (a : M.toStarSubalgebra) : K →L[ℂ] K :=
  ((ι).toContinuousLinearMap.comp (traceFreeLeftOnPreHilbert hfactor hdiff hfinite hunit a)).extend
    (ι).toContinuousLinearMap

local notation "L" => traceFreeLeftAction hfactor hdiff hfinite hunit

@[simp] theorem traceFreeLeftAction_inclusion (a : M.toStarSubalgebra) (x : E) :
    L a (ι x) = ι (copy a*x) := by
  exact ContinuousLinearMap.extend_eq
    ((ι).toContinuousLinearMap.comp (traceFreeLeftOnPreHilbert hfactor hdiff hfinite hunit a))
    (e := (ι).toContinuousLinearMap) (traceFreeInclusion_denseRange hfactor hdiff hfinite hunit)
    ((ι).isometry.isUniformInducing) x

@[simp] theorem traceFreeLeftAction_coe (a : M.toStarSubalgebra) (x : E) :
    L a (x : K) = ((copy a*x : E) : K) :=
  traceFreeLeftAction_inclusion hfactor hdiff hfinite hunit a x

@[simp] theorem traceFreeLeftAction_one : L 1 = 1 := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  simp only [traceFreeLeftAction_coe,map_one,one_mul,one_apply_eq_self]

@[simp] theorem traceFreeLeftAction_mul (a b : M.toStarSubalgebra) :
    L (a*b) = L a*L b := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  simp only [mul_apply_eq_comp,traceFreeLeftAction_coe,map_mul,mul_assoc]

attribute [local instance] OAI.Generator.Tracial.traceHilbertActionCStar
local instance traceHilbertActionOrder_r5f7020_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertActionStarOrder_r5f7020_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
@[simp] theorem traceFreeLeftAction_add (a b : M.toStarSubalgebra) :
    L (a+b) = L a+L b := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  simp only [add_apply,traceFreeLeftAction_coe,map_add,add_mul,UniformSpace.Completion.coe_add]

@[simp] theorem traceFreeLeftAction_smul (c : ℂ) (a : M.toStarSubalgebra) :
    L (c • a) = c • L a := by
  apply ContinuousLinearMap.ext
  intro x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (L (c • a)).continuous ((c • L a : K →L[ℂ] K)).continuous) ?_
  intro b
  change L (c • a) (ι b) = c • L a (ι b)
  rw [traceFreeLeftAction_inclusion,traceFreeLeftAction_inclusion,map_smul,smul_mul_assoc]
  exact (ι).map_smul c _

end

/-! Bounded right multiplication and its commutation with the constructed
left action. These supply separation on the actual double commutant. -/

/-! The actual double commutant of the new representation, with a constructed
faithful tracial vector. Equality with the original image is a later theorem. -/

/-! The constructed representation is WOT continuous on every original
operator-norm ball. This does not assert whole-carrier WOT continuity. -/
open scoped ComplexConjugate CStarAlgebra BigOperators

end Generator.Tracial

end

end OAI
end


