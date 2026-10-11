-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0079_1
-- name    : PNT_ZeroFree_433_0079_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:16:46.860564+00:00
-- url     : https://prove2.me/theorems/9d55b145-2779-453a-8d33-57c91c98462c
-- title:
--   Zero-free region foundations: CubicSieve.ChildTransfer [0079_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.ChildTransfer
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ChildTransfer.lean#L254-L379

import Definitions.Def_PNT_ZeroFree_433_0079_1_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ChildTransfer.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

namespace SecondPassArithmetic

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

section

open scoped BigOperators Classical


section
open ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hg

theorem commonProduct_mask
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (U G : Finset ι) :
    rowCoprimeMask (fun i => Ideal.span {p i}) U (∏ i ∈ G, p i) =
      if Disjoint U G then 1 else 0 := by
  by_cases hd : Disjoint U G
  · rw [if_pos hd, FirstPassCubeLabels.mask_prod _ hg U G p]
    apply Finset.prod_eq_one
    intro j hj
    have hh : ¬ ∃ i ∈ U, p j ∈ Ideal.span {p i} := by
      rintro ⟨i, hi, hpi⟩
      have hij : i ≠ j := fun he => Finset.disjoint_left.mp hd hi (he ▸ hj)
      exact (prime_generator_not_mem_of_ne (Ideal.span {p i}) (Ideal.span {p j})
        (fun he => hij (hinj he)) (p j) rfl) hpi
    simp [rowCoprimeMask, hh]
  · rw [if_neg hd]
    obtain ⟨i, hiU, hiG⟩ := Finset.not_disjoint_iff.mp hd
    have hh : ∃ j ∈ U, (∏ i ∈ G, p i) ∈ Ideal.span {p j} :=
      ⟨i, hiU, Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem p hiG)⟩
    simp [rowCoprimeMask, hh]

theorem sum_remove_common_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (A : Finset ι → ℂ) :
    (∑ U ∈ (F \ G).powerset, A U) =
      ∑ U ∈ F.powerset, rowCoprimeMask (fun i => Ideal.span {p i}) U (∏ i ∈ G, p i) * A U := by
  have hsub : (F \ G).powerset ⊆ F.powerset := Finset.powerset_mono.mpr Finset.sdiff_subset
  calc
    _ = ∑ U ∈ (F \ G).powerset,
        rowCoprimeMask (fun i => Ideal.span {p i}) U (∏ i ∈ G, p i) * A U := by
      apply Finset.sum_congr rfl
      intro U hU
      have hd : Disjoint U G := Finset.disjoint_left.mpr (fun i hi hG =>
        (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hU) hi)).2 hG)
      rw [commonProduct_mask p hg hinj U G, if_pos hd, one_mul]
    _ = _ := by
      apply Finset.sum_subset hsub
      intro U hUF hUG
      have hd : ¬ Disjoint U G := by
        intro hd
        apply hUG
        apply Finset.mem_powerset.mpr
        intro i hi
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hUF) hi,
          fun hG => Finset.disjoint_left.mp hd hi hG⟩
      rw [commonProduct_mask p hg hinj U G, if_neg hd, zero_mul]

omit [DecidableEq ι] in
theorem secondInputCoefficient_fixed_mask (Ψ : O →* ℂ) (m g c d : O)
    (H : Finset ι → ℂ) (U : Finset ι) :
    secondInputCoefficient p hg Ψ (m*g) c d H U =
      rowCoprimeMask (fun i => Ideal.span {p i}) U g * secondInputCoefficient p hg Ψ m c d H U := by
  rw [secondInputCoefficient, FirstPassCubeLabels.mask_mul _ hg U m g]
  unfold secondInputCoefficient
  ring

theorem inputConjugateRow_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ) (z : O) :
    inputConjugateRow p hg (F \ G) Ψ m c d H z =
      inputConjugateRow p hg F Ψ (m * ∏ i ∈ G, p i) c d H z := by
  unfold inputConjugateRow FirstCauchyArithmetic.supportConjugateSum
  rw [sum_remove_common_pool p hg hinj F G]
  apply Finset.sum_congr rfl
  intro U hU
  rw [secondInputCoefficient_fixed_mask]
  ring

end

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hg

theorem sum_pair_remove_common_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (A : Finset ι → Finset ι → ℂ) :
    (∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset, A U V) =
      ∑ U ∈ F.powerset, ∑ V ∈ F.powerset,
        rowCoprimeMask (fun i => Ideal.span {p i}) U (∏ i ∈ G, p i) *
        rowCoprimeMask (fun i => Ideal.span {p i}) V (∏ i ∈ G, p i) * A U V := by
  rw [sum_remove_common_pool p hg hinj F G]
  apply Finset.sum_congr rfl
  intro U hU
  rw [sum_remove_common_pool p hg hinj F G, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro V hV
  ring

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] hg in
lemma star_mask (P : ι → Ideal O) (S : Finset ι) (a : O) :
    star (rowCoprimeMask P S a) = rowCoprimeMask P S a := by
  unfold rowCoprimeMask
  split_ifs <;> simp

theorem input_pair_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ) :
    (∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
      if Disjoint U V then
        star (supportMobius (fun i => Ideal.span {p i}) U * secondInputCoefficient p hg Ψ₁ m c d H₁ U) *
        (supportMobius (fun i => Ideal.span {p i}) V * secondInputCoefficient p hg Ψ₂ m c d H₂ V) * K U V
      else 0) =
    ∑ U ∈ F.powerset, ∑ V ∈ F.powerset,
      if Disjoint U V then
        star (supportMobius (fun i => Ideal.span {p i}) U *
          secondInputCoefficient p hg Ψ₁ (m * ∏ i ∈ G, p i) c d H₁ U) *
        (supportMobius (fun i => Ideal.span {p i}) V *
          secondInputCoefficient p hg Ψ₂ (m * ∏ i ∈ G, p i) c d H₂ V) * K U V
      else 0 := by
  rw [sum_pair_remove_common_pool p hg hinj F G]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  by_cases hd : Disjoint U V
  · rw [if_pos hd, if_pos hd, secondInputCoefficient_fixed_mask,
      secondInputCoefficient_fixed_mask]
    simp only [star_mul, star_mask]
    ring
  · simp [hd]


end


end


end SecondPassArithmetic

end

end OAI

end


