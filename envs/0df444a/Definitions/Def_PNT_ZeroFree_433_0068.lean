-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0068
-- name    : PNT_ZeroFree_433_0068
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T20:42:44.920991+00:00
-- url     : https://prove2.me/theorems/e6c1d9fa-cdfe-4dbb-acd5-5b667e221ec9
-- title:
--   Zero-free region foundations: Reciprocity.RamifiedSymbol [0068]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Reciprocity.RamifiedSymbol
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/RamifiedSymbol.lean#L421-L752

import Definitions.Def_PNT_ZeroFree_433_0068_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/RamifiedSymbol.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

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

open scoped BigOperators Classical

namespace CubicRamified
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss


end CubicRamified

namespace CubicJacobiGlobal
open ActualEisensteinCubic CompletedGauss CubicRamified


end CubicJacobiGlobal

namespace PrimaryIdealUnitReindex
open ActualEisensteinCubic ActualEisensteinCoordinates ShortDraftLatticeCount


def unitCoordinateEquiv : Oˣ ≃ {z : ℤ × ℤ // z ∈ unitCoordinates} :=
  Equiv.ofBijective unitCoordinateMap unitCoordinateMap_bijective

theorem card_units_eq_six : Nat.card Oˣ = 6 := by
  rw [Nat.card_congr unitCoordinateEquiv, Nat.card_eq_fintype_card, Fintype.card_coe]
  norm_num [unitCoordinates]

end PrimaryIdealUnitReindex

open scoped BigOperators Classical SchwartzMap
namespace QuadraticUnitInvariance
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open GaussGeneratorTransport QuadraticGaussRay EisensteinSchwartzPoisson
open PrimaryIdealUnitReindex CompletedGauss

theorem rowCoprimeMask_unit_mul {α : Type*} (R : α → Ideal O)
    (S : Finset α) (u : Oˣ) (z : O) :
    rowCoprimeMask R S (u.val * z) = rowCoprimeMask R S z := by
  simp only [rowCoprimeMask, Ideal.unit_mul_mem_iff_mem _ u.isUnit]

theorem rowCoprimeMask_norm_le_one {α : Type*} (R : α → Ideal O)
    (S : Finset α) (z : O) : ‖rowCoprimeMask R S z‖ ≤ 1 := by
  unfold rowCoprimeMask
  split_ifs <;> simp

theorem masked_two_rows_radial_summable
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (Q : κ → Ideal O) [∀ i, (Q i).IsMaximal] (hgq : ∀ i, lambda ∉ Q i) (k : κ → ℕ)
    (R : α → Ideal O) (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => rowCoprimeMask R S z *
      (finiteSexticRow P hg j z * finiteSexticRow Q hgq k z) *
      W (‖eisEmbedding z‖ ^ 2 / M)) := by
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hM)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _ hW
  intro z
  simp only [norm_mul]
  calc
    _ ≤ 1 * (1 * 1) * ‖W (‖eisEmbedding z‖ ^ 2 / M)‖ := by
      gcongr
      · exact rowCoprimeMask_norm_le_one R S z
      · exact QuadraticInitialBound.finiteSexticRow_norm_le_one P hg j z
      · exact QuadraticInitialBound.finiteSexticRow_norm_le_one Q hgq k z
    _ = _ := by ring

theorem quadratic_pair_lattice_eq_primary_ideal_sum
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (q : κ → O) (hq : ∀ i, q i ≠ 0) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hcopq : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {q i})))
    (hgq : ∀ i, lambda ∉ Ideal.span {q i})
    (hcharq : ∀ i, ringChar (O ⧸ Ideal.span {q i}) ≠ 2)
    (hray : residue (∏ i, p i) = residue (∏ i, q i))
    (R : α → Ideal O) (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, if lambda ∣ z then 0 else rowCoprimeMask R S z *
      (finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) z *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) z) *
      W (‖eisEmbedding z‖ ^ 2 / M)) =
    (Nat.card Oˣ : ℂ) * ∑' I : GoodIdeal,
      rowCoprimeMask R S (primaryGenerator I.val) *
      (finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) (primaryGenerator I.val) *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) (primaryGenerator I.val)) *
      W ((Ideal.absNorm I.val : ℝ) / M) := by
  have hs := masked_two_rows_radial_summable (fun i => Ideal.span {p i}) hg (fun _ => 3)
    (fun i => Ideal.span {q i}) hgq (fun _ => 3) R S W M hM
  have hu (u : Oˣ) (I : GoodIdeal) :
      rowCoprimeMask R S (u.val * primaryGenerator I.val) *
      (finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) (u.val * primaryGenerator I.val) *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) (u.val * primaryGenerator I.val)) *
      W (‖eisEmbedding (u.val * primaryGenerator I.val)‖ ^ 2 / M) =
      rowCoprimeMask R S (primaryGenerator I.val) *
      (finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) (primaryGenerator I.val) *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) (primaryGenerator I.val)) *
      W (‖eisEmbedding (primaryGenerator I.val)‖ ^ 2 / M) := by
    rw [rowCoprimeMask_unit_mul, quadratic_pair_unit_invariant p hp hcop hg hchar
      q hq hcopq hgq hcharq hray, norm_eisEmbedding_unit_mul]
  have ht := tsum_ramified_mask_unit_invariant _ hs hu
  have hn (I : GoodIdeal) := primaryGenerator_norm_sq I.val I.property
  simpa only [hn] using ht

end QuadraticUnitInvariance

namespace GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase

theorem canonical_masked_radial_poisson_product
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (R : α → Ideal O) [∀ i, (R i).IsMaximal] (hinj : Function.Injective R) (S : Finset α)
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask R S z * finiteSexticRow (fun i => Ideal.span {p i}) hg j z *
      W (‖eisEmbedding z‖ ^ 2 / M)) =
    ((M : ℂ) * canonicalProductGauss p hp hcop hg j / (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
      ∑ E ∈ S.powerset,
        let d := primeSubsetGenerator R E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) *
          finiteSexticRow (fun i => Ideal.span {p i}) hg j d / (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hg j h) *
          paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding (∏ i, p i)‖ ^ 2)) := by
  have ht := canonical_masked_radial_poisson_collected R hinj S
    (fun i => Ideal.span {p i}) hcop hg hchar j hj0 hj6 W M hM
  dsimp only at ht
  rw [finitePrimeModulus_norm_eq_product p] at ht
  rw [ht]
  let a : Finset α → ℂ := fun E =>
    (UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) *
      finiteSexticRow (fun i => Ideal.span {p i}) hg j (primeSubsetGenerator R E) /
      (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 : ℝ)
  let F : Finset α → ℝ → ℂ := fun E t => paperRadialFourier W
    (M * t / (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 * ‖eisEmbedding (∏ i, p i)‖ ^ 2))
  have hu := gauss_weighted_finite_radial_sum_transport p hp hcop hg j S.powerset a F
  change ((M : ℂ) * canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hg j /
      (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
        (∑ E ∈ S.powerset, a E * ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hg j h) *
          F E (‖eisEmbedding h‖ ^ 2)) = _
  calc
    _ = ((M : ℂ) / (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
      (canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hg j *
        ∑ E ∈ S.powerset, a E * ∑' h : O,
          star (finiteSexticRow (fun i => Ideal.span {p i}) hg j h) * F E (‖eisEmbedding h‖ ^ 2)) := by ring
    _ = _ := by rw [hu]; ring
end GaussGeneratorTransport

namespace QuadraticUnitInvariance
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open QuadraticGaussRay MixedCrossSeparation QuadraticInitialBound
open GaussGeneratorTransport EisensteinSchwartzPoisson

theorem odd_of_quadraticRayValue_norm_eq_one (r : EisensteinEPrimaryPhase.Coord)
    (hr : ‖quadraticRayValue r‖ = 1) : EisensteinEPrimaryPhase.odd r := by
  rcases r with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [EisensteinEPrimaryPhase.odd, quadraticRayValue, breveGaussianFourTerms_formula,
      zpow_neg, Complex.I_sq, Complex.I_pow_three, Complex.inv_I, ZMod.val] at *

theorem quadraticBlock_union_eq_one_of_same_ray
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (A B : Finset ι) (hd : Disjoint A B)
    (hray : residue (∏ i ∈ A, p i) = residue (∏ i ∈ B, p i)) :
    quadraticBlock p hp hg (A ∪ B) = 1 := by
  have hnorm := norm_quadraticBlock p hp hcop hg hchar A
  rw [quadraticBlock_eq_rayValue p hp hcop hg hchar A] at hnorm
  have hodd := odd_of_quadraticRayValue_norm_eq_one _ hnorm
  rw [quadraticBlock_eq_rayValue p hp hcop hg hchar (A ∪ B), Finset.prod_union hd]
  exact quadraticRayValue_same_residue_product _ _ hodd hray

theorem same_ray_quadratic_pair_poisson
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (R : α → Ideal O) [∀ i, (R i).IsMaximal] (hinj : Function.Injective R) (S : Finset α)
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (A B : Finset ι) (hd : Disjoint A B)
    (hray : residue (∏ i ∈ A, p i) = residue (∏ i ∈ B, p i))
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    let n := ∏ i ∈ A ∪ B, p i
    let χ := fun z => quadraticRow (fun i => Ideal.span {p i}) hg A z *
      quadraticRow (fun i => Ideal.span {p i}) hg B z
    (∑' z : O, rowCoprimeMask R S z * χ z * W (‖eisEmbedding z‖ ^ 2 / M)) =
      ((M : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
        ∑ E ∈ S.powerset,
          let d := primeSubsetGenerator R E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
            (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, χ h * paperRadialFourier W
            (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) := by
  have hcAB : Pairwise (Function.onFun IsCoprime
      (fun i : (A ∪ B : Finset ι) => Ideal.span {p i.val})) := by
    intro i k hik
    exact hcop (fun h => hik (Subtype.ext h))
  have ht := canonical_masked_radial_poisson_product R hinj S
    (fun i : (A ∪ B : Finset ι) => p i.val) (fun i => hp i.val) hcAB
    (fun i => hg i.val) (fun i => hchar i.val) (fun _ => 3)
    (fun _ => by decide) (fun _ => by decide) W M hM
  have hγ := quadraticBlock_union_eq_one_of_same_ray p hp hcop hg hchar A B hd hray
  rw [quadraticBlock_eq_productGauss p hp hcop hg (A ∪ B)] at hγ
  rw [hγ, mul_one, Finset.prod_coe_sort] at ht
  have hrow (z : O) : finiteSexticRow (fun i : (A ∪ B : Finset ι) => Ideal.span {p i.val})
      (fun i => hg i.val) (fun _ => 3) z =
      quadraticRow (fun i => Ideal.span {p i}) hg A z *
        quadraticRow (fun i => Ideal.span {p i}) hg B z := by
    rw [← quadraticRow_eq_canonical (fun i => Ideal.span {p i}) hg (A ∪ B) z,
      quadraticRow_disjoint_union _ _ _ _ hd]
  simp only [hrow, star_mul, quadraticRow_star] at ht
  simpa only [mul_comm] using ht

end QuadraticUnitInvariance

open scoped BigOperators Classical SchwartzMap
namespace EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT

theorem paperRadialFourier_nonzero_lattice_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K : ℝ), 1 ≤ K →
        (∑' h : {h : O // h ≠ 0}, ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + K) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W K hK
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let F : O → ℝ := fun h => ‖paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)‖
  have hs := paperRadialFourier_lattice_summable_norm W K hK0
  let f : {h : O // h ≠ 0} → {h : O // K ≤ K * ‖eisEmbedding h‖ ^ 2} :=
    fun h => ⟨h.val, by nlinarith [one_le_eisenstein_norm_sq h.val h.property]⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg
      (fun z : {h : O // K ≤ K * ‖eisEmbedding h‖ ^ 2} => z.val) hab)
  have hi : (∑' h : {h : O // h ≠ 0}, F h.val) ≤
      ∑' h : {h : O // K ≤ K * ‖eisEmbedding h‖ ^ 2}, F h.val := by
    exact (hs.subtype (fun h => h ≠ 0)).tsum_le_tsum_of_inj f hf
      (fun _ _ => norm_nonneg _) (fun _ => le_rfl) (hs.subtype _)
  have ht := hb W K K hK0 hK0.le
  simpa only [min_eq_left hK, one_pow, one_mul] using hi.trans ht

theorem paperRadialFourier_nonzero_sum_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K : ℝ), 1 ≤ K →
        ‖∑' h : O, if h = 0 then 0 else paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + K) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_nonzero_lattice_decay A
  refine ⟨s, C, hC, ?_⟩
  intro W K hK
  have hs := paperRadialFourier_lattice_summable_norm W K (lt_of_lt_of_le zero_lt_one hK)
  have he : (∑' h : O, if h = 0 then 0 else paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)) =
      ∑' h : {h : O // h ≠ 0}, paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2) := by
    rw [← tsum_subtype_eq_of_support_subset (s := {h : O | h ≠ 0}) (by
      intro h hh hz
      subst h
      exact hh (by simp))]
    apply tsum_congr
    intro h
    simp only [if_neg h.property]
  rw [he]
  exact (norm_tsum_le_tsum_norm (hs.subtype _)).trans (hb W K hK)

theorem principal_tail_scalar (A : ℕ) (B x N M : ℝ)
    (hB : 0 ≤ B) (hx : 0 < x) (hxN : x ≤ N) (hM : 0 < M) :
    (M / x) * (B / (1 + M / x) ^ (A + 1)) ≤ B * (N / M) ^ A := by
  have hu : 0 < M / x := div_pos hM hx
  calc
    _ ≤ (M / x) * (B / (M / x) ^ (A + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hu.le
      exact div_le_div_of_nonneg_left hB (pow_pos hu _) (pow_le_pow_left₀ hu.le (by linarith) _)
    _ = B * (x / M) ^ A := by
      simp only [div_pow, pow_succ]
      field_simp

    _ ≤ B * (N / M) ^ A := by
      gcongr

theorem maskedPrincipalRemainder_large_scale (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (P : α → Ideal O) [∀ i, (P i).IsMaximal]
        (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ), 0 < M →
        (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) ≤ M →
        ‖maskedPrincipalRemainder P S W M‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
            ((Ideal.absNorm (∏ i ∈ S, P i) : ℝ) / M) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_nonzero_sum_decay (A + 1)
  refine ⟨s, C, hC, ?_⟩
  intro α _ P _ S W M hM hsize
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let N := (Ideal.absNorm (∏ i ∈ S, P i) : ℝ)
  let n := fun E : Finset α => (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hn (E : Finset α) : 0 < n E := by
    dsimp [n]
    rw [← primeSubsetGenerator_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E)))
  have hnN (E : Finset α) (hE : E ∈ S.powerset) : n E ≤ N := by
    have hd := Finset.prod_dvd_prod_of_subset E S P (Finset.mem_powerset.mp hE)
    have hdN := map_dvd Ideal.absNorm hd
    have hpos : 0 < Ideal.absNorm (∏ i ∈ S, P i) := by
      have hh := hn S
      dsimp only [n] at hh
      exact_mod_cast hh
    dsimp only [n, N]
    exact_mod_cast Nat.le_of_dvd hpos hdN
  have ht (E : Finset α) (hE : E ∈ S.powerset) :
      ‖∑' h : O, if h = 0 then 0 else paperRadialFourier W
        (M * ‖eisEmbedding h‖ ^ 2 / n E)‖ ≤ B / (1 + M / n E) ^ (A + 1) := by
    have hscale : 1 ≤ M / n E := (le_div_iff₀ (hn E)).mpr (by simpa using (hnN E hE).trans hsize)
    have h := hb W (M / n E) hscale
    convert! h using 1 ; congr 2 ; funext z ; congr 2 ; ring
  let f := fun E : Finset α =>
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
      (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) *
    ∑' h : O, if h = 0 then 0 else paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / n E)
  have hf (E : Finset α) (hE : E ∈ S.powerset) :
      ‖f E‖ ≤ (1 / n E) * (B / (1 + M / n E) ^ (A + 1)) := by
    dsimp [f]
    rw [norm_mul, norm_div, Complex.norm_natCast]
    gcongr
    · exact QuadraticInitialBound.norm_ideal_moebius_le_one _
    · exact ht E hE
  change ‖(M : ℂ) * ∑ E ∈ S.powerset, f E‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  calc
    _ ≤ M * ∑ E ∈ S.powerset, ‖f E‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hM.le
    _ ≤ M * ∑ E ∈ S.powerset, (1 / n E) * (B / (1 + M / n E) ^ (A + 1)) := by
      gcongr with E hE
      exact hf E hE
    _ = ∑ E ∈ S.powerset, (M / n E) * (B / (1 + M / n E) ^ (A + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _
      ring
    _ ≤ ∑ E ∈ S.powerset, B * (N / M) ^ A := by
      apply Finset.sum_le_sum
      intro E hE
      exact principal_tail_scalar A B (n E) N M hB (hn E) (hnN E hE) hM
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

end EisensteinSchwartzPoisson

end

end OAI

end


