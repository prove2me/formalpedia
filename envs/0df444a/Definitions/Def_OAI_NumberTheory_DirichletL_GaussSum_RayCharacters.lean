-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RayCharacters
-- name    : OAI_NumberTheory_DirichletL_GaussSum_RayCharacters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:21:37.950204+00:00
-- url     : https://prove2.me/theorems/b0308a7d-debc-464a-b8ac-6fc89ac6adae
-- title:
--   Ray Characters
-- statement:
--   Definitions and structural lemmas for Ray Characters, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/RayCharacters.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedExpansion
set_option autoImplicit false
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
namespace RayFourExpansion
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase QuadraticGaussRay
open ActualEisensteinCoordinates MixedCrossSeparation
end RayFourExpansion
namespace MixedCrossSeparation
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open QuadraticGaussRay ActualEisensteinCoordinates GaussGeneratorTransport
end MixedCrossSeparation
namespace FirstCauchyArithmetic
section
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic CoprimeMobiusExtension
def supportMobius {ι : Type*} (P : ι → Ideal O) (S : Finset ι) : ℂ :=
  (UniqueFactorizationMonoid.moebius (∏ i ∈ S, P i) : ℂ)
def supportConjugateSum {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (B : Finset ι) (C : Finset ι → ℂ) (h : O) : ℂ :=
  ∑ S ∈ B.powerset, supportMobius P S * C S * star (finiteSquarefreeRow P hg S h)
end
section
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedCrossSeparation RayFourExpansion
def supportRay {ι : Type*} (p : ι → O) (χ : RayCharacter) (S : Finset ι) : ℂ :=
  rayCharacter χ (∏ i ∈ S, p i)
end
open ActualEisensteinCubic ConcretePrimeRowBridge
theorem family_prime {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (i : ι) :
    Prime (P i) := Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
theorem family_prod_ne_zero {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset ι) :
    (∏ i ∈ S, P i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (family_prime P i).ne_zero)
def supportIdealFamily {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (B : Finset ι) : Finset (Ideal O) :=
  B.powerset.image (fun S => ∏ i ∈ S, P i)
theorem supportIdealFamily_pos {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (B : Finset ι) :
    ∀ I ∈ supportIdealFamily P B, I ≠ ⊥ := by
  intro I hI
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hI
  exact family_prod_ne_zero P S
theorem factor_family_product_iff {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset ι) (Q : Ideal O) :
    Q ∈ UniqueFactorizationMonoid.normalizedFactors (∏ i ∈ S, P i) ↔
      ∃ i ∈ S, Q = P i := by
  rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff (family_prod_ne_zero P S)]
  constructor
  · rintro ⟨hQ, hd⟩
    obtain ⟨i, hi, hdiv⟩ := (hQ.dvd_finsetProd_iff P).mp hd
    exact ⟨i, hi, associated_iff_eq.mp (hQ.associated_of_dvd (family_prime P i) hdiv)⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨family_prime P i, Finset.dvd_prod_of_mem P hi⟩
theorem supportIdealFamily_good {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (B : Finset ι) :
    ∀ I ∈ supportIdealFamily P B,
      ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ Q := by
  intro I hI Q hQ
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨i, hi, rfl⟩ := (factor_family_product_iff P S Q).mp hQ
  exact hg i
def recoveredSupport {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (B : Finset ι) (I : Ideal O) : Finset ι :=
  B.filter (fun i => P i ∣ I)
end FirstCauchyArithmetic
end
end OAI


