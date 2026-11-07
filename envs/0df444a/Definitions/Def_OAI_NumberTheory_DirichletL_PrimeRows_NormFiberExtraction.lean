-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
-- name    : OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:17:26.604534+00:00
-- url     : https://prove2.me/theorems/5cda626b-e207-47ce-bf4a-ee25ab359cd1
-- title:
--   Norm Fiber Extraction
-- statement:
--   Definitions and structural lemmas for Norm Fiber Extraction, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/NormFiberExtraction.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


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
namespace ConcretePrimeRowBridge
section
open ActualEisensteinCubic ShortDraftHeckeBridge
abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K
instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
instance : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K
noncomputable def idealGenerator (I : Ideal O) : O :=
  Submodule.IsPrincipal.generator I
noncomputable def idealsUpTo (D : ℕ) : Finset (Ideal O) :=
  (Finset.Icc 1 D).biUnion
    (fun n => (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset)
theorem mem_idealsUpTo {D : ℕ} {I : Ideal O} :
    I ∈ idealsUpTo D ↔ 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D := by
  classical
  simp [idealsUpTo, Finset.mem_biUnion, Finset.mem_Icc]
noncomputable def columnsUpTo (D : ℕ) : Finset O :=
  by
    classical
    exact (idealsUpTo D).image idealGenerator
noncomputable def columnWeight {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (x : O) : ℂ :=
  baseChangeWeight χ (Ideal.span {x}) * W (Ideal.absNorm (Ideal.span {x}))
noncomputable def goodLambda : O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1
noncomputable def primePool (F : Finset (Ideal O)) : Finset (Ideal O) :=
  F.biUnion (fun I => (UniqueFactorizationMonoid.normalizedFactors I).toFinset)
theorem mem_primePool_iff {F : Finset (Ideal O)} {P : Ideal O} :
    P ∈ primePool F ↔
      ∃ I ∈ F, P ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  classical
  simp only [primePool, Finset.mem_biUnion, Multiset.mem_toFinset]
theorem primePool_maximal (F : Finset (Ideal O))
    (_hFpos : ∀ I ∈ F, I ≠ ⊥) (i : primePool F) :
    (i.1).IsMaximal := by
  obtain ⟨I, hIF, hfac⟩ := mem_primePool_iff.mp i.property
  have hp : Prime i.1 := UniqueFactorizationMonoid.prime_of_normalized_factor i.1 hfac
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
theorem primePool_good (F : Finset (Ideal O))
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (i : primePool F) : goodLambda ∉ i.1 := by
  obtain ⟨I, hIF, hfac⟩ := mem_primePool_iff.mp i.property
  exact hFgood I hIF i.1 hfac
noncomputable def idealSupport (F : Finset (Ideal O)) (I : Ideal O) :
    Finset (primePool F) :=
  Finset.univ.filter (fun i => i.1 ∈ UniqueFactorizationMonoid.normalizedFactors I)
noncomputable def idealSexticRow
    (F : Finset (Ideal O))
    (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (I : Ideal O) (u : O) : ℂ := by
  letI : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact ActualEisensteinCubic.finiteSquarefreeRow
    (fun i : primePool F => i.1) (primePool_good F hFgood)
    (idealSupport F I) u
noncomputable def elementRow
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (u : O) : ℂ := by
  classical
  letI : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact ∑ x ∈ F.image idealGenerator,
    columnWeight χ W x *
      finiteSquarefreeRow (fun i : primePool F => i.1)
        (primePool_good F hFgood)
        (idealSupport F (Ideal.span {x})) u
noncomputable def idealRowSum
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (u : O) : ℂ :=
  ∑ I ∈ F,
    baseChangeWeight χ I * W (Ideal.absNorm I) *
      idealSexticRow F hFpos hFgood I u
open ActualEisensteinCubic ShortDraftHeckeBridge
open scoped Classical
noncomputable def rowNormDisk (H : ℕ) : Finset O := by
  classical
  exact (ShortDraftLatticeCount.rowNormBall H).filter
    (fun u => 0 < Ideal.absNorm (Ideal.span {u}) ∧
      Ideal.absNorm (Ideal.span {u}) ≤ H)
end
open ShortDraftHeckeBridge FiniteSFactor
noncomputable def outsideIdealsUpTo (S : Finset (Ideal O)) (D : ℕ) :
    Finset (Ideal O) := by
  classical
  exact (idealsUpTo D).filter (fun I => ∀ P ∈ S, ¬ P ∣ I)
theorem mem_outsideIdealsUpTo {S : Finset (Ideal O)} {D : ℕ}
    {I : Ideal O} :
    I ∈ outsideIdealsUpTo S D ↔
      1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D ∧
        (∀ P ∈ S, ¬ P ∣ I) := by
  classical
  simp [outsideIdealsUpTo, mem_idealsUpTo, and_assoc]
theorem outsideIdealsUpTo_ne_bot (S : Finset (Ideal O)) (D : ℕ)
    (I : Ideal O) (hI : I ∈ outsideIdealsUpTo S D) : I ≠ ⊥ := by
  have hn := (mem_outsideIdealsUpTo.mp hI).1
  intro h
  subst I
  simp at hn
theorem outsideIdealsUpTo_good
    (S : Finset (Ideal O)) (D : ℕ)
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (I : Ideal O) (hI : I ∈ outsideIdealsUpTo S D)
    (Q : Ideal O) (hQ : Q ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    goodLambda ∉ Q := by
  intro hmemLam
  have hne : I ≠ ⊥ := outsideIdealsUpTo_ne_bot S D I hI
  have hp : Prime Q := UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ
  have hmax : Q.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hQS : Q ∈ S := hSbad Q hmax hmemLam
  have hdiv : Q ∣ I := (Ideal.dvd_iff_le).mpr
    ((Ideal.mem_normalizedFactors_iff hne).mp hQ).2
  exact (mem_outsideIdealsUpTo.mp hI).2.2 Q hQS hdiv
open ShortDraftHeckeBridge FiniteSFactor Filter
end ConcretePrimeRowBridge
end
end OAI


