-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
-- name    : OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:06:33.963246+00:00
-- url     : https://prove2.me/theorems/82175f27-e540-475d-877f-de64f906be58
-- title:
--   Active Gauss Factorization
-- statement:
--   Definitions and structural lemmas for Active Gauss Factorization, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/ActiveGaussFactorization.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_IdealGenerators
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
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
namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge ConcreteTraceCRT
end ConcretePrimeRowBridge
open scoped BigOperators Classical
namespace ActualEisensteinCubic
def activeSupport {α : Type*} [DecidableEq α] (S T : Finset α) : Finset α :=
  (S \ T) ∪ (T \ S)
abbrev activePrimes {α : Type*} [DecidableEq α]
    (P : α → Ideal O) (S T : Finset α) (i : activeSupport S T) : Ideal O := P i.val
def activeExponent {α : Type*} [DecidableEq α]
    (S T : Finset α) (i : activeSupport S T) : ℕ :=
  if i.val ∈ S \ T then 5 else 1
theorem activePrimes_injective {α : Type*} [DecidableEq α]
    (P : α → Ideal O) (hinj : Function.Injective P) (S T : Finset α) :
    Function.Injective (activePrimes P S T) := by
  intro a b h
  apply Subtype.ext
  exact hinj h
theorem activePrimes_pairwise_isCoprime {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (S T : Finset α) :
    Pairwise (Function.onFun IsCoprime (activePrimes P S T)) := by
  intro a b hab
  exact Ideal.isCoprime_of_isMaximal (fun h => hab (activePrimes_injective P hinj S T h))
open ConcreteTraceCRT EisensteinSchwartzPoisson
noncomputable def squarefreePairPoissonKernel
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  let Q := activePrimes P S T
  let hQ := activePrimes_pairwise_isCoprime P hinj S T
  let row := finiteSexticRow Q (fun i => hgood i.val) (activeExponent S T)
  let c := finitePrimeModulus Q
  ((scale : ℂ) * canonicalNormalizedGauss Q hQ (fun i => hgood i.val)
      (activeExponent S T) / (‖eisEmbedding c‖ : ℂ)) *
    ∑ E ∈ (S ∩ T).powerset,
      let d := primeSubsetGenerator P E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        ∑' h : O, star (row h) * paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding c‖ ^ 2))
end ActualEisensteinCubic
namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge ConcreteTraceCRT EisensteinSchwartzPoisson
noncomputable def idealPairPoissonKernel
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ := by
  letI : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact squarefreePairPoissonKernel (fun i : primePool F => i.1)
    Subtype.val_injective (primePool_good F hFgood)
    (idealSupport F I) (idealSupport F J) W scale
end ConcretePrimeRowBridge
open scoped BigOperators Classical
namespace IdealGaussCRT
end IdealGaussCRT
namespace FiniteGaussPhase
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
def cofactor {ι : Type*} [Fintype ι] (p : ι → O) (i : ι) : O :=
  ∏ k ∈ Finset.univ.erase i, p k
theorem span_finset_prod {ι : Type*} (s : Finset ι) (p : ι → O) :
    Ideal.span {∏ i ∈ s, p i} = ∏ i ∈ s, Ideal.span {p i} := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      ← Ideal.span_singleton_mul_span_singleton, ih]
def productElementCRT {ι : Type*} [Fintype ι]
    (p : ι → O) (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) :
    (O ⧸ Ideal.span {∏ i, p i}) ≃+* ∀ i, O ⧸ Ideal.span {p i} :=
  (Ideal.quotEquivOfEq (span_finset_prod Finset.univ p)).trans
    (IdealGaussCRT.quotientProdEquivPi (fun i => Ideal.span {p i}) hcop)
def normalizedProductTraceGauss {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) : ℂ := by
  let hpall : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  letI : Finite (O ⧸ Ideal.span {∏ i, p i}) := finite_quotient_span hpall
  letI : Fintype (O ⧸ Ideal.span {∏ i, p i}) := Fintype.ofFinite _
  exact (∑ x : O ⧸ Ideal.span {∏ i, p i},
    (∏ i, χ i (productElementCRT p hcop x i)) *
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        (∏ i, p i) hpall x) / (‖eisEmbedding (∏ i, p i)‖ : ℂ)
def canonicalProductGauss {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) : ℂ :=
  normalizedProductTraceGauss p hp hcop (fun i => canonicalSextic (Ideal.span {p i}) (hgood i) ^ j i)
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
def angularFactor (a : O) : ℂ := eisEmbedding a / (‖eisEmbedding a‖ : ℂ)
def canonicalCrossFactor {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) : ℂ :=
  ∏ i, ∏ k ∈ Finset.univ.erase i,
    canonicalSextic (Ideal.span {p i}) (hgood i)
      (Ideal.Quotient.mk (Ideal.span {p i}) (p k))
def canonicalProductCoefficient {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) : ℂ :=
  star (angularFactor (∏ i, p i)) * canonicalProductGauss p hp hcop hgood (fun _ => 2)
def canonicalProductG {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) : ℂ :=
  (∏ i, canonicalSextic (Ideal.span {p i}) (hgood i)
      (Ideal.Quotient.mk (Ideal.span {p i}) (4 : O)))⁻¹ *
    canonicalProductGauss p hp hcop hgood (fun _ => 3)
end FiniteGaussPhase
end
end OAI


