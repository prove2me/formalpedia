-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
-- name    : OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:09:25.909431+00:00
-- url     : https://prove2.me/theorems/f69236ba-9a52-44c5-be57-744e8ebfba5e
-- title:
--   Cubic Trace
-- statement:
--   Definitions and structural lemmas for Cubic Trace, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CubicTrace.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_norm_sq_eq_absNorm_span
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
namespace ActualEisensteinCubic
end ActualEisensteinCubic
namespace CubicFrobenius
end CubicFrobenius
namespace ActualEisensteinCubic
end ActualEisensteinCubic
open scoped BigOperators Classical SchwartzMap ContDiff
namespace GaussGeneratorTransport
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase
theorem norm_eisEmbedding_unit (u : Oˣ) : ‖eisEmbedding (u : O)‖ = 1 := by
  have h := eisEmbedding_norm_sq_eq_absNorm_span (u : O)
  rw [Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.absNorm_top, Nat.cast_one] at h
  nlinarith [norm_nonneg (eisEmbedding (u : O))]
@[simp] theorem norm_eisEmbedding_unit_mul (u : Oˣ) (a : O) :
    ‖eisEmbedding ((u : O) * a)‖ = ‖eisEmbedding a‖ := by
  rw [map_mul, norm_mul, norm_eisEmbedding_unit, one_mul]
def principalNormalizedGauss {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i) (hc0 : c ≠ 0) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  exact (∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r *
    eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc0 r) /
      (‖eisEmbedding c‖ : ℂ)
theorem exists_modulus_unit {ι : Type*} [Fintype ι] (p : ι → O) :
    ∃ u : Oˣ, finitePrimeModulus (fun i => Ideal.span {p i}) = (u : O) * ∏ i, p i := by
  have hs : Ideal.span {∏ i, p i} =
      Ideal.span {finitePrimeModulus (fun i => Ideal.span {p i})} := by
    rw [span_finitePrimeModulus, span_finset_prod]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs
  exact ⟨u, by simpa only [mul_comm] using hu.symm⟩
def modulusUnit {ι : Type*} [Fintype ι] (p : ι → O) : Oˣ :=
  Classical.choose (exists_modulus_unit p)
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase
def squarefreePairProductPoissonKernel
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  let q : activeSupport S T → O := fun i => p i.val
  let Q := activePrimes (fun i => Ideal.span {p i}) S T
  let hQ := activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T
  let row := finiteSexticRow Q (fun i => hgood i.val) (activeExponent S T)
  let n := ∏ i, q i
  ((scale : ℂ) * canonicalProductGauss q (fun i => hp i.val) hQ
      (fun i => hgood i.val) (activeExponent S T) / (‖eisEmbedding n‖ : ℂ)) *
    ∑ E ∈ (S ∩ T).powerset,
      let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * row d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        ∑' h : O, star (row h) * paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))
end GaussGeneratorTransport
end
end OAI


