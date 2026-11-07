-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_FiniteOperator
-- name    : OAI_NumberTheory_DirichletL_QuadraticSieve_FiniteOperator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:10:36.780217+00:00
-- url     : https://prove2.me/theorems/3e0df6ef-545d-46a9-9c43-c0d45582d14c
-- title:
--   Finite Operator
-- statement:
--   Definitions and structural lemmas for Finite Operator, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/FiniteOperator.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_SquarefreeDivisors
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply


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
open scoped BigOperators
namespace FiniteSieveOperator
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
def operator (A : Matrix m n ℂ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
  A.toEuclideanLin.toContinuousLinearMap
omit [DecidableEq m] in
@[simp] theorem operator_apply (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) (i : m) :
    operator A x i = ∑ j, A i j * x j := rfl
end FiniteSieveOperator
section
open scoped BigOperators Classical
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT RayFourExpansion
def quadraticMatrix {ι m n : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (rows : m → Finset ι) (cols : n → Finset ι) : Matrix m n ℂ :=
  fun i j => quadraticSymbol p hg (cols j) (rows i)
def quadraticSieveNorm {ι m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (rows : m → Finset ι) (cols : n → Finset ι) : ℝ :=
  ‖FiniteSieveOperator.operator (quadraticMatrix p hg rows cols)‖ ^ 2
end QuadraticInitialBound
open scoped BigOperators Classical
open Filter IdealMobiusDivisorSum UniqueFactorizationMonoid
namespace IdealDivisorBound
abbrev O := ActualEisensteinCubic.O
end IdealDivisorBound
end
namespace SecondPassFiber
open scoped BigOperators Classical
open IdealMobiusDivisorSum ConcretePrimeRowBridge
abbrev O := ActualEisensteinCubic.O
@[ext] structure OldTuple where
  core : Fin 8 → Ideal O
  v : Ideal O
  j2 : Ideal O
  b2 : Ideal O
  row : O
structure Valid (x : OldTuple) (F b0 : Ideal O) (y : O) : Prop where
  label : x.core 0 * x.core 1 * x.core 2 * x.v = F
  j_split : x.core 3 * x.j2 = x.core 0
  b_split : x.core 4 * x.b2 = b0 ^ 2 * x.j2 ^ 2 * x.core 3
  a1 : x.core 5 ∣ x.core 4 * x.b2
  a2 : x.core 6 ∣ x.core 4 * x.b2
  d : x.core 7 ∣ F * b0
  row_eq : idealGenerator (x.core 7) * idealGenerator (x.core 2) * x.row = y
def divisorTarget (F b0 : Ideal O) : Ideal O := (F * b0) ^ 2
def newLabel (x : OldTuple) : Ideal O := x.core 0 * x.core 1 * x.core 2 * x.v
def newRow (x : OldTuple) : O :=
  idealGenerator (x.core 7) * idealGenerator (x.core 2) * x.row
end SecondPassFiber
open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic
def cubePairLocal (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (m₁ m₂ : ℕ) (ε₁ ε₂ : Bool) (z : O) : ℂ :=
  let q := canonicalSextic P hg (Ideal.Quotient.mk P z)
  q ^ bit ε₁ * star (q ^ bit ε₂) * q ^ (3 * m₁) * star (q ^ (3 * m₂))
def cubeConductorSupport {κ : Type*} (B : Finset κ) (v₁ v₂ : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : Finset κ :=
  B.filter (fun j => conductorExponent (parity (v₁ j + v₂ j)) (ε₁ j) (ε₂ j) ≠ 0)
def cubePrincipalSupport {κ : Type*} (B : Finset κ) (v₁ v₂ : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : Finset κ :=
  B.filter (fun j => conductorExponent (parity (v₁ j + v₂ j)) (ε₁ j) (ε₂ j) = 0)
def multiplicityRow {κ : Type*} (P : κ → Ideal O) [∀ j, (P j).IsMaximal]
    (hg : ∀ j, lambda ∉ P j) (B : Finset κ) (v : κ → ℕ) (z : O) : ℂ :=
  ∏ j ∈ B, canonicalSextic (P j) (hg j) (Ideal.Quotient.mk (P j) z) ^ v j
def cubePairRow {κ : Type*} (P : κ → Ideal O) [∀ j, (P j).IsMaximal]
    (hg : ∀ j, lambda ∉ P j) (B : Finset κ) (v₁ v₂ : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (z : O) : ℂ :=
  finiteSquarefreeRow P hg (B.filter fun j => ε₁ j) z *
    star (finiteSquarefreeRow P hg (B.filter fun j => ε₂ j) z) *
    multiplicityRow P hg B v₁ z ^ 3 * star (multiplicityRow P hg B v₂ z ^ 3)
theorem cubeConductorPrimes_pairwise_coprime {κ : Type*}
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (hinj : Function.Injective P)
    (B : Finset κ) (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool) :
    Pairwise (Function.onFun IsCoprime
      (fun j : cubeConductorSupport B v₁ v₂ ε₁ ε₂ => P j.val)) := by
  intro i j hij
  apply Ideal.isCoprime_of_isMaximal
  exact fun he => hij (Subtype.ext (hinj he))
open scoped SchwartzMap ContDiff
open ConcreteTraceCRT
open EisensteinSchwartzPoisson (paperRadialFourier)
def cubePairPoissonKernel {κ : Type*} [DecidableEq κ]
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ j, lambda ∉ P j) (B : Finset κ) (v₁ v₂ : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  let Q := fun j : cubeConductorSupport B v₁ v₂ ε₁ ε₂ => P j.val
  let hQ := cubeConductorPrimes_pairwise_coprime P hinj B v₁ v₂ ε₁ ε₂
  let eg := fun j : cubeConductorSupport B v₁ v₂ ε₁ ε₂ =>
    (conductorExponent (parity (v₁ j.val + v₂ j.val)) (ε₁ j.val) (ε₂ j.val)).val
  let row := finiteSexticRow Q (fun j => hg j.val) eg
  let c := finitePrimeModulus Q
  ((scale : ℂ) * canonicalNormalizedGauss Q hQ (fun j => hg j.val) eg /
    (‖eisEmbedding c‖ : ℂ)) *
    ∑ E ∈ (cubePrincipalSupport B v₁ v₂ ε₁ ε₂).powerset,
      let d := primeSubsetGenerator P E
      ((UniqueFactorizationMonoid.moebius (∏ j ∈ E, P j) : ℂ) * row d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        ∑' h : O, star (row h) * paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding c‖ ^ 2))
end FirstPassCubeLabels
end
end OAI


