-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PrincipalTruncation
-- name    : OAI_NumberTheory_DirichletL_QuadraticSieve_PrincipalTruncation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:47:29.565212+00:00
-- url     : https://prove2.me/theorems/95b54b13-8ea4-4bf8-826d-44841c5a7a44
-- title:
--   Principal Truncation
-- statement:
--   Definitions and structural lemmas for Principal Truncation, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/PrincipalTruncation.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_RamifiedNormWeights
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
open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport UnrestrictedIdealReindex
def lowPrincipalIdeal (I J : Ideal O) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' A : {A : Ideal O // Supported A},
    (idealZeroMask I (primaryGenerator A.val) * idealZeroMask J (primaryGenerator A.val)) *
      W (((Ideal.absNorm A.val : ℝ) / X) ^ 2)
def lowPrincipalLattice (I J : Ideal O) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' z : O, rowCoprimeMask (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ z *
    W ((‖eisEmbedding z‖ ^ 2 / X) ^ 2)
end
section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson TruncatedPrincipalPoisson IdealCoprimeSieveOperator
def lowPrincipalMain (I J : Ideal O) (W : SchwartzMap ℝ ℂ) (X Z : ℝ) : ℂ :=
  (6 : ℂ)⁻¹ * principalTruncation (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ
    (quadraticSquareProfile W) X Z
def lowPrincipalMiddle (I J : Ideal O) (W : SchwartzMap ℝ ℂ) (X Y Z lengthScale : ℝ) : ℂ :=
  (6 : ℂ)⁻¹ * middleTruncation (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ
    (quadraticSquareProfile W) X Y Z lengthScale
def lowPrincipalError (I J : Ideal O) (W : SchwartzMap ℝ ℂ) (X Y Z lengthScale : ℝ) : ℂ :=
  (6 : ℂ)⁻¹ * truncationError (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ
    (quadraticSquareProfile W) X Y Z lengthScale
end
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
end CanonicalQuadraticSieve
open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstCauchyArithmetic (activeGaussRowFactor)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
end
section
open ActualEisensteinCubic
def secondExpansionPool {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) : Finset (SecondExpansionData ι) :=
  F.powerset.biUnion (fun G => G.powerset.biUnion (fun E =>
    F.powerset.biUnion (fun V => (K G E).image (fun k => ⟨G,E,V,k⟩))))
def secondExpansionSector {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) : Finset (SecondExpansionData ι) :=
  (secondExpansionPool F K).filter (fun x => x.sourceCommon \ x.divisor = R)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
end
section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn jLabel)
open JointLogSeparation (halfNormalizationCLM)
end
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hc : ∀ i, ringChar (OAI.SecondPassArithmetic.O ⧸ Ideal.span {p i}) ≠ 2)
include hc
end SecondPassArithmetic
end
end OAI


