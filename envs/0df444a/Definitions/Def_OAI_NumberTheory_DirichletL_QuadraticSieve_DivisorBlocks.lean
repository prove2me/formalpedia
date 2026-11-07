-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_DivisorBlocks
-- name    : OAI_NumberTheory_DirichletL_QuadraticSieve_DivisorBlocks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:26:08.629284+00:00
-- url     : https://prove2.me/theorems/5536f424-0786-40fd-a55b-a1a15d98d839
-- title:
--   Divisor Blocks
-- statement:
--   Definitions and structural lemmas for Divisor Blocks, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/DivisorBlocks.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_IdealQuotients
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
namespace CanonicalQuadraticSieve
section
open IdealCoprimeSieveOperator DivisorBlockCauchy IdealDivisorBilinearBlocks
def quotientBlock {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) : ℝ :=
  blockValue left right (fun D => quotientMatrix D rows left)
    (fun E => quotientMatrix E rows right) a b D E
end
section
open ConcretePrimeRowBridge ActualEisensteinCubic
end
open IdealDivisorBilinearBlocks CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy
def originalBlock {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) : ℝ :=
  blockValue left right (fun _ i j => quadraticRow (left j) (primaryGenerator (rows i)))
    (fun _ i k => quadraticRow (right k) (primaryGenerator (rows i))) a b D E
end CanonicalQuadraticSieve
namespace FiniteSieveRestriction
open FiniteSieveOperator
end FiniteSieveRestriction
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss
open QuadraticSquarefreeKernel FiniteSieveOperator
def Supported (I : Ideal O) : Prop :=
  I ≠ 0 ∧ ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
    lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2
def fullRange (M : ℝ) : Finset (Ideal O) := (idealsUpTo ⌊M⌋₊).filter Supported
def highKernelRange (M K : ℝ) : Finset (Ideal O) :=
  (fullRange M).filter (fun I => K < (Ideal.absNorm (squarefreePart I) : ℝ))
def highKernelMatrix (M N K : ℝ) : Matrix (highKernelRange M K) (idealRange N) ℂ :=
  fun I J => quadraticRow J.val (primaryGenerator I.val)
def highKernelNorm (M N K : ℝ) : ℝ := ‖operator (highKernelMatrix M N K)‖ ^ 2
end CanonicalQuadraticSieve
open MeasureTheory
open scoped BigOperators Classical SchwartzMap
namespace QuadraticKernelTransfer
open FourierBridge EisensteinSchwartzPoisson
end QuadraticKernelTransfer
namespace CanonicalQuadraticSieve
open FourierBridge EisensteinSchwartzPoisson QuadraticKernelTransfer
open IdealCoprimeSieveOperator DivisorBlockCauchy IdealDivisorBilinearBlocks
section
variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
def quotientTerm (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) (i : m) (j : n) (k : p) : ℂ :=
  if IsCoprime (left j) (right k) then
    star (quotientMatrix D rows left i j * (if D ∣ left j then a j else 0)) *
      (quotientMatrix E rows right i k * (if E ∣ right k then b k else 0)) else 0
def divisorBlockCost (ε : ℝ) (hε : 0 < ε) (D₁ D₂ M N : ℝ) (a : n → ℂ) (b : p → ℂ) : ℝ :=
  256 ^ 2 * D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂) *
    (supportConstant ε hε * divisorConstant ε hε) ^ 2 * (N ^ ε) ^ 4 *
    (∑ j, ‖a j‖ ^ 2) * (∑ k, ‖b k‖ ^ 2)
end
end CanonicalQuadraticSieve
open MeasureTheory
open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open FourierBridge EisensteinSchwartzPoisson QuadraticKernelTransfer
open IdealCoprimeSieveOperator DivisorBlockCauchy IdealDivisorBilinearBlocks
section
variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
def originalTerm (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) (i : m) (j : n) (k : p) : ℂ :=
  if IsCoprime (left j) (right k) then
    star (quadraticRow (left j) (CompletedGauss.primaryGenerator (rows i)) * (if D ∣ left j then a j else 0)) *
      (quadraticRow (right k) (CompletedGauss.primaryGenerator (rows i)) * (if E ∣ right k then b k else 0)) else 0
end
end CanonicalQuadraticSieve
end
end OAI


