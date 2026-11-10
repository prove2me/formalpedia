-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_ProductColumns
-- name    : OAI_NumberTheory_DirichletL_QuadraticSieve_ProductColumns
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T08:19:24.683986+00:00
-- url     : https://prove2.me/theorems/38494f73-797b-4dbe-8768-86fc4d7d4046
-- title:
--   Product Columns
-- statement:
--   Definitions and structural lemmas for Product Columns, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/ProductColumns.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_TransformedColumns
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
open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
def productColumnCoefficient (S T : Finset (Ideal O)) (β : Ideal O → Ideal O → ℂ) (I : Ideal O) : ℂ :=
  ∑p∈(S×ˢT).filter (fun p => p.1*p.2=I),β p.1 p.2
end CanonicalQuadraticSieve
namespace CompletedGauss
section
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge
def shortCompletedSum (Ψ : O →* ℂ) (W : ℝ → ℂ) (X H₀ : ℝ) : ℂ :=
  ∑' H : Ideal O, if (Ideal.absNorm H:ℝ)<H₀ then
    (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψ H*
      completedT Ψ W (X/(Ideal.absNorm H:ℝ)^3) else 0
def shortCubeRange (H₀ : ℝ) : Finset (Ideal O) :=
  (idealsUpTo ⌈H₀⌉₊).filter (fun H => (Ideal.absNorm H:ℝ)<H₀)
end
open ActualEisensteinCubic CanonicalQuadraticSieve
end CompletedGauss
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel
end CanonicalQuadraticSieve
end
end OAI


