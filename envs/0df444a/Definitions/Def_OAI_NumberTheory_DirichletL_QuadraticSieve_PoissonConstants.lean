-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonConstants
-- name    : OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonConstants
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T04:54:14.851794+00:00
-- url     : https://prove2.me/theorems/0c0a050f-49b4-4177-bc5b-df779ad7aded
-- title:
--   Poisson Constants
-- statement:
--   Definitions and structural lemmas for Poisson Constants, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonConstants.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GlobalBinLoss
set_option autoImplicit false
namespace OAI
noncomputable section
namespace CanonicalQuadraticSieve
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
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson
def poissonPrimitiveConstants
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    {α : ℝ} (hexp : HasSieveExponent α) (η : ℝ) (hη : 0<η)
    (D : ℝ) (W : 𝓢(ℝ,ℂ)) : List ℝ :=
  [divisorConstant η hη, 2+1/(η*Real.log 2), 256,
   supportConstant η hη, divisorExponentConstant hexp η hη,
   ‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖,
   ‖quadraticTransformedSquareProfile W 0‖,
   dualMiddleDecayConstant (quadraticTransformedSquareProfile W),
   ‖paperRadialFourier (quadraticSquareProfile W) 0‖,
   originalMiddleDecayConstant (quadraticSquareProfile W),
   nonzeroLatticeEnvelopeConstant, CD, CS, CT, CP,
   sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W),
   sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W),
   sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W, D^η]
end
section
end
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson
def poissonShape (M X α : ℝ) : ℝ := M+X+X^(2*α-1)*M^(1-α)
def poissonShapeConstant (B C1 : ℝ) : ℝ := 2+4*C1^3+B^2+C1
end CanonicalQuadraticSieve
end
end OAI


