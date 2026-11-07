-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_IdealGenerators
-- name    : OAI_NumberTheory_DirichletL_PrimeRows_IdealGenerators
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:03:48.739607+00:00
-- url     : https://prove2.me/theorems/ceae862e-0330-4e11-8bfa-654d85535f42
-- title:
--   Ideal Generators
-- statement:
--   Definitions and structural lemmas for Ideal Generators, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/IdealGenerators.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson
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
namespace ConcretePrimeRowBridge
end ConcretePrimeRowBridge
namespace ActualEisensteinCubic
noncomputable def primeSubsetGenerator {ι : Type*}
    (P : ι → Ideal O) (E : Finset ι) : O :=
  ConcretePrimeRowBridge.idealGenerator (∏ i ∈ E, P i)
open ConcreteTraceCRT
open ConcreteTraceCRT EisensteinSchwartzPoisson
end ActualEisensteinCubic
namespace GeneralPrimitiveTrace
open Complex EisensteinEmbedding ConcreteTraceCRT
open scoped ComplexConjugate
end GeneralPrimitiveTrace
namespace IdealGaussCRT
end IdealGaussCRT
namespace ActualEisensteinCubic
open ConcreteTraceCRT EisensteinSchwartzPoisson
end ActualEisensteinCubic
end
end OAI


