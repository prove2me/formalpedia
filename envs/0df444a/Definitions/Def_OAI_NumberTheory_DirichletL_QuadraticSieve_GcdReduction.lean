-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GcdReduction
-- name    : OAI_NumberTheory_DirichletL_QuadraticSieve_GcdReduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:00:00.579923+00:00
-- url     : https://prove2.me/theorems/99268509-e109-4a33-812b-41c456b6c8c9
-- title:
--   Gcd Reduction
-- statement:
--   Definitions and structural lemmas for Gcd Reduction, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/GcdReduction.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_TupleWeights
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
open ActualEisensteinCubic CompletedGauss FiniteSieveOperator IdealCoprimeSieveOperator DivisorBlockCauchy
def gcdPool {n : Type*} [Fintype n] (cols : n → Ideal O) : Finset (Ideal O) :=
  Finset.univ.image (fun p : n × n => gcd (cols p.1) (cols p.2))
end CanonicalQuadraticSieve
namespace FiniteSieveRestriction
def sectorCoefficient {n r : Type*} [DecidableEq r] (σ : n → r) (c : r) (a : n → ℂ) (j : n) : ℂ :=
  if σ j = c then a j else 0
end FiniteSieveRestriction
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy
open FiniteSieveRestriction
def columnRay (I : Ideal O) : EisensteinEPrimaryPhase.Coord := ActualEisensteinCoordinates.residue (primaryGenerator I)
def rayGcdBlock {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) : ℂ :=
  gcdBlock D rows cols (sectorCoefficient (fun j => columnRay (cols j)) c a)
end CanonicalQuadraticSieve
namespace FiniteSieveOperator
end FiniteSieveOperator
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss FiniteSieveOperator
open IdealCoprimeSieveOperator DivisorBlockCauchy
def rayGramMatrix {m n : Type*} [Fintype m]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (rows : m → Ideal O) (cols : n → Ideal O) : Matrix n n ℂ :=
  fun j k => ∑ i, if gcd (cols j) (cols k) = D ∧ columnRay (cols j) = c ∧ columnRay (cols k) = c then
    star (quadraticRow (cols j) (primaryGenerator (rows i))) *
      quadraticRow (cols k) (primaryGenerator (rows i)) else 0
def rayThirdNorm (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) : ℝ :=
  sSup (Set.range (fun a : idealRange N → ℂ =>
    ‖rayGcdBlock D c (fun I : highKernelRange M K => I.val) (fun J : idealRange N => J.val) a‖ /
      (∑ J, ‖a J‖ ^ 2)))
def thirdNorm (M N K : ℝ) (D : Ideal O) : ℝ :=
  ∑ c : EisensteinEPrimaryPhase.Coord, rayThirdNorm M N K D c
open ActualEisensteinCubic CompletedGauss FiniteSieveOperator IdealCoprimeSieveOperator DivisorBlockCauchy
def weightedGcdBlock {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (rows : m → Ideal O) (cols : n → Ideal O) (w : m → ℂ) (a : n → ℂ) : ℂ :=
  ∑ i, w i * ∑ j, ∑ k, gcdTerm D rows cols a i j k
end CanonicalQuadraticSieve
namespace FiniteSieveRestriction
end FiniteSieveRestriction
namespace CanonicalQuadraticSieve
section
open ActualEisensteinCubic CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy FiniteSieveRestriction
def weightedRayGcdBlock {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (rows : m → Ideal O) (cols : n → Ideal O) (v : m → ℝ) (a : n → ℂ) : ℂ :=
  weightedGcdBlock D rows cols (fun i => (v i : ℂ))
    (sectorCoefficient (fun j => columnRay (cols j)) c a)
end
open ActualEisensteinCubic CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy
def smoothHighWeight (M : ℝ) (I : Ideal O) : ℝ :=
  QuadraticInitialBound.sieveBump ((Ideal.absNorm I : ℝ) / M)
def smoothHighEnergy (M N K : ℝ) (a : idealRange N → ℂ) : ℝ :=
  ∑ I : highKernelRange (2 * M) K, smoothHighWeight M I.val *
    ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2
def smoothRayGcdBlock (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) : ℂ :=
  weightedRayGcdBlock D c (fun I : highKernelRange (2 * M) K => I.val)
    (fun J : idealRange N => J.val) (fun I => smoothHighWeight M I.val) a
end CanonicalQuadraticSieve
end
end OAI


