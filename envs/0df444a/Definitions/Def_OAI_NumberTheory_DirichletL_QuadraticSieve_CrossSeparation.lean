-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CrossSeparation
-- name    : OAI_NumberTheory_DirichletL_QuadraticSieve_CrossSeparation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:11:32.120499+00:00
-- url     : https://prove2.me/theorems/4bca916b-0ad8-4eaf-8bd0-95dd37a7e2fa
-- title:
--   Cross Separation
-- statement:
--   Definitions and structural lemmas for Cross Separation, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/CrossSeparation.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SquarePhaseFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_MixedConversion
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
namespace MixedCrossSeparation
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
def crossSymbol {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i k : ι) : ℂ :=
  canonicalSextic (Ideal.span {p i}) (hg i)
    (Ideal.Quotient.mk (Ideal.span {p i}) (p k))
def convertedColumnBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (inverse : Bool) : ℂ :=
  ∏ i ∈ S, (∏ k ∈ S.erase i, crossSymbol p hg i k ^ (if inverse then 5 else 1)) *
    convertedLocal (p i) (hp i) (hg i) inverse
def quadraticCrossPhase {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) : ℂ :=
  ∏ i ∈ A, ∏ k ∈ B, crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open QuadraticGaussRay ActualEisensteinCoordinates
theorem restricted_prime_coprime {ι : Type*} (p : ι → O)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (A : Finset ι) :
    Pairwise (Function.onFun IsCoprime (fun i : A => Ideal.span {p i.val})) := by
  intro i k hik
  exact hcop (fun h => hik (Subtype.ext h))
def quadraticBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A : Finset ι) : ℂ :=
  ∏ i ∈ A, (∏ k ∈ A.erase i, crossSymbol p hg i k ^ 3) *
    localGauss (p i) (hp i) (hg i) 3
def quadraticRayPair (a b : EisensteinEPrimaryPhase.Coord) : ℂ :=
  quadraticRayValue (EisensteinEPrimaryPhase.mul a b) /
    (quadraticRayValue a * quadraticRayValue b)
end MixedCrossSeparation
open scoped BigOperators Classical
namespace CoprimeMobiusExtension
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic
end CoprimeMobiusExtension
end
end OAI


