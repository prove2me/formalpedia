-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoefficientCancellation
-- name    : OAI_NumberTheory_DirichletL_QuadraticSieve_CoefficientCancellation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:25:48.687775+00:00
-- url     : https://prove2.me/theorems/96a84099-0d59-4059-b356-2e6bb667b483
-- title:
--   Coefficient Cancellation
-- statement:
--   Definitions and structural lemmas for Coefficient Cancellation, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/CoefficientCancellation.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RayCharacters
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRadialFourier_nonzero_lattice_uniform

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
namespace MixedCrossSeparation
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
theorem columnPrimeCoprime {ι : Type*} (p : ι → O)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (S : Finset ι) :
    Pairwise (Function.onFun IsCoprime (fun i : S => Ideal.span {p i.val})) := by
  intro i j hij
  exact hcop (fun h => hij (Subtype.ext h))
def columnCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) : ℂ :=
  canonicalProductCoefficient (fun i : S => p i.val) (fun i => hp i.val)
    (columnPrimeCoprime p hcop S) (fun i => hg i.val)
def columnG {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) : ℂ :=
  canonicalProductG (fun i : S => p i.val) (fun i => hp i.val)
    (columnPrimeCoprime p hcop S) (fun i => hg i.val)
end MixedCrossSeparation
open scoped BigOperators Classical SchwartzMap ContDiff
namespace FirstCauchyArithmetic
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open MixedCrossSeparation GaussGeneratorTransport ConcretePrimeRowBridge EisensteinSchwartzPoisson
def firstPassColumnMinus {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (C : Finset ι → ℂ) (d : O) (S : Finset ι) : ℂ :=
  star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1)) *
    columnG p hp hcop hg S * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d * C S
def firstPassColumnPlus {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (C : Finset ι → ℂ) (d : O) (S : Finset ι) : ℂ :=
  columnG p hp hcop hg S * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d * C S
def activeGaussRowFactor
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (d h : O) : ℂ :=
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  let row := finiteSexticRow (activePrimes P S T) (fun i => hg i.val) (activeExponent S T)
  canonicalProductGauss (fun i : activeSupport S T => p i.val) (fun i => hp i.val)
    (activePrimes_pairwise_isCoprime P hinj S T) (fun i => hg i.val) (activeExponent S T) *
      (row d * star (row h))
end FirstCauchyArithmetic
open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
def pvSeminorms : Finset (ℕ × ℕ) :=
  Classical.choose paperRadialFourier_nonzero_lattice_uniform
def pvConstant : ℝ :=
  Classical.choose (Classical.choose_spec paperRadialFourier_nonzero_lattice_uniform)
def pvControl (W : 𝓢(ℝ, ℂ)) : ℝ :=
  pvConstant * pvSeminorms.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
end QuadraticInitialBound
end
end OAI


