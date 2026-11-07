-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_MixedConversion
-- name    : OAI_NumberTheory_DirichletL_GaussSum_MixedConversion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:09:08.859203+00:00
-- url     : https://prove2.me/theorems/ab03358d-9f91-47ed-bbe7-d856abb753ec
-- title:
--   Mixed Conversion
-- statement:
--   Definitions and structural lemmas for Mixed Conversion, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/MixedConversion.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ActiveConductor
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
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
open scoped BigOperators Classical
namespace MixedGaussConversion
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase
def localGauss (p : O) (hp : p ≠ 0) [ (Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (j : ℕ) : ℂ :=
  ConcreteBreveE.normalizedTraceGauss p hp (canonicalSextic (Ideal.span {p}) hg ^ j)
def localCoefficient (p : O) (hp : p ≠ 0) [ (Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) : ℂ :=
  star (angularFactor p) * localGauss p hp hg 2
def localG (p : O) (hp : p ≠ 0) [ (Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) : ℂ :=
  breveLocalG (Ideal.span {p}) hg p rfl hp
def convertedLocal (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (inverse : Bool) : ℂ :=
  if inverse then
    (canonicalSextic (Ideal.span {p}) hg (Ideal.Quotient.mk (Ideal.span {p}) (-1 : O)) *
      localCoefficient p hp hg) / localG p hp hg
  else star (localCoefficient p hp hg) / star (localG p hp hg)
end MixedGaussConversion
open scoped BigOperators Classical SchwartzMap ContDiff
namespace GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase
open MixedGaussConversion
def activeConvertedGauss
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) : ℂ :=
  (∏ i : activeSupport S T,
    ∏ k ∈ @Finset.erase (activeSupport S T)
      (fun a b => Classical.propDecidable (a = b)) Finset.univ i,
    (canonicalSextic (Ideal.span {p i.val}) (hgood i.val) ^ activeExponent S T i)
      (Ideal.Quotient.mk (Ideal.span {p i.val}) (p k.val))) *
    ∏ i : activeSupport S T,
      convertedLocal (p i.val) (hp i.val) (hgood i.val) (decide (i.val ∈ S \ T))
def activePairDualSeries
    {ι : Type*} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  let row := finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) S T)
    (fun i => hgood i.val) (activeExponent S T)
  let n := ∏ i : activeSupport S T, p i.val
  ∑ E ∈ (S ∩ T).powerset,
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * row d /
      (‖eisEmbedding d‖ ^ 2 : ℝ)) *
      ∑' h : O, star (row h) * paperRadialFourier W
        (scale * ‖eisEmbedding h‖ ^ 2 /
          (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))
def convertedPairPoissonKernel
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  ((scale : ℂ) / (‖eisEmbedding (∏ i : activeSupport S T, p i.val)‖ : ℂ)) *
    activeConvertedGauss p hp hgood S T * activePairDualSeries p hgood S T W scale
end GaussGeneratorTransport
open scoped BigOperators Classical SchwartzMap ContDiff
namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge ConcreteTraceCRT EisensteinSchwartzPoisson
noncomputable def mobiusIdealColumn (C : Ideal O → ℂ) (I : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius I : ℂ) * C I
noncomputable def conjugateIdealRowSum
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (C : Ideal O → ℂ) (y : O) : ℂ :=
  ∑ I ∈ F, mobiusIdealColumn C I * star (idealSexticRow F hFpos hFgood I y)
end ConcretePrimeRowBridge
open MeasureTheory Set
open scoped BigOperators
namespace EisensteinSchwartzPoisson
open ConcreteTraceCRT ActualEisensteinCubic
end EisensteinSchwartzPoisson
end
end OAI


