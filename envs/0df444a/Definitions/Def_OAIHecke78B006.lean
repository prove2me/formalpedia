-- Prove2me | Definitions.Def_OAIHecke78B006
-- name    : OAIHecke78B006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T21:45:42.604585+00:00
-- url     : https://prove2.me/theorems/148cf9dc-a2c0-4b80-86e9-180954d72624
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 7 of 29
-- statement:
--   Definitions bundle 7 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B003`, `OAIHecke78B005` of this split, and through them their definitions. It also imports wurtle's published bundle `HeckeSevenEighths` (the comparator definitions of OpenAI's challenge statement: `Character`, `LFunction` and the theta-function pairs they are built from), which OpenAI's development defines identically.
--
--   Modules: `CubicSieve.IntegratedTransfer`, `QuadraticSieve.PrimePools`, `CubicSieve.FixedProfiles`, `Eisenstein.ConstantTermSupport`, `QuadraticSieve.SquareParts`, `CubicSieve.ResidualSectors`, `QuadraticSieve.UnrestrictedCharacters`, `CubicSieve.ConjugateProfiles`, `Eisenstein.RamifiedNormWeights`, `QuadraticSieve.PrincipalTruncation`, `CubicSieve.FrequencyCutoffs`, `QuadraticSieve.TruncatedSecondTransfer`, `Fourier.LogDensity`, `CubicSieve.GlobalEncoding`, `QuadraticSieve.CuspCoercivity`, `GaussSum.GlobalScales`, `QuadraticSieve.AnnularLifting`, `CubicSieve.CubeBlocks`, `MeanSquare.OutsideIdeals`, `MeanSquare.PoissonSource`, `CubicSieve.DualZeroMode`, `MeanSquare.CanonicalDensity`, `CubicSieve.RankMargins`, `MeanSquare.UniformPolynomialHeight`, `CubicSieve.Elements`, `Descent.ActualProfiles`, `Descent.WindowFourier`, `Descent.ActualSecondProfile`, `Descent.ActualSecondMeasure`, `Inversion.AmbientProfileTower`, `Inversion.InitialProfile`, `Inversion.InitialClippedColumns`, `Descent.SecondSourceProfile`, `Descent.SecondWeights`, `Moments.Lattice`, `Moments.Twist`, `Descent.FirstBlocks`, `Descent.FirstFamilyEnergy`, `Descent.FirstRetainedPhysical`, `Descent.FirstCanonicalEnergy`, `Descent.FirstFamilySource`, `Descent.FirstPhysicalFamily`, `Descent.FirstActualSecondEnergy`, `Descent.FirstWholeCubePriority`, `Inversion.PrincipalEnergy`, `Inversion.SecondPrincipalCaller`, `Descent.PriorityProfile`, `Descent.ClippedChild`, `Descent.FirstTailAggregation`, `Descent.ReopenedSource`, `Inversion.WholePriorityValidSource`, `Descent.FirstLabelCellStepGates`, `Detector.IdealMultiplicative`, `Hecke.InverseAmplificationRows`, `Detector.CanonicalSlots`, `Detector.GramGcd`, `Detector.GramIdealDilation`, `Detector.GramPhysicalScale`, `Detector.GramMobiusPool`, `Detector.GramCommonSource`, `Inversion.InitialProfileBounds`, `Moments.RetainedProfile`, `Moments.Unequal`, `PrimeRows.Valuation`, `PrimeRows.CoarseAmplitude`, `PrimeRows.CubeBinPartition`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B003
import Definitions.Def_OAIHecke78B005

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B006

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  CubicSieve.IntegratedTransfer
  QuadraticSieve.PrimePools
  CubicSieve.FixedProfiles
  Eisenstein.ConstantTermSupport
  QuadraticSieve.SquareParts
  CubicSieve.ResidualSectors
  QuadraticSieve.UnrestrictedCharacters
  CubicSieve.ConjugateProfiles
  Eisenstein.RamifiedNormWeights
  QuadraticSieve.PrincipalTruncation
  CubicSieve.FrequencyCutoffs
  QuadraticSieve.TruncatedSecondTransfer
  Fourier.LogDensity
  CubicSieve.GlobalEncoding
  QuadraticSieve.CuspCoercivity
  GaussSum.GlobalScales
  QuadraticSieve.AnnularLifting
  CubicSieve.CubeBlocks
  MeanSquare.OutsideIdeals
  MeanSquare.PoissonSource
  CubicSieve.DualZeroMode
  MeanSquare.CanonicalDensity
  CubicSieve.RankMargins
  MeanSquare.UniformPolynomialHeight
  CubicSieve.Elements
  Descent.ActualProfiles
  Descent.WindowFourier
  Descent.ActualSecondProfile
  Descent.ActualSecondMeasure
  Inversion.AmbientProfileTower
  Inversion.InitialProfile
  Inversion.InitialClippedColumns
  Descent.SecondSourceProfile
  Descent.SecondWeights
  Moments.Lattice
  Moments.Twist
  Descent.FirstBlocks
  Descent.FirstFamilyEnergy
  Descent.FirstRetainedPhysical
  Descent.FirstCanonicalEnergy
  Descent.FirstFamilySource
  Descent.FirstPhysicalFamily
  Descent.FirstActualSecondEnergy
  Descent.FirstWholeCubePriority
  Inversion.PrincipalEnergy
  Inversion.SecondPrincipalCaller
  Descent.PriorityProfile
  Descent.ClippedChild
  Descent.FirstTailAggregation
  Descent.ReopenedSource
  Inversion.WholePriorityValidSource
  Descent.FirstLabelCellStepGates
  Detector.IdealMultiplicative
  Hecke.InverseAmplificationRows
  Detector.CanonicalSlots
  Detector.GramGcd
  Detector.GramIdealDilation
  Detector.GramPhysicalScale
  Detector.GramMobiusPool
  Detector.GramCommonSource
  Inversion.InitialProfileBounds
  Moments.RetainedProfile
  Moments.Unequal
  PrimeRows.Valuation
  PrimeRows.CoarseAmplitude
  PrimeRows.CubeBinPartition
-/

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace SecondPassArithmetic

section

open scoped BigOperators Classical
open MeasureTheory

section
open ActualEisensteinCubic
open FirstPassCubeLabels (cubeOddSupport coreRayCoefficient coreRayTwist dilatedCoreRow
  b0Label jLabel columnLog )
open FirstCauchyArithmetic (supportMobius supportConjugateSum)
open RayFourExpansion (RayCharacter crossCoeff)
open FourierBridge (logPhase)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def firstCoreInputRow (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (z : O) : ℂ :=
  inputConjugateRow p hg (F \ D) (firstCoreTwist negative χ Ψ r)
    (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
    (firstCoreTest H V y negative t D) (if negative then -z else z)

end

open ActualEisensteinCubic
open FirstPassCubeLabels (cubeOddSupport coreRayCoefficient dilatedCoreRow b0Label jLabel
  columnLog )
open RayFourExpansion (RayCharacter crossCoeff)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end

open ActualEisensteinCubic
open FirstPassCubeLabels (b0Label jLabel)
open RayFourExpansion (RayCharacter)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace JointLogSeparation

abbrev Frequency := ℝ × ℝ × ℝ

def tripleCoefficient (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (t : Frequency) : ℂ :=
  b₁ t.1 * (b₂ t.2.1 * b₃ t.2.2)

end JointLogSeparation

namespace SecondPassIntegration
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open FirstPassCubeLabels (columnLog)
local instance instFintypeUnitsO : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def childEnergy (F : Finset ι) (Ψ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V : ℝ → ℂ) (X : ℝ) (testNegative rowNegative : Bool) (a b : ℝ) : ℝ :=
  ∑ u : Oˣ, ∑ z ∈ T,
    ‖idealChildRow p hp hcop hg F Ψ m (fixedSecondTest p V X a b testNegative) rowNegative u z‖ ^ 2

end SecondPassIntegration

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

section

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

instance canonicalPoolMaximal (F : Finset (Ideal O)) (i : primePool F) : i.val.IsMaximal := by
  obtain ⟨I, hIF, hi⟩ := mem_primePool_iff.mp i.property
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor i.val hi
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

theorem poolGood (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) (i : primePool F) :
    lambda ∉ i.val := by
  obtain ⟨I, hIF, hi⟩ := mem_primePool_iff.mp i.property
  exact ((hF I hIF).2.2 i.val hi).1

theorem poolOdd (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) (i : primePool F) :
    ringChar (O ⧸ i.val) ≠ 2 := by
  obtain ⟨I, hIF, hi⟩ := mem_primePool_iff.mp i.property
  exact ((hF I hIF).2.2 i.val hi).2

def poolPrimary (F : Finset (Ideal O)) (i : primePool F) : O := primaryPrime i.val

theorem poolPrimary_ne_zero (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (i : primePool F) : poolPrimary F i ≠ 0 := primaryPrime_ne_zero i.val (poolGood F hF i)

theorem poolPrimary_span (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (i : primePool F) : Ideal.span {poolPrimary F i} = i.val :=
  (primaryPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.1

theorem primaryPrime_eq_primaryGenerator (P : Ideal O) [P.IsMaximal] :
    primaryPrime P = primaryGenerator P := by
  have hp : Prime P := Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  rw [primaryGenerator, if_neg hp.ne_zero, UniqueFactorizationMonoid.normalizedFactors_irreducible hp.irreducible,
    normalize_eq]
  simp only [Multiset.map_singleton, Multiset.prod_singleton]

theorem primaryGenerator_eq_poolProduct (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I : Ideal O) (hIF : I ∈ F) :
    primaryGenerator I = ∏ i ∈ idealSupport F I, poolPrimary F i := by
  calc
    _ = primaryGenerator (∏ i ∈ idealSupport F I, i.val) :=
      congrArg primaryGenerator (idealSupport_product_eq F hIF (hF I hIF).2.1).symm
    _ = ∏ i ∈ idealSupport F I, primaryGenerator i.val := by
      change primaryGeneratorHom (∏ i ∈ idealSupport F I, i.val) =
        ∏ i ∈ idealSupport F I, primaryGeneratorHom i.val
      rw [map_prod]
    _ = _ := Finset.prod_congr rfl (fun i hi => (primaryPrime_eq_primaryGenerator i.val).symm)

theorem quadraticRow_eq_pool (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I : Ideal O) (hIF : I ∈ F) (z : O) :
    quadraticRow I z = QuadraticInitialBound.quadraticRow
      (fun i : primePool F => i.val) (poolGood F hF) (idealSupport F I) z := by
  rw [quadraticRow_eq F hF I hIF z]
  rfl

theorem poolPrimary_coprime (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) :
    Pairwise (Function.onFun IsCoprime (fun i : primePool F => Ideal.span {poolPrimary F i})) := by
  intro i j hij
  change IsCoprime (Ideal.span {poolPrimary F i}) (Ideal.span {poolPrimary F j})
  rw [poolPrimary_span F hF i, poolPrimary_span F hF j]
  exact Ideal.isCoprime_of_isMaximal (fun he => hij (Subtype.ext he))

theorem poolPrimary_good (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) (i : primePool F) :
    lambda ∉ Ideal.span {poolPrimary F i} := by rw [poolPrimary_span F hF i]; exact poolGood F hF i

theorem poolPrimary_odd (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) (i : primePool F) :
    ringChar (O ⧸ Ideal.span {poolPrimary F i}) ≠ 2 := by rw [poolPrimary_span F hF i]; exact poolOdd F hF i

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates

theorem quadraticRow_eq_primaryPool (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I : Ideal O) (hIF : I ∈ F) (z : O) :
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    quadraticRow I z = QuadraticInitialBound.quadraticRow
      (fun i : primePool F => Ideal.span {poolPrimary F i}) (poolPrimary_good F hF) (idealSupport F I) z := by
  have he : (fun i : primePool F => Ideal.span {poolPrimary F i}) = (fun i : primePool F => i.val) :=
    funext (poolPrimary_span F hF)
  simpa only [he] using quadraticRow_eq_pool F hF I hIF z

theorem quadraticRow_eq_primeSubset (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I : Ideal O) (hIF : I ∈ F) (z : O) :
    quadraticRow I z = finiteSexticRow
      (fun i : idealSupport F I => i.val.val) (fun i => poolGood F hF i.val) (fun _ => 3) z := by
  rw [quadraticRow_eq_pool F hF I hIF z, QuadraticInitialBound.quadraticRow_eq_canonical]

end
section

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates
open EisensteinSchwartzPoisson GaussGeneratorTransport

theorem quadraticRow_eq_primarySubset (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I : Ideal O) (hIF : I ∈ F) (z : O) :
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    quadraticRow I z = finiteSexticRow
      (fun i : idealSupport F I => Ideal.span {poolPrimary F i.val})
      (fun i => poolPrimary_good F hF i.val) (fun _ => 3) z := by
  have he : (fun i : idealSupport F I => Ideal.span {poolPrimary F i.val}) =
      (fun i : idealSupport F I => i.val.val) := funext (fun i => poolPrimary_span F hF i.val)
  simpa only [he] using quadraticRow_eq_primeSubset F hF I hIF z

end

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassIntegration
open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

def elementNorm (a : O) : ℝ := ‖eisEmbedding a‖ ^ 2

def conjugateProfile (g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap g

@[simp] lemma conjugateProfile_apply (g : 𝓢(ℝ, ℂ)) (s : ℝ) :
    conjugateProfile g s = star (g s) := rfl

end SecondPassIntegration

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def secondPairRadialMode (S T : Finset ι) (e k : O) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  let n := ∏ i : activeSupport T S, p i.val
  ((Y : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) *
    activeGaussRowFactor p hp hinj hg T S e k

def residualSecondMode (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (e k : O) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑ S ∈ (F \ G).powerset, ∑ T ∈ (F \ G).powerset,
    if Disjoint S T then
      star (supportMobius (fun i => Ideal.span {p i}) S * secondInputCoefficient p hg Ψ₁ m c d H₁ S) *
      (supportMobius (fun i => Ideal.span {p i}) T * secondInputCoefficient p hg Ψ₂ m c d H₂ T) *
      secondPairRadialMode p hp hg hinj S T e k W Y
    else 0

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def secondFrequencyKernel (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
    ((Y : ℂ) / (‖eisEmbedding (∏ i ∈ S ∪ T, p i)‖ : ℂ)) *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * primeProductNorm p (S ∪ T))) *
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k H₁ H₂ S T
  else 0

def secondOverlapBlock (F G : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑ S ∈ (F \ G).powerset, ∑ T ∈ (F \ G).powerset, if Disjoint S T then
    overlapPairWeight p hg Ψ m c d H G S T * maskedSecondDual p hg hp hinj G S T W Y
  else 0

end SecondPassArithmetic

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap ContDiff

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

lemma symbol_cube_numerator (a d : O) (hd : denominatorCondition (a^3) d) :
    symbol (a^3) d=1 := by
  have hprimary : lambda^2 ∣ d-1 := lambda_sq_dvd_three.trans hd.2
  rw [symbol_pow_numerator a d hprimary 3]
  apply symbol_cube_of_isCoprime a d hprimary
  exact hd.1.of_isCoprime_of_dvd_left ⟨a^2,by ring⟩

theorem arithmeticResidueSum_cube (a : O) (ha : a ≠ 0) :
    arithmeticResidueSum 0 (a^3)=(Nat.card (AdmissibleResidue (a^3)):ℂ) := by
  let : Finite (AdmissibleResidue (a^3)) := finite_admissibleResidue _ (pow_ne_zero 3 ha)
  let : Fintype (AdmissibleResidue (a^3)) := Fintype.ofFinite _
  rw [arithmeticResidueSum,tsum_fintype]
  have hterm (r : AdmissibleResidue (a^3)) :
      eisEmbedding (symbol (a^3) (denominatorRep (a^3) r.1))*
        ShortDraftTrace.breveE (cuspFrequency 0*eisEmbedding (denominatorRep (a^3) r.1)/
          eisEmbedding (a^3))=1 := by
    rw [symbol_cube_numerator a _ r.2,map_one]
    simp [cuspFrequency]
  simp only [hterm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Nat.card_eq_fintype_card]

lemma admissibleResidue_nonempty (c : O) (hc : c ≠ 0) : Nonempty (AdmissibleResidue c) := by
  let d : AdmissibleDenominator c := ⟨1,isCoprime_one_right,by simp⟩
  exact ⟨((residueDenominatorEquiv c hc).symm d).1⟩

theorem arithmeticResidueSum_cube_ne_zero (a : O) (ha : a ≠ 0) :
    arithmeticResidueSum 0 (a^3) ≠ 0 := by
  rw [arithmeticResidueSum_cube a ha]
  let : Finite (AdmissibleResidue (a^3)) := finite_admissibleResidue _ (pow_ne_zero 3 ha)
  let : Nonempty (AdmissibleResidue (a^3)) := admissibleResidue_nonempty _ (pow_ne_zero 3 ha)
  exact Nat.cast_ne_zero.mpr (Nat.card_pos (α := AdmissibleResidue (a^3))).ne'

lemma denominatorCondition_congr (c d e : O) (h : 3*c ∣ d-e) :
    denominatorCondition c d ↔ denominatorCondition c e := by
  obtain ⟨n,hn⟩ := h
  have hd : d=e+3*c*n := by linear_combination hn
  rw [hd]
  exact denominatorCondition_shift c e n

lemma denominatorCondition_mul (c d t : O) (hd : denominatorCondition c d)
    (ht : denominatorCondition c t) : denominatorCondition c (d*t) := by
  refine ⟨hd.1.mul_right ht.1,?_⟩
  convert (preTransparency := .instances) dvd_add (hd.2.mul_right t) ht.2 using 1 ; ring

lemma row_symbol_congr_modulus (c d e : O) (hlevel : (3:O) ∣ c)
    (he : (3:O) ∣ e-1) (h : 3*c ∣ d-e) : symbol c d=symbol c e := by
  obtain ⟨n,hn⟩ := h
  have hd : d=e+3*c*n := by linear_combination hn
  rw [hd]
  exact row_symbol_shift c e n hlevel he

lemma denominatorRep_product_congr (c t : O) (r : DenominatorResidue c) :
    3*c ∣ denominatorRep c (Ideal.Quotient.mk (Ideal.span {3*c}) t*r)-t*denominatorRep c r := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  rw [denominatorRep_spec,map_mul,denominatorRep_spec]

def residueMultiplication (c t : O) (ht : denominatorCondition c t)
    (r : AdmissibleResidue c) : AdmissibleResidue c :=
  ⟨Ideal.Quotient.mk (Ideal.span {3*c}) t*r.1,
    (denominatorCondition_congr c _ _ (denominatorRep_product_congr c t r.1)).2
      (denominatorCondition_mul c t _ ht r.2)⟩

lemma denominatorCondition_coprime_modulus (c t : O) (ht : denominatorCondition c t) :
    IsCoprime (3*c) t := by
  obtain ⟨n,hn⟩ := ht.2
  have h3 : IsCoprime (3:O) t := ⟨-n,1,by linear_combination hn⟩
  exact h3.mul_left ht.1

lemma residueMultiplication_injective (c t : O) (ht : denominatorCondition c t) :
    Function.Injective (residueMultiplication c t ht) := by
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {3*c}) t) := by
    have hh := (denominatorCondition_coprime_modulus c t ht).map
      (Ideal.Quotient.mk (Ideal.span {3*c}))
    have hz : Ideal.Quotient.mk (Ideal.span {3*c}) (3*c)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    simpa only [hz,isCoprime_zero_left] using hh
  intro r q heq
  apply Subtype.ext
  exact hunit.mul_left_cancel (congrArg Subtype.val heq)

def residueMultiplicationEquiv (c : O) (hc : c ≠ 0) (t : O)
    (ht : denominatorCondition c t) : AdmissibleResidue c ≃ AdmissibleResidue c := by
  letI : Finite (AdmissibleResidue c) := finite_admissibleResidue c hc
  exact Equiv.ofBijective (residueMultiplication c t ht)
    ⟨residueMultiplication_injective c t ht,
      Finite.surjective_of_injective (residueMultiplication_injective c t ht)⟩

lemma residueMultiplication_phase (c : O) (hlevel : (3:O) ∣ c) (t : O)
    (ht : denominatorCondition c t) (r : AdmissibleResidue c) :
    symbol c (denominatorRep c (residueMultiplication c t ht r).1)=
      symbol c t*symbol c (denominatorRep c r.1) := by
  change symbol c (denominatorRep c (Ideal.Quotient.mk (Ideal.span {3*c}) t*r.1))=
    symbol c t*symbol c (denominatorRep c r.1)
  rw [row_symbol_congr_modulus c _ (t*denominatorRep c r.1) hlevel
    (denominatorCondition_mul c t _ ht r.2).2 (denominatorRep_product_congr c t r.1)]
  exact symbol_mul_denominator c t (denominatorRep c r.1)

lemma arithmeticResidueSum_zero (c : O) :
    arithmeticResidueSum 0 c=∑' r : AdmissibleResidue c,
      eisEmbedding (symbol c (denominatorRep c r.1)) := by
  simp only [arithmeticResidueSum,cuspFrequency,map_zero,zero_div,zero_mul,
    AddChar.map_zero_eq_one,mul_one]

theorem arithmeticResidueSum_constant_eigen (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c)
    (t : O) (ht : denominatorCondition c t) :
    eisEmbedding (symbol c t)*arithmeticResidueSum 0 c=arithmeticResidueSum 0 c := by
  rw [arithmeticResidueSum_zero]
  have heq := (residueMultiplicationEquiv c hc t ht).tsum_eq
    (fun r : AdmissibleResidue c => eisEmbedding (symbol c (denominatorRep c r.1)))
  calc
    _ = ∑' r : AdmissibleResidue c,eisEmbedding (symbol c t*symbol c (denominatorRep c r.1)) := by
      simp only [map_mul,tsum_mul_left]
    _ = _ := by
      convert (preTransparency := .instances) heq using 1
      apply tsum_congr
      intro r
      exact congrArg eisEmbedding (residueMultiplication_phase c hlevel t ht r).symm

theorem arithmeticResidueSum_ne_zero_forces_trivial (c : O) (hc : c ≠ 0)
    (hlevel : (3:O) ∣ c) (hA : arithmeticResidueSum 0 c ≠ 0) :
    ∀ t : O, denominatorCondition c t → symbol c t=1 := by
  intro t ht
  apply eisEmbedding_injective
  rw [map_one]
  apply (mul_right_cancel₀ hA)
  rw [arithmeticResidueSum_constant_eigen c hc hlevel t ht,one_mul]

end CubicEisenstein

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

lemma coprime_of_dvd_sub_one (a b : O) (h : a ∣ b-1) : IsCoprime a b := by
  obtain ⟨r,hr⟩ := h
  exact ⟨-r,1,by linear_combination hr⟩

lemma primary_coprime_three (p : O) (hp : lambda^2 ∣ p-1) : IsCoprime p (3:O) :=
  (coprime_of_dvd_sub_one 3 p (three_dvd_primary_sub_one p hp)).symm

lemma exists_one_mod_and_prescribed (p m x : O) (hpm : IsCoprime p m) :
    ∃ t : O, m ∣ t-1 ∧ p ∣ t-x := by
  obtain ⟨r,u,hu⟩ := hpm
  refine ⟨1+m*u*(x-1),⟨u*(x-1),by ring⟩,⟨-r*(x-1),?_⟩⟩
  linear_combination (x-1)*hu

theorem constant_coefficient_primary_prime_exponent (c p b : O) (n : ℕ)
    (hc : c ≠ 0) (hlevel : (3:O) ∣ c) (hp : Prime p) (hprimary : lambda^2 ∣ p-1)
    (hpb : ¬p ∣ b) (hfactor : c=p^n*b) (hA : arithmeticResidueSum 0 c ≠ 0) :
    3 ∣ n := by
  by_contra hn
  let P : Ideal O := Ideal.span {p}
  let : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ P := primary_maximal_divisor_good p hprimary P (Ideal.subset_span (by simp []))
  have hchar : (cubicChar P hg)^n ≠ 1 := by
    intro heq
    have hd := orderOf_dvd_of_pow_eq_one heq
    rw [cubicChar_order P hg] at hd
    exact hn hd
  obtain ⟨u,hu⟩ := MulChar.ne_one_iff.mp hchar
  rw [MulChar.pow_apply_coe] at hu
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective (u : O ⧸ P)
  have hp9 : IsCoprime p (9:O) := by
    simpa only [show (3:O)^2=9 by norm_num] using (primary_coprime_three p hprimary).pow_right (n := 2)
  have hpm : IsCoprime p (9*b) := hp9.mul_right (hp.coprime_iff_not_dvd.mpr hpb)
  obtain ⟨t,htm,htp⟩ := exists_one_mod_and_prescribed p (9*b) x hpm
  have h9 : (9:O) ∣ t-1 := (dvd_mul_right 9 b).trans htm
  have hb : b ∣ t-1 := (dvd_mul_left b 9).trans htm
  have h3 : (3:O) ∣ t-1 := (show (3:O) ∣ 9 from ⟨3,by norm_num⟩).trans h9
  have htprimary : lambda^2 ∣ t-1 := lambda_sq_dvd_three.trans h3
  have htu : Ideal.Quotient.mk P t=(u : O ⧸ P) := by
    rw [← hx]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.mem_span_singleton.mpr htp)
  have hpt : IsCoprime p t := hp.coprime_iff_not_dvd.mpr (by
    intro hdiv
    have hz : Ideal.Quotient.mk P t=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)
    rw [htu] at hz
    exact Units.ne_zero u hz)
  have hbt : IsCoprime b t := coprime_of_dvd_sub_one b t hb
  have hct : IsCoprime c t := by
    rw [hfactor]
    exact hpt.pow_left.mul_left hbt
  have htriv := arithmeticResidueSum_ne_zero_forces_trivial c hc hlevel hA t ⟨hct,h3⟩
  have hbsym : symbol b t=1 := by
    have hh := symbol_denominator_congr b t 1 htprimary (by simp) h9 hb
    simpa only [symbol_one] using hh
  have hpsym : symbol p t=cubicChar P hg (u : O ⧸ P) := by
    rw [symbol_reciprocity p t hp.ne_zero (primary_ne_zero t htprimary) hprimary htprimary]
    change idealSymbol P t=_
    rw [idealSymbol_prime P hg,htu]
  rw [hfactor,symbol_mul_numerator _ _ t htprimary,symbol_pow_numerator p t htprimary,
    hbsym,mul_one,hpsym] at htriv
  exact hu htriv

end CubicEisenstein

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace CubicEisenstein
open MeasureTheory Set Filter
open scoped BigOperators Classical

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid

lemma multiset_cube_remainder {α : Type*} [DecidableEq α] (s : Multiset α) (p : α)
    (hdiv : ∀ q, q ≠ p → 3 ∣ s.count q) :
    ∃ t : Multiset α, s=(s.count p % 3) • {p} + 3 • t := by
  let t := Finsupp.toMultiset (s.toFinsupp.mapRange (fun n : ℕ => n/3) (by decide))
  refine ⟨t,?_⟩
  apply Multiset.ext.mpr
  intro q
  simp only [Multiset.count_add,Multiset.count_nsmul,Multiset.count_singleton,
    t,Finsupp.count_toMultiset,Finsupp.mapRange_apply,Multiset.toFinsupp_apply]
  by_cases hq : q=p
  · subst q
    simp only [ite_true,mul_one]
    omega
  · simp only [hq,ite_false,mul_zero,zero_add]
    exact (Nat.mul_div_cancel' (hdiv q hq)).symm

lemma residue_lambda_prime : Prime lambda := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'

lemma constant_coefficient_unramified_count [NormalizationMonoid O]
    (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) (hA : arithmeticResidueSum 0 c ≠ 0)
    (q : O) (hq : q ≠ normalize lambda) : 3 ∣ (normalizedFactors c).count q := by
  by_cases hmem : q ∈ normalizedFactors c
  · have hprime := prime_of_normalized_factor q hmem
    let P : Ideal O := Ideal.span {q}
    let : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hprime.irreducible
    have hg : lambda ∉ P := by
      intro hl
      have ha : Associated q lambda :=
        hprime.associated_of_dvd residue_lambda_prime (Ideal.mem_span_singleton.mp hl)
      apply hq
      exact (normalize_normalized_factor q hmem).symm.trans
        (normalize_eq_normalize_iff_associated.mpr ha)
    obtain ⟨p,hP,hprimary,-⟩ := cubicJacobi_exists_primary_generator P hg
    have hqp : Associated q p := Ideal.span_singleton_eq_span_singleton.mp hP
    have hp : Prime p := hqp.prime_iff.mp hprime
    obtain ⟨b,hfactor,hpb⟩ := (FiniteMultiplicity.of_prime_left hp hc).exists_eq_pow_mul_and_not_dvd
    have hd := constant_coefficient_primary_prime_exponent c p b (multiplicity p c)
      hc hlevel hp hprimary hpb hfactor hA
    have hcount := multiplicity_eq_count_normalizedFactors hprime.irreducible hc
    rw [normalize_normalized_factor q hmem] at hcount
    rw [← hcount,← multiplicity_eq_of_associated_left hqp]
    exact hd
  · rw [Multiset.count_eq_zero.mpr hmem]
    exact dvd_zero _

theorem constant_coefficient_cube_reduction (c : O) (hc : c ≠ 0)
    (hlevel : (3:O) ∣ c) (hA : arithmeticResidueSum 0 c ≠ 0) :
    ∃ (u : Oˣ) (r : ℕ) (a : O), r < 3 ∧ c=(u:O)*lambda^r*a^3 := by
  let : StrongNormalizationMonoid O := UniqueFactorizationMonoid.strongNormalizationMonoid
  let s := normalizedFactors c
  obtain ⟨t,ht⟩ := multiset_cube_remainder s (normalize lambda)
    (constant_coefficient_unramified_count c hc hlevel hA)
  let r := s.count (normalize lambda) % 3
  have hprod : s.prod=(normalize lambda)^r*t.prod^3 := by
    rw [ht,Multiset.prod_add,Multiset.prod_nsmul,Multiset.prod_singleton,Multiset.prod_nsmul]
  have hassoc : Associated (lambda^r*t.prod^3) c := by
    have hnorm : Associated ((normalize lambda)^r*t.prod^3) (lambda^r*t.prod^3) :=
      (normalize_associated lambda).pow_pow.mul_right _
    apply hnorm.symm.trans
    rw [← hprod]
    exact prod_normalizedFactors hc
  obtain ⟨u,hu⟩ := hassoc
  refine ⟨u,r,t.prod,Nat.mod_lt _ (by decide),?_⟩
  rw [← hu]
  ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified

lemma constant_coefficient_ramified_equation (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c)
    (hA : arithmeticResidueSum 0 c ≠ 0) (u : Oˣ) (r : ℕ) (a : O) (ha : a ≠ 0)
    (hfactor : c=(u:O)*lambda^r*a^3) (A B : ℤ) :
    symbol (u:O) (primaryCoord A B)*(cubicExp A)^r=1 := by
  let t0 := primaryCoord A B
  have ht0 : lambda^2 ∣ t0-1 := primaryCoord_primary A B
  obtain ⟨w,hw⟩ := exists_coprime_three_shift t0 3 a ht0 (primary_coprime_three t0 ht0) ha
  let t := t0+3*w*3
  have ht : lambda^2 ∣ t-1 := primary_add_multiple_three t0 3 w ht0
  have h9 : (9:O) ∣ t-t0 := ⟨w,by dsimp [t]; ring⟩
  have hat : IsCoprime a t := hw.symm
  have hlt : IsCoprime lambda t :=
    coprime_of_dvd_sub_one lambda t ((show lambda ∣ lambda^2 from ⟨lambda,by ring⟩).trans ht)
  have hct : IsCoprime c t := by
    rw [hfactor,show (u:O)*lambda^r*a^3=(u:O)*(lambda^r*a^3) by ring]
    apply (isCoprime_mul_unit_left_left u.isUnit _ _).mpr
    exact hlt.pow_left.mul_left hat.pow_left
  have htriv := arithmeticResidueSum_ne_zero_forces_trivial c hc hlevel hA t
    ⟨hct,three_dvd_primary_sub_one t ht⟩
  have hacube : symbol (a^3) t=1 := by
    rw [symbol_pow_numerator a t ht 3]
    exact symbol_cube_of_isCoprime a t ht hat
  rw [hfactor,symbol_mul_numerator _ _ t ht,symbol_mul_numerator _ _ t ht,
    symbol_pow_numerator lambda t ht r,hacube,mul_one,
    symbol_unit_congr_mod_nine (u:O) t t0 u.isUnit ht ht0 h9,
    symbol_lambda_congr_mod_nine t t0 ht ht0 h9,
    symbol_lambda_eq_linearRay t0 ht0] at htriv
  simpa only [t0,linearRay_primaryCoord,one_mul,zero_mul,add_zero] using htriv

lemma unit_eq_sign_of_symbol_class (u : Oˣ)
    (hu : symbol (u:O) (primaryCoord 0 1)=1) : (u:O)=1 ∨ (u:O)=-1 := by
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η:O)=omega := rfl
  have hlist : u ∈ ([1,-1,η,-η,η^2,-η^2] : List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  have hω : symbol omega (primaryCoord 0 1)=omega^2 := by
    rw [symbol_omega_eq_linearRay _ (primaryCoord_primary 0 1),linearRay_primaryCoord]
    norm_num [cubicExp]
  have hω2 : symbol (omega^2) (primaryCoord 0 1)=omega^4 := by
    rw [symbol_pow_numerator omega _ (primaryCoord_primary 0 1) 2,hω,← pow_mul]
  have hn2 : omega^2 ≠ 1 := (omega_primitive.pow_eq_one_iff_dvd 2).not.mpr (by decide)
  have hn4 : omega^4 ≠ 1 := (omega_primitive.pow_eq_one_iff_dvd 4).not.mpr (by decide)
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hlist
  rcases hlist with h | h | h | h | h | h
  · exact Or.inl (by rw [h,Units.val_one])
  · exact Or.inr (by rw [h,Units.val_neg,Units.val_one])
  · exact False.elim (hn2 (by simpa only [h,hη,hω] using hu))
  · exact False.elim (hn2 (by simpa only [h,Units.val_neg,hη,
      (symbol_neg_numerator _ _ (primaryCoord_primary 0 1)),hω] using hu))
  · exact False.elim (hn4 (by simpa only [h,Units.val_pow_eq_pow_val,hη,hω2] using hu))
  · exact False.elim (hn4 (by simpa only [h,Units.val_neg,Units.val_pow_eq_pow_val,hη,
      (symbol_neg_numerator _ _ (primaryCoord_primary 0 1)),hω2] using hu))

theorem arithmeticResidueSum_ne_zero_implies_cube (c : O) (hc : c ≠ 0)
    (hlevel : (3:O) ∣ c) (hA : arithmeticResidueSum 0 c ≠ 0) : ∃ a : O,c=a^3 := by
  obtain ⟨u,r,a,hr,hfactor⟩ := constant_coefficient_cube_reduction c hc hlevel hA
  have ha : a ≠ 0 := by
    intro hz
    rw [hz,zero_pow (by decide : (3:ℕ) ≠ 0),mul_zero] at hfactor
    exact hc hfactor
  have h01 := constant_coefficient_ramified_equation c hc hlevel hA u r a ha hfactor 0 1
  have husign := unit_eq_sign_of_symbol_class u (by
    simpa only [cubicExp_zero,one_pow,mul_one] using h01)
  have h10 := constant_coefficient_ramified_equation c hc hlevel hA u r a ha hfactor 1 0
  have hωr : omega^r=1 := by
    rcases husign with hu | hu
    · simpa only [hu,symbol_one_numerator _ (primaryCoord_primary 1 0),one_mul,
        cubicExp,Int.reduceMod,Int.toNat_one,pow_one] using h10
    · simpa only [hu,symbol_neg_one _ (primaryCoord_primary 1 0),one_mul,
        cubicExp,Int.reduceMod,Int.toNat_one,pow_one] using h10
  have hdiv : 3 ∣ r := (omega_primitive.pow_eq_one_iff_dvd r).mp hωr
  have hr0 : r=0 := by omega
  rw [hr0,pow_zero,mul_one] at hfactor
  rcases husign with hu | hu
  · refine ⟨a,?_⟩
    simpa only [hu,one_mul] using hfactor
  · refine ⟨-a,?_⟩
    rw [hfactor,hu]
    ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

theorem arithmeticResidueSum_ne_zero_iff_cube (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) :
    arithmeticResidueSum 0 c ≠ 0 ↔ ∃ a : O,c=a^3 := by
  constructor
  · exact arithmeticResidueSum_ne_zero_implies_cube c hc hlevel
  · rintro ⟨a,rfl⟩
    have ha : a ≠ 0 := fun h => hc (by rw [h]; norm_num)
    exact arithmeticResidueSum_cube_ne_zero a ha

end CubicEisenstein

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

def idealZeroMask (D : Ideal O) (z : O) : ℂ :=
  if ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, z ∈ P then 0 else 1

def gcdMaskPrimes (D : Ideal O) : Finset (Ideal O) :=
  {Ideal.span {lambda}, Ideal.span {(2 : O)}} ∪
    (UniqueFactorizationMonoid.normalizedFactors D).toFinset

instance gcdMaskPrimes_maximal (D : Ideal O) (P : gcdMaskPrimes D) : P.val.IsMaximal := by
  rcases Finset.mem_union.mp P.property with hp | hp
  · rcases Finset.mem_insert.mp hp with hp | hp
    · rw [hp]
      exact lambdaIdeal_maximal
    · rw [Finset.mem_singleton.mp hp]
      exact twoIdeal_maximal
  · have h := UniqueFactorizationMonoid.prime_of_normalized_factor P.val (Multiset.mem_toFinset.mp hp)
    exact (Ideal.isPrime_of_prime h).isMaximal h.ne_zero

end
section

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates
open EisensteinSchwartzPoisson GaussGeneratorTransport QuadraticUnitInvariance

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates
open EisensteinSchwartzPoisson GaussGeneratorTransport QuadraticUnitInvariance PrimaryIdealUnitReindex

theorem canonical_pair_unit_invariant (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (u : Oˣ) (z : O) :
    quadraticRow I (u.val * z) * quadraticRow J (u.val * z) =
      quadraticRow I z * quadraticRow J z := by
  let F : Finset (Ideal O) := {I, J}
  have hF : ∀ lengthScale ∈ F, Admissible lengthScale := by
    intro lengthScale hL
    rcases Finset.mem_insert.mp hL with rfl | hL
    · exact hI
    · have hLJ := Finset.mem_singleton.mp hL
      simpa only [hLJ] using hJ
  have hIF : I ∈ F := by simp [F]
  have hJF : J ∈ F := by simp [F]
  let p := poolPrimary F
  let A := idealSupport F I
  let B := idealSupport F J
  let : ∀ i : primePool F, (Ideal.span {p i}).IsMaximal :=
    fun i => by change (Ideal.span {poolPrimary F i}).IsMaximal; rw [poolPrimary_span F hF i]; infer_instance
  have hcA : Pairwise (Function.onFun IsCoprime (fun i : A => Ideal.span {p i.val})) :=
    fun i j hij => poolPrimary_coprime F hF (fun h => hij (Subtype.ext h))
  have hcB : Pairwise (Function.onFun IsCoprime (fun i : B => Ideal.span {p i.val})) :=
    fun i j hij => poolPrimary_coprime F hF (fun h => hij (Subtype.ext h))
  have hr : residue (∏ i : A, p i.val) = residue (∏ i : B, p i.val) := by
    rw [Finset.prod_coe_sort, Finset.prod_coe_sort,
      ← primaryGenerator_eq_poolProduct F hF I hIF, ← primaryGenerator_eq_poolProduct F hF J hJF]
    exact hray
  have h := quadratic_pair_unit_invariant
    (fun i : A => p i.val) (fun i => poolPrimary_ne_zero F hF i.val) hcA
    (fun i => poolPrimary_good F hF i.val) (fun i => poolPrimary_odd F hF i.val)
    (fun i : B => p i.val) (fun i => poolPrimary_ne_zero F hF i.val) hcB
    (fun i => poolPrimary_good F hF i.val) (fun i => poolPrimary_odd F hF i.val) hr u z
  have hrowI (w : O) : finiteSexticRow (fun i : A => Ideal.span {p i.val})
      (fun i => poolPrimary_good F hF i.val) (fun _ => 3) w = quadraticRow I w :=
    (quadraticRow_eq_primarySubset F hF I hIF w).symm
  have hrowJ (w : O) : finiteSexticRow (fun i : B => Ideal.span {p i.val})
      (fun i => poolPrimary_good F hF i.val) (fun _ => 3) w = quadraticRow J w :=
    (quadraticRow_eq_primarySubset F hF J hJF w).symm
  simpa only [hrowI, hrowJ] using h

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge
open EisensteinSchwartzPoisson GaussGeneratorTransport PrimaryIdealUnitReindex

theorem supported_primaryGenerator_ne_zero (lengthScale : Ideal O) (hL : Supported lengthScale) :
    primaryGenerator lengthScale ≠ 0 :=
  primaryGenerator_ne_zero_of_good_factors lengthScale hL.1 (fun P hP => (hL.2 P hP).1)

theorem supported_span_primaryGenerator_iff (lengthScale : Ideal O) :
    Supported (Ideal.span {primaryGenerator lengthScale}) ↔ Supported lengthScale := by
  constructor
  · intro h
    have hn : primaryGenerator lengthScale ≠ 0 := by
      intro hz
      apply h.1
      simp [hz]
    rwa [(primaryGenerator_spec lengthScale hn).1] at h
  · intro h
    rw [(primaryGenerator_spec lengthScale (supported_primaryGenerator_ne_zero lengthScale h)).1]
    exact h

end CanonicalQuadraticSieve

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

section
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge QuadraticSquarefreeKernel

theorem supported_mul_iff (A B : Ideal O) : Supported (A * B) ↔ Supported A ∧ Supported B := by
  constructor
  · intro h
    have hA : A ≠ 0 := left_ne_zero_of_mul h.1
    have hB : B ≠ 0 := right_ne_zero_of_mul h.1
    refine ⟨⟨hA, ?_⟩, ⟨hB, ?_⟩⟩
    · intro P hP
      apply h.2 P
      rw [UniqueFactorizationMonoid.normalizedFactors_mul hA hB]
      exact Multiset.mem_add.mpr (Or.inl hP)
    · intro P hP
      apply h.2 P
      rw [UniqueFactorizationMonoid.normalizedFactors_mul hA hB]
      exact Multiset.mem_add.mpr (Or.inr hP)
  · rintro ⟨hA, hB⟩
    refine ⟨mul_ne_zero hA.1 hB.1, ?_⟩
    intro P hP
    rw [UniqueFactorizationMonoid.normalizedFactors_mul hA.1 hB.1] at hP
    rcases Multiset.mem_add.mp hP with hP | hP
    · exact hA.2 P hP
    · exact hB.2 P hP

theorem supported_sq_iff (A : Ideal O) : Supported (A ^ 2) ↔ Supported A := by
  rw [pow_two, supported_mul_iff, and_self]

theorem supported_square_parts (lengthScale : Ideal O) :
    Supported lengthScale ↔ Supported (squarePart lengthScale) ∧ Admissible (squarefreePart lengthScale) := by
  have he := supported_mul_iff (squarePart lengthScale ^ 2) (squarefreePart lengthScale)
  rw [squarePart_sq_mul_squarefreePart, supported_sq_iff] at he
  rw [he]
  have hsf := squarefree_squarefreePart lengthScale
  constructor
  · rintro ⟨hA, hB⟩
    exact ⟨hA, hB.1, hsf, hB.2⟩
  · rintro ⟨hA, hB⟩
    exact ⟨hA, hB.1, hB.2.2⟩

def supportedSquarefreeEquiv : {lengthScale : Ideal O // Supported lengthScale} ≃
    ({A : Ideal O // Supported A} × {B : Ideal O // Admissible B}) where
  toFun lengthScale := (⟨squarePart lengthScale.val, ((supported_square_parts lengthScale.val).mp lengthScale.property).1⟩,
    ⟨squarefreePart lengthScale.val, ((supported_square_parts lengthScale.val).mp lengthScale.property).2⟩)
  invFun p := ⟨p.1.val ^ 2 * p.2.val,
    (supported_mul_iff _ _).mpr ⟨(supported_sq_iff _).mpr p.1.property, admissible_supported p.2.property⟩⟩
  left_inv lengthScale := Subtype.ext (squarePart_sq_mul_squarefreePart lengthScale.val)
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (squarePart_mul_squarefree p.1.property.1 p.2.property.2.1).1
    · exact Subtype.ext (squarePart_mul_squarefree p.1.property.1 p.2.property.2.1).2

theorem canonical_quadraticRow_argument_mul (D : Ideal O) (hD : Admissible D) (a b : O) :
    quadraticRow D (a * b) = quadraticRow D a * quadraticRow D b := by
  let F : Finset (Ideal O) := {D}
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    have hID := Finset.mem_singleton.mp hI
    simpa only [hID] using hD
  simp only [quadraticRow_eq_pool F hF D (Finset.mem_singleton_self D)]
  exact QuadraticSquarefreeKernel.quadraticRow_mul _ _ _ a b

end

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open EisensteinSchwartzPoisson PrimaryIdealUnitReindex QuadraticSquarefreeKernel

def originalPairSource (I J : Ideal O) (W : ℝ → ℂ) (M : ℝ) (lengthScale : Ideal O) : ℂ :=
  if Supported lengthScale then (star (quadraticRow I (primaryGenerator lengthScale)) *
    quadraticRow J (primaryGenerator lengthScale)) * W ((Ideal.absNorm lengthScale : ℝ) / M) else 0

def originalPairLow (I J : Ideal O) (W : ℝ → ℂ) (M K : ℝ) (lengthScale : Ideal O) : ℂ :=
  if (Ideal.absNorm (squarefreePart lengthScale) : ℝ) ≤ K then originalPairSource I J W M lengthScale else 0

def originalPairHigh (I J : Ideal O) (W : ℝ → ℂ) (M K : ℝ) (lengthScale : Ideal O) : ℂ :=
  if K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then originalPairSource I J W M lengthScale else 0

end

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss QuadraticSquarefreeKernel

def rayPairCoefficient (N : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) (I J : idealRange N) : ℂ :=
  if gcd I.val J.val = D ∧ columnRay I.val = c ∧ columnRay J.val = c then star (a I) * a J else 0

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport

def originalPairDualKernel (D I J : Ideal O) (W : ℝ → ℂ) (M : ℝ) : ℂ :=
  let I' := idealQuotient D I
  let J' := idealQuotient D J
  let n := primaryGenerator I' * primaryGenerator J'
  let χ := fun z => quadraticRow I' z * quadraticRow J' z
  let R := fun P : gcdMaskPrimes D => P.val
  ((M : ℂ) / (6 * ‖eisEmbedding n‖ : ℂ)) *
    ∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
      let d := primeSubsetGenerator R E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
      ∑' h : O, χ h * paperRadialFourier W
        (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap ContDiff

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
namespace SecondPassArithmetic

section
open ActualEisensteinCubic

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def secondSourcePairKernel (e k : O) (H₁ H₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (S T : Finset ι) : ℂ :=
  (star (H₁ S) * H₂ T /
    ((‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ) * (‖eisEmbedding (∏ i ∈ T, p i)‖ : ℂ))) *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * (primeProductNorm p S * primeProductNorm p T)))

def secondSourceCommonCoefficient (Ψ : O →* ℂ) (m c d : O) (G E : Finset ι) : ℂ :=
  (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ) *
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
      (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ))

def truncatedSecondSource (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) : ℂ :=
  ∑ G ∈ F.powerset, ∑ E : G.powerset, ∑ k ∈ K G E.val,
    secondSourceCommonCoefficient p hg Ψ m c d G E.val *
      secondFrequencyKernel p hp hg hinj F Ψ Ψ m
        (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
        (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y

def secondSourceTail (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) : ℂ :=
  ∑ G ∈ F.powerset, ∑ E : G.powerset,
    secondSourceCommonCoefficient p hg Ψ m c d G E.val *
      ∑' k : {k : O // k ∉ K G E.val},
        secondFrequencyKernel p hp hg hinj F Ψ Ψ m
          (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k.val
          (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

@[ext] structure SecondExpansionData (ι : Type*) where
  sourceCommon : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  frequency : O
  deriving DecidableEq

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical
namespace UnrestrictedIdealReindex
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open PrimaryIdealUnitReindex CanonicalQuadraticSieve

abbrev NonzeroIdeal := {I : Ideal O // I ≠ 0}
abbrev NonzeroElement := {z : O // z ≠ 0}

theorem span_unit_generator (u : Oˣ) (I : NonzeroIdeal) :
    Ideal.span {u.val * idealGenerator I.val} = I.val := by
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, span_idealGenerator]

def unitIdealToElement (p : Oˣ × NonzeroIdeal) : NonzeroElement :=
  ⟨p.1.val * idealGenerator p.2.val, mul_ne_zero p.1.ne_zero (idealGenerator_ne_zero p.2.val p.2.property)⟩

theorem unitIdealToElement_bijective : Function.Bijective unitIdealToElement := by
  constructor
  · intro p q hpq
    have he : p.1.val * idealGenerator p.2.val = q.1.val * idealGenerator q.2.val := congrArg Subtype.val hpq
    have hi : p.2 = q.2 := by
      apply Subtype.ext
      simpa only [span_unit_generator] using congrArg (fun z : O => Ideal.span {z}) he
    have hu : p.1 = q.1 := by
      apply Units.ext
      rw [hi] at he
      exact mul_right_cancel₀ (idealGenerator_ne_zero q.2.val q.2.property) he
    exact Prod.ext hu hi
  · intro z
    let I : NonzeroIdeal := ⟨Ideal.span {z.val}, Ideal.span_singleton_eq_bot.not.mpr z.property⟩
    have ha : Associated (idealGenerator I.val) z.val :=
      Ideal.span_singleton_eq_span_singleton.mp (span_idealGenerator I.val)
    obtain ⟨u, hu⟩ := ha
    refine ⟨(u, I), Subtype.ext ?_⟩
    change u.val * idealGenerator I.val = z.val
    simpa only [mul_comm] using hu

def unitIdealEquiv : Oˣ × NonzeroIdeal ≃ NonzeroElement :=
  Equiv.ofBijective unitIdealToElement unitIdealToElement_bijective

theorem tsum_nonzero_unit_invariant (f : O → ℂ) (hf : Summable f)
    (hu : ∀ (u : Oˣ) (z : O), f (u.val * z) = f z) :
    (∑' z : NonzeroElement, f z.val) = (6 : ℂ) * ∑' I : NonzeroIdeal, f (idealGenerator I.val) := by
  let : Finite Oˣ := finite_units
  let : Fintype Oˣ := Fintype.ofFinite _
  have he : (∑' z : NonzeroElement, f z.val) =
      ∑' p : Oˣ × NonzeroIdeal, f (p.1.val * idealGenerator p.2.val) :=
    (unitIdealEquiv.tsum_eq (fun z : NonzeroElement => f z.val)).symm
  have hs : Summable (fun p : Oˣ × NonzeroIdeal => f (p.1.val * idealGenerator p.2.val)) :=
    unitIdealEquiv.summable_iff.mpr (hf.subtype _)
  rw [he, hs.tsum_prod]
  simp only [hu, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : Fintype.card Oˣ = 6 := by simpa only [Nat.card_eq_fintype_card] using card_units_eq_six
  rw [hc]
  norm_num

theorem tsum_unit_invariant_of_zero (f : O → ℂ) (hf : Summable f) (h0 : f 0 = 0)
    (hu : ∀ (u : Oˣ) (z : O), f (u.val * z) = f z) :
    (∑' z : O, f z) = (6 : ℂ) * ∑' I : NonzeroIdeal, f (idealGenerator I.val) := by
  have he : (∑' z : NonzeroElement, f z.val) = ∑' z : O, f z := by
    apply tsum_subtype_eq_of_support_subset
    intro z hz
    exact fun hz0 => hz (hz0 ▸ h0)
  rw [← he]
  exact tsum_nonzero_unit_invariant f hf hu

end UnrestrictedIdealReindex

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss

def unrestrictedPairCharacter (I J lengthScale : Ideal O) : ℂ :=
  quadraticRow I (idealGenerator lengthScale) * quadraticRow J (idealGenerator lengthScale)

theorem unrestrictedPairCharacter_span (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (z : O) :
    unrestrictedPairCharacter I J (Ideal.span {z}) = quadraticRow I z * quadraticRow J z := by
  have ha : Associated (idealGenerator (Ideal.span {z})) z :=
    Ideal.span_singleton_eq_span_singleton.mp (span_idealGenerator _)
  obtain ⟨u, hu⟩ := ha
  have hv := canonical_pair_unit_invariant I J hI hJ hray u (idealGenerator (Ideal.span {z}))
  have he : u.val * idealGenerator (Ideal.span {z}) = z := by simpa only [mul_comm] using hu
  rw [he] at hv
  exact hv.symm

theorem unrestrictedPairCharacter_mul (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (A B : Ideal O) :
    unrestrictedPairCharacter I J (A * B) =
      unrestrictedPairCharacter I J A * unrestrictedPairCharacter I J B := by
  have hs : Ideal.span {idealGenerator A * idealGenerator B} = A * B := by
    rw [← Ideal.span_singleton_mul_span_singleton, span_idealGenerator, span_idealGenerator]
  rw [← hs, unrestrictedPairCharacter_span I J hI hJ hray]
  rw [canonical_quadraticRow_argument_mul I hI, canonical_quadraticRow_argument_mul J hJ]
  unfold unrestrictedPairCharacter
  ring

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex GaussGeneratorTransport

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open IdealMobiusDivisorSum

def fixedBadPrimes : Finset (Ideal O) := {Ideal.span {lambda}, Ideal.span {(2 : O)}}

theorem prime_good_iff_not_bad (P : Ideal O) [P.IsMaximal] :
    (lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2) ↔ P ∉ fixedBadPrimes := by
  constructor
  · rintro ⟨hl, hc⟩ hp
    rcases Finset.mem_insert.mp hp with hp | hp
    · exact hl (hp ▸ Ideal.subset_span (by simp))
    · have he : P = Ideal.span {(2 : O)} := Finset.mem_singleton.mp hp
      exact hc (he ▸ twoIdeal_characteristic)
  · intro hp
    constructor
    · intro hl
      have he := maximal_ideal_eq_span_of_mem P inferInstance lambda lambdaIdeal_maximal hl
      exact hp (he ▸ Finset.mem_insert_self _ _)
    · intro hc
      have ht : (2 : O) ∈ P := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        have hz : (2 : O ⧸ P) = 0 := (ringChar.spec (O ⧸ P) 2).mpr (by rw [hc])
        simpa only [map_ofNat] using hz
      have he := maximal_ideal_eq_span_of_mem P inferInstance (2 : O) twoIdeal_maximal ht
      exact hp (he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

def badPrimeSupport (I : Ideal O) : Finset (Ideal O) := IdealMobiusDivisorSum.primeSupport I ∩ fixedBadPrimes

def goodPrimeSupport (I : Ideal O) : Finset (Ideal O) := IdealMobiusDivisorSum.primeSupport I \ fixedBadPrimes

def goodSquarefreePart (I : Ideal O) : Ideal O := ∏ P ∈ goodPrimeSupport I, P

theorem badPrimeSupport_subset (I : Ideal O) : badPrimeSupport I ⊆ fixedBadPrimes :=
  Finset.inter_subset_right

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge

def badPrimeSector (I : Ideal O) : fixedBadPrimes.powerset :=
  ⟨badPrimeSupport I, Finset.mem_powerset.mpr (badPrimeSupport_subset I)⟩

end
section

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport UnrestrictedIdealReindex

def originalPairIdealDualKernel (D I J : Ideal O) (W : ℝ → ℂ) (M : ℝ) : ℂ :=
  let I' := idealQuotient D I
  let J' := idealQuotient D J
  let n := primaryGenerator I' * primaryGenerator J'
  let χ := fun z => quadraticRow I' z * quadraticRow J' z
  let R := fun P : gcdMaskPrimes D => P.val
  ((M : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
    ∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
      let d := primeSubsetGenerator R E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
      ∑' lengthScale : NonzeroIdeal, unrestrictedPairCharacter I' J' lengthScale.val * paperRadialFourier W
        (M * (Ideal.absNorm lengthScale.val : ℝ) / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open QuadraticSquarefreeKernel UnrestrictedIdealReindex

end CanonicalQuadraticSieve

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform

open scoped BigOperators Classical
namespace SecondPassArithmetic

section

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm jLabel)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondExpansionQuotient (x : SecondExpansionData ι) : O :=
  if h : x.divisor ⊆ x.sourceCommon then
    secondMaskQuotient p x.divisor x.sourceCommon h else 0

omit [∀ (i : ι), (span {p i}).IsMaximal] in
@[simp] theorem secondExpansionQuotient_of_subset (x : SecondExpansionData ι)
    (h : x.divisor ⊆ x.sourceCommon) :
    secondExpansionQuotient p x = secondMaskQuotient p x.divisor x.sourceCommon h := by
  simp [secondExpansionQuotient, h]

end

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def secondExpansionSource
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (s : Finset (SecondExpansionData ι)) (H₁ H₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑ x ∈ s,
    ((Y : ℂ) * secondSourceCommonCoefficient p hg Ψ m c d x.sourceCommon x.divisor) *
    (secondTotalWeight p hp hcop hg Ψ Ψ m (secondExpansionQuotient p x) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (z,x.overlap) *
    secondChildKernelPair p hp hcop hg F x.overlap (secondRayMinus Ψ z) (secondRayPlus Ψ z)
      m (secondExpansionQuotient p x) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (-x.frequency)
      (secondSourcePairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
        x.frequency (fun A => H₁ (x.sourceCommon∪A)) (fun A => H₂ (x.sourceCommon∪A)) W Y))

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

end SecondPassArithmetic

open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

lemma isUnit_quotient_span_iff (c d : O) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {c}) d) ↔ IsCoprime c d := by
  constructor
  · intro hd
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hd
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hdiv : c ∣ d*b-1 := by
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_sub,map_mul,map_one,sub_eq_zero] using hb
    obtain ⟨k,hk⟩ := hdiv
    exact ⟨-k,b,by linear_combination hk⟩
  · rintro ⟨a,b,hab⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk (Ideal.span {c}) b, ?_⟩
    have hc : Ideal.Quotient.mk (Ideal.span {c}) c=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have h := congrArg (Ideal.Quotient.mk (Ideal.span {c})) hab
    simpa only [map_add,map_mul,map_one,hc,mul_zero,zero_mul,zero_add,mul_comm] using h

abbrev AffineUnitResidue (c : O) :=
  {u : O ⧸ Ideal.span {c} // IsUnit (1+3*u)}

lemma affine_representative_condition (c : O) (u : AffineUnitResidue c) :
    denominatorCondition c (1+3*GaussianShiftedPartition.representative c u.1) := by
  refine ⟨(isUnit_quotient_span_iff c _).mp ?_, ⟨_,by ring⟩⟩
  simpa only [map_add,map_mul,map_one,map_ofNat,
    GaussianShiftedPartition.representative_spec] using u.2

def affineResidueMap (c : O) (u : AffineUnitResidue c) : AdmissibleResidue c :=
  ⟨Ideal.Quotient.mk (Ideal.span {3*c})
    (1+3*GaussianShiftedPartition.representative c u.1), by
    apply (denominatorCondition_congr c _
      (1+3*GaussianShiftedPartition.representative c u.1) ?_).mpr
      (affine_representative_condition c u)
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    exact denominatorRep_spec c _⟩

lemma affineResidueMap_bijective (c : O) : Function.Bijective (affineResidueMap c) := by
  constructor
  · intro u v huv
    have hdiv : 3*c ∣ (1+3*GaussianShiftedPartition.representative c u.1)-
        (1+3*GaussianShiftedPartition.representative c v.1) := by
      apply Ideal.mem_span_singleton.mp
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (congrArg Subtype.val huv)
    obtain ⟨k,hk⟩ := hdiv
    have hk' : GaussianShiftedPartition.representative c u.1-
        GaussianShiftedPartition.representative c v.1=c*k := by
      have h3 : (3:O) ≠ 0 := by norm_num
      apply mul_left_cancel₀ h3
      linear_combination hk
    apply Subtype.ext
    rw [← GaussianShiftedPartition.representative_spec c u.1,
      ← GaussianShiftedPartition.representative_spec c v.1]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_span_singleton.mpr ⟨k,hk'⟩)
  · intro r
    obtain ⟨u,hu⟩ := r.2.2
    have hd : denominatorRep c r.1=1+3*u := by linear_combination hu
    let q : AffineUnitResidue c := ⟨Ideal.Quotient.mk (Ideal.span {c}) u, by
      have hh := (isUnit_quotient_span_iff c _).mpr r.2.1
      simpa only [hd,map_add,map_one,map_mul,map_ofNat] using hh⟩
    refine ⟨q,Subtype.ext ?_⟩
    change Ideal.Quotient.mk (Ideal.span {3*c})
      (1+3*GaussianShiftedPartition.representative c q.1)=r.1
    rw [← denominatorRep_spec c r.1,hd]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    have hrep : c ∣ GaussianShiftedPartition.representative c q.1-u := by
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      exact GaussianShiftedPartition.representative_spec c q.1
    obtain ⟨k,hk⟩ := hrep
    exact ⟨k,by linear_combination 3*hk⟩

def affineResidueEquiv (c : O) : AffineUnitResidue c ≃ AdmissibleResidue c :=
  Equiv.ofBijective (affineResidueMap c) (affineResidueMap_bijective c)

def unitsSubtypeEquiv (R : Type*) [Monoid R] : Rˣ ≃ {x : R // IsUnit x} where
  toFun u := ⟨u,u.isUnit⟩
  invFun x := x.2.unit
  left_inv u := Units.ext u.isUnit.unit_spec
  right_inv x := Subtype.ext x.2.unit_spec

def quotientProductEquiv (a b : O) (hab : IsCoprime a b) :
    (O ⧸ Ideal.span {a*b}) ≃+* (O ⧸ Ideal.span {a}) × (O ⧸ Ideal.span {b}) :=
  (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton a b).symm).trans
    (Ideal.quotientMulEquivQuotientProd _ _ ((Ideal.isCoprime_span_singleton_iff a b).mpr hab))

def affineCRTEq (a b : O) (hab : IsCoprime a b) :
    AffineUnitResidue (a*b) ≃ AffineUnitResidue a × AffineUnitResidue b :=
  ((quotientProductEquiv a b hab).toEquiv.subtypeEquiv (fun q => by
    rw [← MulEquiv.isUnit_map (quotientProductEquiv a b hab) (x := 1+3*q)]
    simp only [map_add,map_one,map_mul,map_ofNat,Prod.isUnit_iff]
    rfl)).trans Equiv.subtypeProdEquivProd

lemma affine_ramified_unit (n : ℕ) (q : O ⧸ Ideal.span {lambda^n}) : IsUnit (1+3*q) := by
  obtain ⟨d,rfl⟩ := Ideal.Quotient.mk_surjective q
  have hlam3 : lambda ∣ (3:O) :=
    (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans lambda_sq_dvd_three
  have hcop : IsCoprime lambda (1+3*d) :=
    coprime_of_dvd_sub_one _ _ (by convert (preTransparency := .instances) hlam3.mul_right d using 1 ; ring)
  have h := (isUnit_quotient_span_iff (lambda^n) (1+3*d)).mpr hcop.pow_left
  simpa only [map_add,map_one,map_mul,map_ofNat] using h

def affineRamifiedEquiv (n : ℕ) : AffineUnitResidue (lambda^n) ≃ (O ⧸ Ideal.span {lambda^n}) :=
  Equiv.subtypeUnivEquiv (affine_ramified_unit n)

def affineUnramifiedEquiv (m : O) (hm : IsCoprime m (3:O)) :
    AffineUnitResidue m ≃ (O ⧸ Ideal.span {m})ˣ := by
  let h3 : IsUnit (3 : O ⧸ Ideal.span {m}) := by
    simpa only [map_ofNat] using (isUnit_quotient_span_iff m 3).mpr hm
  let e : (O ⧸ Ideal.span {m}) ≃ (O ⧸ Ideal.span {m}) :=
    h3.unit.mulLeft.trans (Equiv.addLeft 1)
  refine (e.subtypeEquiv (fun q => ?_)).trans (unitsSubtypeEquiv _).symm
  change IsUnit (1+3*q) ↔ IsUnit (1+(h3.unit : O ⧸ Ideal.span {m})*q)
  rw [h3.unit_spec]

def idealTotient (I : Ideal O) : ℕ := Nat.card (O ⧸ I)ˣ

lemma card_admissible_ramified_product (n : ℕ) (m : O)
    (hm : IsCoprime m (3:O)) (hlamm : IsCoprime lambda m) :
    Nat.card (AdmissibleResidue (lambda^n*m)) =
      Nat.card (O ⧸ Ideal.span {lambda^n}) * idealTotient (Ideal.span {m}) := by
  calc
    _ = Nat.card (AffineUnitResidue (lambda^n*m)) :=
      Nat.card_congr (affineResidueEquiv _).symm
    _ = Nat.card (AffineUnitResidue (lambda^n) × AffineUnitResidue m) :=
      Nat.card_congr (affineCRTEq _ _ hlamm.pow_left)
    _ = Nat.card ((O ⧸ Ideal.span {lambda^n}) × (O ⧸ Ideal.span {m})ˣ) :=
      Nat.card_congr (Equiv.prodCongr (affineRamifiedEquiv n) (affineUnramifiedEquiv m hm))
    _ = _ := Nat.card_prod _ _

lemma absNorm_span_lambda : Ideal.absNorm (Ideal.span {lambda})=3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsCyclotomicExtension {3^(0+1)} ℚ ActualEisensteinCubic.K := by
    simpa using (inferInstance : IsCyclotomicExtension {3} ℚ ActualEisensteinCubic.K)
  exact IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one 3 0
    (IsCyclotomicExtension.zeta_spec 3 ℚ ActualEisensteinCubic.K)

lemma card_quotient_lambda_pow (n : ℕ) :
    Nat.card (O ⧸ Ideal.span {lambda^n})=3^n := by
  change Ideal.absNorm (Ideal.span {lambda^n})=3^n
  rw [← Ideal.span_singleton_pow,map_pow,absNorm_span_lambda]

theorem card_admissible_lambda_pow_mul (n : ℕ) (m : O)
    (hm : IsCoprime m (3:O)) :
    Nat.card (AdmissibleResidue (lambda^n*m)) = 3^n * idealTotient (Ideal.span {m}) := by
  have hlam3 : lambda ∣ (3:O) :=
    (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans lambda_sq_dvd_three
  rw [card_admissible_ramified_product n m hm
    (hm.symm.of_isCoprime_of_dvd_left hlam3),card_quotient_lambda_pow]

end CubicEisenstein

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace CubicEisenstein

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

def predicateFiberEquiv {R S : Type*} (f : R → S) (P : S → Prop) :
    {x : R // P (f x)} ≃ Σ y : {y : S // P y}, {x : R // f x=y.1} where
  toFun x := ⟨⟨f x.1,x.2⟩,⟨x.1,rfl⟩⟩
  invFun y := ⟨y.2.1,by rw [y.2.2]; exact y.1.2⟩
  left_inv x := rfl
  right_inv y := by
    rcases y with ⟨⟨y,hy⟩,x,hx⟩
    dsimp at hx
    cases hx
    rfl

def predicateKernelEquiv {R S : Type*} [AddGroup R] [AddGroup S]
    (f : R →+ S) (hf : Function.Surjective f) (P : S → Prop) :
    {x : R // P (f x)} ≃ {y : S // P y} × f.ker :=
  (predicateFiberEquiv f P).trans
    ((Equiv.sigmaCongrRight (fun y : {y : S // P y} =>
      AddMonoidHom.fiberEquivKerOfSurjective hf y.1)).trans (Equiv.sigmaEquivProd _ _))

lemma card_ring_eq_card_mul_kernel {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (hf : Function.Surjective f) :
    Nat.card R=Nat.card S*Nat.card f.toAddMonoidHom.ker := by
  have h := Nat.card_congr (predicateKernelEquiv f.toAddMonoidHom hf (fun _ => True))
  simpa only [Nat.card_prod,Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => True.intro))] using h

lemma card_units_eq_card_mul_kernel {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (hunit : ∀x, IsUnit (f x) ↔ IsUnit x) :
    Nat.card Rˣ=Nat.card Sˣ*Nat.card f.toAddMonoidHom.ker := by
  let e : Rˣ ≃ {x : R // IsUnit (f x)} :=
    (unitsSubtypeEquiv R).trans (Equiv.subtypeEquivRight (fun x => (hunit x).symm))
  calc
    _ = Nat.card ({y : S // IsUnit y} × f.toAddMonoidHom.ker) :=
      Nat.card_congr (e.trans (predicateKernelEquiv f.toAddMonoidHom hf IsUnit))
    _ = Nat.card {y : S // IsUnit y} * Nat.card f.toAddMonoidHom.ker := Nat.card_prod _ _
    _ = _ := by rw [← Nat.card_congr (unitsSubtypeEquiv S)]

lemma card_units_mul_card_target {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (hunit : ∀x, IsUnit (f x) ↔ IsUnit x) :
    Nat.card S*Nat.card Rˣ=Nat.card R*Nat.card Sˣ := by
  rw [card_units_eq_card_mul_kernel f hf hunit,card_ring_eq_card_mul_kernel f hf]
  ring

theorem idealTotient_pow_succ (I : Ideal O) (hI : I ≠ 0) (n : ℕ) :
    idealTotient (I ^(n+1))=Ideal.absNorm I ^n*idealTotient I := by
  let f : (O ⧸ I ^(n+1)) →+* (O ⧸ I) :=
    Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero n))
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective _
  have hu (x : O ⧸ I ^(n+1)) : IsUnit (f x) ↔ IsUnit x := by
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk I (Nat.succ_ne_zero n)).symm
  have h := card_units_mul_card_target f hf hu
  change Ideal.absNorm I*idealTotient (I ^(n+1))=
    Ideal.absNorm (I ^(n+1))*idealTotient I at h
  rw [map_pow] at h
  have hpos : 0<Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    _ = Ideal.absNorm I ^(n+1)*idealTotient I := h
    _ = _ := by ring

theorem idealTotient_cube (I : Ideal O) (hI : I ≠ 0) :
    idealTotient (I ^3)=Ideal.absNorm I ^2*idealTotient I :=
  idealTotient_pow_succ I hI 2

theorem card_admissible_cube_product (n : ℕ) (a : O) (ha : a ≠ 0)
    (hcop : IsCoprime a (3:O)) :
    Nat.card (AdmissibleResidue (lambda^(3*n)*a^3)) =
      3^(3*n)*Ideal.absNorm (Ideal.span {a})^2*idealTotient (Ideal.span {a}) := by
  rw [card_admissible_lambda_pow_mul (3*n) (a^3) hcop.pow_left,
    ← Ideal.span_singleton_pow,idealTotient_cube _ (Ideal.span_singleton_eq_bot.not.mpr ha)]
  ring

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

lemma isUnit_quotient_iff_sup (I : Ideal O) (x : O) :
    IsUnit (Ideal.Quotient.mk I x) ↔ I ⊔ Ideal.span {x}=⊤ := by
  constructor
  · intro hx
    obtain ⟨b,hb⟩ := isUnit_iff_exists_inv.mp hx
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective b
    have hI : x*b-1 ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_sub,map_mul,map_one,sub_eq_zero] using hb
    apply (Ideal.eq_top_iff_one _).mpr
    have hx' : x*b ∈ I ⊔ Ideal.span {x} :=
      (le_sup_right : Ideal.span {x} ≤ I ⊔ Ideal.span {x})
        ((Ideal.span {x}).mul_mem_right b (Ideal.subset_span (by simp)))
    convert (preTransparency := .instances) (I ⊔ Ideal.span {x}).sub_mem hx' ((le_sup_left : I ≤ I ⊔ Ideal.span {x}) hI) using 1 ; ring
  · intro h
    have h1 : (1:O) ∈ I ⊔ Ideal.span {x} := by rw [h]; trivial
    obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp h1
    obtain ⟨k,rfl⟩ := Ideal.mem_span_singleton.mp hb
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk I k, ?_⟩
    have ha0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    have hh := congrArg (Ideal.Quotient.mk I) hab
    simpa only [map_add,map_mul,map_one,ha0,zero_add] using hh

lemma residue_unit_mobius (I : Ideal O) (hI : I ≠ 0) (r : O ⧸ I) :
    (if IsUnit r then (1:ℂ) else 0) =
      ∑ J ∈ idealDivisors I, if Quotient.out r ∈ J then (moebius J:ℂ) else 0 := by
  let G : Ideal O := I ⊔ Ideal.span {Quotient.out r}
  have hG : G ≠ 0 := by
    intro hG
    apply hI
    apply le_antisymm _ bot_le
    calc
      I ≤ G := le_sup_left
      _ = ⊥ := hG
  have hdiv : (idealDivisors I).filter (fun J => Quotient.out r ∈ J)=idealDivisors G := by
    ext J
    simp only [Finset.mem_filter,mem_idealDivisors hI,mem_idealDivisors hG,
      Ideal.dvd_iff_le,G,sup_le_iff,Ideal.span_le,Set.singleton_subset_iff,SetLike.mem_coe]
  rw [← Finset.sum_filter,hdiv,sum_moebius_divisors G hG]
  have hu : IsUnit r ↔ G=⊤ := by
    rw [← Ideal.Quotient.mk_out r]
    exact isUnit_quotient_iff_sup I (Quotient.out r)
  simp only [hu]

lemma sum_indicator_const {R : Type*} [Fintype R] (P : R → Prop) (z : ℂ) :
    (∑ r : R, if P r then z else 0)=(Nat.card {r : R // P r}:ℂ)*z := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_eq_fintype_card,Fintype.card_subtype]

lemma card_quotient_multiples (I J : Ideal O) (hI : I ≠ 0) (hIJ : I ≤ J) :
    (Nat.card {r : O ⧸ I // Quotient.out r ∈ J}:ℂ)=
      (Ideal.absNorm I:ℂ)/(Ideal.absNorm J:ℂ) := by
  let f : (O ⧸ I) →+* (O ⧸ J) := Ideal.Quotient.factor hIJ
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hIJ
  have hpred (r : O ⧸ I) : Quotient.out r ∈ J ↔ f r=0 := by
    have hfr : f r=Ideal.Quotient.mk J (Quotient.out r) := by
      calc
        f r = f (Ideal.Quotient.mk I (Quotient.out r)) :=
          congrArg f (Ideal.Quotient.mk_out r).symm
        _ = _ := Ideal.Quotient.factor_mk hIJ _
    rw [← Ideal.Quotient.eq_zero_iff_mem,hfr]
  let e : {r : O ⧸ I // Quotient.out r ∈ J} ≃ f.toAddMonoidHom.ker :=
    Equiv.subtypeEquivRight hpred
  have hcard := card_ring_eq_card_mul_kernel f hf
  have hJ : J ≠ 0 := fun h => hI (le_antisymm (h ▸ hIJ) bot_le)
  have hnJ : (Ideal.absNorm J:ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  rw [Nat.card_congr e]
  apply (eq_div_iff hnJ).mpr
  have hh : Nat.card f.toAddMonoidHom.ker * Ideal.absNorm J = Ideal.absNorm I :=
    (Nat.mul_comm _ _).trans hcard.symm
  exact_mod_cast hh

theorem idealTotient_moebius (I : Ideal O) (hI : I ≠ 0) :
    (idealTotient I:ℂ)=(Ideal.absNorm I:ℂ)*
      ∑ J ∈ idealDivisors I, (moebius J:ℂ)/(Ideal.absNorm J:ℂ) := by
  let : Finite (O ⧸ I) := I.finiteQuotientOfFreeOfNeBot hI
  let : Fintype (O ⧸ I) := Fintype.ofFinite _
  classical
  have hcount : (idealTotient I:ℂ)=∑ r : O ⧸ I,
      @ite ℂ (IsUnit r) (Classical.propDecidable _) 1 0 := by
    have h := sum_indicator_const (R := O ⧸ I) IsUnit (1:ℂ)
    rw [mul_one] at h
    calc
      _ = (Nat.card {r : O ⧸ I // IsUnit r}:ℂ) := by
        exact_mod_cast Nat.card_congr (unitsSubtypeEquiv (O ⧸ I))
      _ = _ := h.symm
  rw [hcount]
  have hs : (∑ r : O ⧸ I, @ite ℂ (IsUnit r) (Classical.propDecidable _) 1 0) =
      ∑ r : O ⧸ I, ∑ J ∈ idealDivisors I,
        if Quotient.out r ∈ J then (moebius J:ℂ) else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    exact residue_unit_mobius I hI r
  rw [hs]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [sum_indicator_const,card_quotient_multiples I J hI
    (Ideal.dvd_iff_le.mp ((mem_idealDivisors hI).mp hJ))]
  ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)

def unramifiedNormWeight (s : ℂ) : Ideal O →*₀ ℂ where
  toFun I := if primaryGenerator I=0 then 0 else (Ideal.absNorm I:ℂ)^(-s)
  map_zero' := by simp
  map_one' := by
    rw [primaryGenerator_one,if_neg one_ne_zero,map_one,Nat.cast_one,Complex.one_cpow]
  map_mul' I J := by
    by_cases hI : primaryGenerator I=0
    · simp [primaryGenerator_mul,hI]
    by_cases hJ : primaryGenerator J=0
    · simp [primaryGenerator_mul,hJ]
    simp only [primaryGenerator_mul,mul_eq_zero,hI,hJ,false_or,ite_false,map_mul,Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow _ _ _

lemma unramifiedNormWeight_of_good (s : ℂ) (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    unramifiedNormWeight s I=(Ideal.absNorm I:ℂ)^(-s) := if_neg hI

lemma unramifiedNormWeight_of_bad (s : ℂ) (I : Ideal O) (hI : primaryGenerator I=0) :
    unramifiedNormWeight s I=0 := if_pos hI

lemma primaryGenerator_injective_good :
    Function.Injective (fun I : GoodIdeal => primaryGenerator I.1) := by
  intro I J h
  dsimp only at h
  apply Subtype.ext
  rw [← (primaryGenerator_spec I.1 I.2).1,← (primaryGenerator_spec J.1 J.2).1,h]

lemma norm_unramifiedNormWeight (s : ℂ) (I : GoodIdeal) :
    ‖unramifiedNormWeight s I.1‖=‖eisEmbedding (primaryGenerator I.1)‖^(-2*s.re) := by
  rw [unramifiedNormWeight_of_good s I.1 I.2]
  have hnorm : ‖eisEmbedding (primaryGenerator I.1)‖^2=(Ideal.absNorm I.1:ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,(primaryGenerator_spec I.1 I.2).1]
  have hn : 0<‖eisEmbedding (primaryGenerator I.1)‖ :=
    norm_pos_iff.mpr (eisEmbedding_ne_zero I.2)
  have hcast : (Ideal.absNorm I.1:ℂ)=((‖eisEmbedding (primaryGenerator I.1)‖^2:ℝ):ℂ) := by
    exact_mod_cast hnorm.symm
  rw [hcast,Complex.norm_cpow_eq_rpow_re_of_pos (sq_pos_of_pos hn)]
  rw [← Real.rpow_natCast_mul hn.le 2]
  congr 1
  simp only [Complex.neg_re,Nat.cast_ofNat]
  ring

theorem unramifiedNormWeight_summable_norm (s : ℂ) (hs : 1<s.re) :
    Summable (fun I : Ideal O => ‖unramifiedNormWeight s I‖) := by
  have hlat := (summable_embedding_rpow (-2*s.re) (by linarith)).comp_injective
    primaryGenerator_injective_good
  have hsub : Summable (fun I : GoodIdeal => ‖unramifiedNormWeight s I.1‖) := by
    simpa only [Function.comp_def, norm_unramifiedNormWeight] using hlat
  have hind := (summable_subtype_iff_indicator (s := {I : Ideal O | primaryGenerator I ≠ 0})
    (f := fun I => ‖unramifiedNormWeight s I‖)).mp hsub
  apply hind.congr
  intro I
  by_cases hI : primaryGenerator I=0
  · simp [Set.indicator,hI,unramifiedNormWeight_of_bad s I hI]
  · simp [Set.indicator,hI]

lemma norm_ideal_moebius_le_one (I : Ideal O) : ‖(moebius I:ℂ)‖≤1 := by
  by_cases hI : Squarefree I
  · simp [hI.moebius_eq]
  · simp [moebius_of_not_squarefree hI]

lemma moebius_unramifiedNormWeight_summable_norm (s : ℂ) (hs : 1<s.re) :
    Summable (fun I : Ideal O => ‖(moebius I:ℂ)*unramifiedNormWeight s I‖) := by
  apply (unramifiedNormWeight_summable_norm s hs).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_ideal_moebius_le_one I)

def unramifiedIdealZeta (s : ℂ) : ℂ := ∑' I : Ideal O, unramifiedNormWeight s I

def unramifiedMobiusSeries (s : ℂ) : ℂ :=
  ∑' I : Ideal O, (moebius I:ℂ)*unramifiedNormWeight s I

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

theorem unramifiedMobiusSeries_mul_zeta (s : ℂ) (hs : 1<s.re) :
    unramifiedMobiusSeries s*unramifiedIdealZeta s=1 := by
  let F : Ideal O × Ideal O → ℂ := fun p =>
    (moebius p.1:ℂ)*unramifiedNormWeight s (p.1*p.2)
  have hprod := (moebius_unramifiedNormWeight_summable_norm s hs).mul_norm
    (unramifiedNormWeight_summable_norm s hs)
  have hF : Summable F := by
    apply hprod.of_norm.congr
    intro p
    dsimp only [F]
    rw [map_mul]
    ring
  have hfiber (B : Ideal O) : (∑' p : MulFiber B,F p.1)=if B=1 then 1 else 0 := by
    by_cases hB : B=0
    · subst B
      have hz (p : MulFiber 0) : F p.1=0 := by simp only [F,p.2,map_zero,mul_zero]
      simp only [hz,tsum_zero,zero_ne_one,ite_false]
    · calc
        _ = (∑' p : MulFiber B,(moebius p.1.1:ℂ))*unramifiedNormWeight s B := by
          rw [← tsum_mul_right]
          apply tsum_congr
          intro p
          simp only [F,p.2]
        _ = _ := by
          rw [mulFiber_moebius_sum B hB]
          split_ifs with hB1
          · subst B; simp only [map_one,mul_one]
          · simp only [zero_mul]
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B,F p.1) (∑' p,F p) at hsum
  simp_rw [hfiber] at hsum
  have hFone : (∑' p,F p)=1 := by simpa using hsum.tsum_eq.symm
  calc
    _ = ∑' p : Ideal O × Ideal O,
        ((moebius p.1:ℂ)*unramifiedNormWeight s p.1)*unramifiedNormWeight s p.2 :=
      tsum_mul_tsum_of_summable_norm (moebius_unramifiedNormWeight_summable_norm s hs)
        (unramifiedNormWeight_summable_norm s hs)
    _ = ∑' p,F p := by
      apply tsum_congr
      intro p
      simp only [F,map_mul]
      ring
    _ = 1 := hFone

theorem unramifiedIdealZeta_ne_zero (s : ℂ) (hs : 1<s.re) : unramifiedIdealZeta s ≠ 0 := by
  intro hz
  have h := unramifiedMobiusSeries_mul_zeta s hs
  rw [hz,mul_zero] at h
  exact zero_ne_one h

theorem unramifiedMobiusSeries_eq_inv (s : ℂ) (hs : 1<s.re) :
    unramifiedMobiusSeries s=(unramifiedIdealZeta s)⁻¹ := by
  have h := unramifiedMobiusSeries_mul_zeta s hs
  calc
    _ = (unramifiedMobiusSeries s*unramifiedIdealZeta s)*(unramifiedIdealZeta s)⁻¹ := by
      field_simp [unramifiedIdealZeta_ne_zero s hs]
    _ = _ := by rw [h,one_mul]

lemma unramifiedNormWeight_shift (s : ℂ) (I : Ideal O) :
    unramifiedNormWeight (s-1) I=(Ideal.absNorm I:ℂ)*unramifiedNormWeight s I := by
  by_cases hg : primaryGenerator I=0
  · rw [unramifiedNormWeight_of_bad _ I hg,unramifiedNormWeight_of_bad _ I hg,mul_zero]
  · rw [unramifiedNormWeight_of_good _ I hg,unramifiedNormWeight_of_good _ I hg]
    have hn : (Ideal.absNorm I:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (primaryGenerator_ne_zero_ideal I hg))
    rw [show -(s-1)=(1:ℂ)+(-s) by ring,Complex.cpow_add _ _ hn,Complex.cpow_one]

lemma mulFiber_totient_sum (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : MulFiber B,(moebius p.1.1:ℂ)*(Ideal.absNorm p.1.2:ℂ))=(idealTotient B:ℂ) := by
  let e := mulFiberDivisorEquiv B hB
  have hp (p : MulFiber B) :
      (moebius p.1.1:ℂ)*(Ideal.absNorm p.1.2:ℂ)=
        (Ideal.absNorm B:ℂ)*((moebius p.1.1:ℂ)/(Ideal.absNorm p.1.1:ℂ)) := by
    have hI : p.1.1 ≠ 0 := by
      intro hz
      have hh := p.2
      rw [hz,zero_mul] at hh
      exact hB hh.symm
    have hn : (Ideal.absNorm p.1.1:ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    have heq : (Ideal.absNorm B:ℂ)=(Ideal.absNorm p.1.1:ℂ)*(Ideal.absNorm p.1.2:ℂ) := by
      calc
        _ = (Ideal.absNorm (p.1.1*p.1.2):ℂ) := congrArg (fun I => (Ideal.absNorm I:ℂ)) p.2.symm
        _ = _ := by rw [map_mul,Nat.cast_mul]
    rw [heq]
    field_simp
  calc
    _ = ∑' p : MulFiber B,(Ideal.absNorm B:ℂ)*
        ((moebius p.1.1:ℂ)/(Ideal.absNorm p.1.1:ℂ)) := tsum_congr hp
    _ = (Ideal.absNorm B:ℂ)*
        ∑' D : {D : Ideal O // D ∈ idealDivisors B},
          ((moebius D.1:ℂ)/(Ideal.absNorm D.1:ℂ)) := by
      rw [← tsum_mul_left]
      exact e.tsum_eq (fun D => (Ideal.absNorm B:ℂ)*((moebius D.1:ℂ)/(Ideal.absNorm D.1:ℂ)))
    _ = (Ideal.absNorm B:ℂ)*
        ∑ D ∈ idealDivisors B,((moebius D:ℂ)/(Ideal.absNorm D:ℂ)) := by
      rw [tsum_fintype]
      apply congrArg (fun z : ℂ => (Ideal.absNorm B:ℂ)*z)
      exact (Finset.sum_subtype (idealDivisors B) (fun _ => Iff.rfl)
        (fun D => (moebius D:ℂ)/(Ideal.absNorm D:ℂ))).symm
    _ = _ := (idealTotient_moebius B hB).symm

def unramifiedTotientSeries (s : ℂ) : ℂ :=
  ∑' I : Ideal O,(idealTotient I:ℂ)*unramifiedNormWeight s I

theorem unramifiedTotientSeries_product (s : ℂ) (hs : 2<s.re) :
    unramifiedTotientSeries s=unramifiedMobiusSeries s*unramifiedIdealZeta (s-1) := by
  have hs1 : 1<s.re := by linarith
  have hs2 : 1<(s-1).re := by simp only [Complex.sub_re,Complex.one_re]; linarith
  let F : Ideal O × Ideal O → ℂ := fun p =>
    (moebius p.1:ℂ)*(Ideal.absNorm p.2:ℂ)*unramifiedNormWeight s (p.1*p.2)
  have hprod := (moebius_unramifiedNormWeight_summable_norm s hs1).mul_norm
    (unramifiedNormWeight_summable_norm (s-1) hs2)
  have heq (p : Ideal O × Ideal O) :
      ((moebius p.1:ℂ)*unramifiedNormWeight s p.1)*unramifiedNormWeight (s-1) p.2=F p := by
    simp only [F,unramifiedNormWeight_shift,map_mul]
    ring
  have hF : Summable F := hprod.of_norm.congr heq
  have hfiber (B : Ideal O) : (∑' p : MulFiber B,F p.1)=
      (idealTotient B:ℂ)*unramifiedNormWeight s B := by
    by_cases hB : B=0
    · subst B
      have hz (p : MulFiber 0) : F p.1=0 := by simp only [F,p.2,map_zero,mul_zero]
      simp only [hz,tsum_zero,map_zero,mul_zero]
    · calc
        _ = (∑' p : MulFiber B,(moebius p.1.1:ℂ)*(Ideal.absNorm p.1.2:ℂ))*
            unramifiedNormWeight s B := by
          rw [← tsum_mul_right]
          apply tsum_congr
          intro p
          simp only [F,p.2]
        _ = _ := by rw [mulFiber_totient_sum B hB]
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B,F p.1) (∑' p,F p) at hsum
  simp_rw [hfiber] at hsum
  calc
    _ = ∑' p,F p := hsum.tsum_eq
    _ = _ := by
      rw [unramifiedMobiusSeries,unramifiedIdealZeta,
        tsum_mul_tsum_of_summable_norm (moebius_unramifiedNormWeight_summable_norm s hs1)
          (unramifiedNormWeight_summable_norm (s-1) hs2)]
      exact tsum_congr (fun p => (heq p).symm)

theorem unramifiedTotientSeries_quotient (s : ℂ) (hs : 2<s.re) :
    unramifiedTotientSeries s=unramifiedIdealZeta (s-1)/unramifiedIdealZeta s := by
  rw [unramifiedTotientSeries_product s hs,unramifiedMobiusSeries_eq_inv s (by linarith),div_eq_mul_inv]
  ring

lemma idealTotient_le_absNorm (I : Ideal O) (hI : I ≠ 0) :
    idealTotient I ≤ Ideal.absNorm I := by
  let : Finite (O ⧸ I) := I.finiteQuotientOfFreeOfNeBot hI
  change Nat.card (O ⧸ I)ˣ ≤ Nat.card (O ⧸ I)
  exact Nat.card_le_card_of_injective (Units.val : (O ⧸ I)ˣ → O ⧸ I) Units.val_injective

theorem unramifiedTotientSeries_summable_norm (s : ℂ) (hs : 2<s.re) :
    Summable (fun I : Ideal O => ‖(idealTotient I:ℂ)*unramifiedNormWeight s I‖) := by
  have hs1 : 1<(s-1).re := by simp only [Complex.sub_re,Complex.one_re]; linarith
  apply (unramifiedNormWeight_summable_norm (s-1) hs1).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro I
  by_cases hI : I=0
  · subst I; simp only [map_zero,mul_zero,norm_zero,le_refl]
  · rw [norm_mul,Complex.norm_natCast,unramifiedNormWeight_shift,norm_mul,Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (idealTotient_le_absNorm I hI)) (norm_nonneg _)

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

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
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)

include hc

end SecondPassArithmetic

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm )
open ConcreteTraceCRT (eisEmbedding)

def secondFrequencyCutoff (scale H : ℝ) : Finset O :=
  ShortDraftLatticeCount.rowNormBall ⌈H/scale⌉₊

end
section

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def truncatedSecondZero (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (K : Finset ι → Finset ι → Finset O) : ℂ :=
  (Y : ℂ) * paperRadialFourier W 0 *
    ∑ G ∈ F.powerset,
      (‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2 : ℝ) * star (H G) * H G *
      ∑ E : G.powerset, if 0 ∈ K G E.val then
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E.val, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖ ^ 2 : ℝ)
        else 0

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (columnLog jLabel b0Label )
open JointLogSeparation (tripleCoefficient)

end SecondPassArithmetic

open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)

def ramifiedIdeal : Ideal O := Ideal.span {lambda}

lemma ramifiedIdeal_prime : Prime ramifiedIdeal := by
  exact Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr residue_lambda_prime.ne_zero)
    ((Ideal.span_singleton_prime residue_lambda_prime.ne_zero).mpr residue_lambda_prime)

lemma goodIdeal_iff_not_ramified (I : Ideal O) :
    primaryGenerator I ≠ 0 ↔ ¬ ramifiedIdeal ∣ I := by
  rw [← ConcretePrimeRowBridge.span_idealGenerator I,
    PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff,
    Ideal.dvd_iff_le,ramifiedIdeal,Ideal.span_singleton_le_span_singleton]

lemma ramifiedIdeal_absNorm : Ideal.absNorm ramifiedIdeal=3 := absNorm_span_lambda

lemma prime_power_remainder_multiplicity {R : Type*} [CommMonoidWithZero R]
    [IsCancelMulZero R] {p a : R} (hp : Prime p) (ha : ¬ p ∣ a) (n : ℕ) :
    multiplicity p (p^n*a)=n := by
  apply multiplicity_eq_of_dvd_of_not_dvd ⟨a,rfl⟩
  intro hd
  rw [pow_succ] at hd
  exact ha ((mul_dvd_mul_iff_left (pow_ne_zero n hp.ne_zero)).mp hd)

abbrev NonzeroIdeal := {I : Ideal O // I ≠ 0}

def lambdaFactorMap (p : ℕ × GoodIdeal) : NonzeroIdeal :=
  ⟨ramifiedIdeal^p.1*p.2.1,mul_ne_zero (pow_ne_zero _ ramifiedIdeal_prime.ne_zero)
    (primaryGenerator_ne_zero_ideal _ p.2.2)⟩

lemma lambdaFactorMap_bijective : Function.Bijective lambdaFactorMap := by
  constructor
  · rintro ⟨n,I⟩ ⟨m,J⟩ heq
    have hh : ramifiedIdeal^n*I.1=ramifiedIdeal^m*J.1 := congrArg Subtype.val heq
    have hn : n=m := by
      have hm := congrArg (multiplicity ramifiedIdeal) hh
      rw [prime_power_remainder_multiplicity ramifiedIdeal_prime
        ((goodIdeal_iff_not_ramified I.1).mp I.2),
        prime_power_remainder_multiplicity ramifiedIdeal_prime
        ((goodIdeal_iff_not_ramified J.1).mp J.2)] at hm
      exact hm
    subst m
    have hIJ : I=J := Subtype.ext (mul_left_cancel₀ (pow_ne_zero n ramifiedIdeal_prime.ne_zero) hh)
    subst J
    rfl
  · intro I
    obtain ⟨J,hJ,hnot⟩ := (FiniteMultiplicity.of_prime_left ramifiedIdeal_prime I.2).exists_eq_pow_mul_and_not_dvd
    refine ⟨(multiplicity ramifiedIdeal I.1,⟨J,(goodIdeal_iff_not_ramified J).mpr hnot⟩), ?_⟩
    exact Subtype.ext hJ.symm

def lambdaFactorEquiv : ℕ × GoodIdeal ≃ NonzeroIdeal :=
  Equiv.ofBijective lambdaFactorMap lambdaFactorMap_bijective

lemma ideal_pow_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (fun I : Ideal O => I ^n) := by
  intro I J h
  dsimp only at h
  apply le_antisymm
  · apply Ideal.dvd_iff_le.mp
    apply (pow_dvd_pow_iff_dvd hn).mp
    rw [h]
  · apply Ideal.dvd_iff_le.mp
    apply (pow_dvd_pow_iff_dvd hn).mp
    rw [h]

lemma lambdaFactor_generator_span (n : ℕ) (I : GoodIdeal) :
    Ideal.span {lambda^n*primaryGenerator I.1}=ramifiedIdeal^n*I.1 := by
  rw [← Ideal.span_singleton_mul_span_singleton,← Ideal.span_singleton_pow,
    (primaryGenerator_spec I.1 I.2).1]
  rfl

lemma three_dvd_lambda_sq : (3:O) ∣ lambda^2 := by
  have h := three_dvd_primary_sub_one (lambda^2+1) (show lambda^2 ∣ lambda^2+1-1 by simp)
  simpa only [add_sub_cancel_right] using h

lemma unit_cube_eq_sign (u : Oˣ) : (u:O)^3=1 ∨ (u:O)^3= -1 := by
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ ActualEisensteinCubic.K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η:O)=omega := rfl
  have hlist : u ∈ ([1,-1,η,-η,η^2,-η^2] : List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hlist
  rcases hlist with h | h | h | h | h | h
  · left; simp [h]
  · right; norm_num [h]
  · left; simpa only [h,hη] using omega_primitive.pow_eq_one
  · right
    rw [h,Units.val_neg,hη]
    have hh := omega_primitive.pow_eq_one
    linear_combination -hh
  · left
    rw [h,Units.val_pow_eq_pow_val,hη,show (omega^2)^3=(omega^3)^2 by ring,omega_primitive.pow_eq_one]
    simp
  · right
    rw [h,Units.val_neg,Units.val_pow_eq_pow_val,hη]
    simp only [neg_pow,show (-1:O)^3= -1 by norm_num,
      show (omega^2)^3=(omega^3)^2 by ring,omega_primitive.pow_eq_one,one_pow,mul_one]

def cubeSign : Bool → O
  | false => 1
  | true => -1

lemma cubeSign_isUnit (b : Bool) : IsUnit (cubeSign b) := by
  cases b <;> simp [cubeSign]

lemma cubeSign_cube (b : Bool) : (cubeSign b)^3=cubeSign b := by
  cases b <;> norm_num [cubeSign]

lemma cubeSign_injective : Function.Injective cubeSign := by
  intro a b h
  cases a <;> cases b <;> try rfl
  all_goals norm_num [cubeSign] at h

def cubeBase (n : ℕ) (I : GoodIdeal) : O := lambda^(n+1)*primaryGenerator I.1

def cubeColumn (b : Bool) (n : ℕ) (I : GoodIdeal) : O := cubeSign b*(cubeBase n I)^3

lemma cubeBase_ne_zero (n : ℕ) (I : GoodIdeal) : cubeBase n I ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ residue_lambda_prime.ne_zero) I.2

lemma cubeColumn_ne_zero (b : Bool) (n : ℕ) (I : GoodIdeal) : cubeColumn b n I ≠ 0 :=
  mul_ne_zero (cubeSign_isUnit b).ne_zero (pow_ne_zero 3 (cubeBase_ne_zero n I))

lemma cubeColumn_cube (b : Bool) (n : ℕ) (I : GoodIdeal) :
    cubeColumn b n I=(cubeSign b*cubeBase n I)^3 := by
  rw [mul_pow,cubeSign_cube]
  rfl

lemma cubeColumn_level (b : Bool) (n : ℕ) (I : GoodIdeal) : (3:O) ∣ cubeColumn b n I := by
  have h3 : (3:O) ∣ lambda^(3*(n+1)) := three_dvd_lambda_sq.trans (pow_dvd_pow lambda (by omega))
  have heq : cubeColumn b n I=cubeSign b*(lambda^(3*(n+1))*(primaryGenerator I.1)^3) := by
    simp only [cubeColumn,cubeBase,mul_pow,← pow_mul]
    congr 2
    ring
  rw [heq]
  exact (h3.mul_right _).mul_left _

lemma cubeColumn_span (b : Bool) (n : ℕ) (I : GoodIdeal) :
    Ideal.span {cubeColumn b n I}=(ramifiedIdeal^(n+1)*I.1)^3 := by
  rw [cubeColumn,Ideal.span_singleton_mul_left_unit (cubeSign_isUnit b),
    ← Ideal.span_singleton_pow]
  change (Ideal.span {lambda^(n+1)*primaryGenerator I.1})^3=_
  rw [lambdaFactor_generator_span]

abbrev CubeLower := {c : LevelLower // c.1 ≠ 0 ∧ ∃ a : O,c.1=a^3}

def cubeColumnMap (p : Bool × ℕ × GoodIdeal) : CubeLower :=
  ⟨⟨cubeColumn p.1 p.2.1 p.2.2,cubeColumn_level p.1 p.2.1 p.2.2⟩,
    cubeColumn_ne_zero p.1 p.2.1 p.2.2,⟨cubeSign p.1*cubeBase p.2.1 p.2.2,
      cubeColumn_cube p.1 p.2.1 p.2.2⟩⟩

lemma cubeColumnMap_injective : Function.Injective cubeColumnMap := by
  rintro ⟨b,n,I⟩ ⟨d,m,J⟩ h
  have hc : cubeColumn b n I=cubeColumn d m J := congrArg (fun c : CubeLower => c.1.1) h
  have hs := congrArg (fun a : O => Ideal.span {a}) hc
  rw [cubeColumn_span,cubeColumn_span] at hs
  have hr := ideal_pow_injective (by decide : (3:ℕ) ≠ 0) hs
  have hp : lambdaFactorMap (n+1,I)=lambdaFactorMap (m+1,J) := Subtype.ext hr
  have he := lambdaFactorMap_bijective.1 hp
  have hnm : n=m := Nat.succ.inj (congrArg Prod.fst he)
  have hIJ : I=J := congrArg Prod.snd he
  subst m; subst J
  have hbd : b=d := cubeSign_injective (mul_right_cancel₀
    (pow_ne_zero 3 (cubeBase_ne_zero n I)) hc)
  subst d
  rfl

lemma cubeColumnMap_surjective : Function.Surjective cubeColumnMap := by
  intro c
  obtain ⟨a,ha⟩ := c.2.2
  have ha0 : a ≠ 0 := by intro h; rw [h,zero_pow (by decide)] at ha; exact c.2.1 ha
  let A : NonzeroIdeal := ⟨Ideal.span {a},Ideal.span_singleton_eq_bot.not.mpr ha0⟩
  obtain ⟨⟨k,I⟩,hAI⟩ := lambdaFactorMap_bijective.2 A
  have hfact : ramifiedIdeal^k*I.1=Ideal.span {a} := congrArg Subtype.val hAI
  have hla : lambda ∣ a := by
    apply residue_lambda_prime.dvd_of_dvd_pow
    have hlam3 : lambda ∣ (3:O) :=
      (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans lambda_sq_dvd_three
    rw [← ha]
    exact hlam3.trans c.1.2
  have hk : k ≠ 0 := by
    intro hk
    have hIeq : I.1=Ideal.span {a} := by simpa only [hk,pow_zero,one_mul] using hfact
    apply (goodIdeal_iff_not_ramified I.1).mp I.2
    rw [hIeq,Ideal.dvd_iff_le,ramifiedIdeal,Ideal.span_singleton_le_span_singleton]
    exact hla
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hspan : Ideal.span {cubeBase n I}=Ideal.span {a} :=
    (lambdaFactor_generator_span (n+1) I).trans hfact
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  rcases unit_cube_eq_sign u with hu1 | hum1
  · refine ⟨(false,n,I),Subtype.ext (Subtype.ext ?_)⟩
    change cubeColumn false n I=c.1.1
    rw [ha,← hu,mul_pow,hu1,mul_one]
    simp only [cubeColumn,cubeSign,one_mul]
  · refine ⟨(true,n,I),Subtype.ext (Subtype.ext ?_)⟩
    change cubeColumn true n I=c.1.1
    rw [ha,← hu,mul_pow,hum1]
    simp only [cubeColumn,cubeSign]
    ring

def cubeColumnEquiv : Bool × ℕ × GoodIdeal ≃ CubeLower :=
  Equiv.ofBijective cubeColumnMap ⟨cubeColumnMap_injective,cubeColumnMap_surjective⟩

lemma cubeColumn_expanded (b : Bool) (n : ℕ) (I : GoodIdeal) :
    cubeColumn b n I=lambda^(3*(n+1))*(cubeSign b*primaryGenerator I.1)^3 := by
  simp only [cubeColumn,cubeBase,mul_pow,cubeSign_cube,← pow_mul]
  rw [Nat.mul_comm (n+1) 3]
  ring

lemma cubeColumn_arithmetic_sum (b : Bool) (n : ℕ) (I : GoodIdeal) :
    arithmeticResidueSum 0 (cubeColumn b n I)=
      (3^(3*(n+1))*Ideal.absNorm I.1^2*idealTotient I.1:ℕ) := by
  have ha : cubeSign b*cubeBase n I ≠ 0 :=
    mul_ne_zero (cubeSign_isUnit b).ne_zero (cubeBase_ne_zero n I)
  have hA := arithmeticResidueSum_cube _ ha
  rw [← cubeColumn_cube] at hA
  rw [hA,cubeColumn_expanded]
  have hc : IsCoprime (cubeSign b*primaryGenerator I.1) (3:O) :=
    (isCoprime_mul_unit_left_left (cubeSign_isUnit b) _ _).mpr
      (primary_coprime_three _ (primaryGenerator_spec I.1 I.2).2)
  have hs : Ideal.span {cubeSign b*primaryGenerator I.1}=I.1 := by
    rw [Ideal.span_singleton_mul_left_unit (cubeSign_isUnit b),(primaryGenerator_spec I.1 I.2).1]
  rw [card_admissible_cube_product (n+1) _ (mul_ne_zero (cubeSign_isUnit b).ne_zero I.2) hc,hs]

lemma cubeColumn_norm (b : Bool) (n : ℕ) (I : GoodIdeal) :
    Ideal.absNorm (Ideal.span {cubeColumn b n I})=3^(3*(n+1))*Ideal.absNorm I.1^3 := by
  rw [cubeColumn_span,map_pow,map_mul,map_pow,ramifiedIdeal_absNorm,mul_pow,← pow_mul]
  rw [Nat.mul_comm (n+1) 3]

def ramifiedRatio (s : ℂ) : ℂ := (3:ℂ)^(3-3*s)

lemma cube_norm_weight_algebra (s : ℂ) (n N : ℕ) (hN : N ≠ 0) :
    ((3^(3*(n+1))*N^3:ℕ):ℂ)^(-s) * (3^(3*(n+1))*N^2:ℕ) =
      ramifiedRatio s^(n+1) * (N:ℂ)^(-(3*s-2)) := by
  have hNc : (N:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have hsplit : ((3:ℂ)^(3*(n+1):ℕ)*(N:ℂ)^3)^(-s)=
      (3:ℂ)^((3*(n+1):ℕ)*(-s))*(N:ℂ)^(3*(-s)) := by
    have hm := Complex.natCast_mul_natCast_cpow (3^(3*(n+1))) (N^3) (-s)
    simp only [Nat.cast_pow,Nat.cast_ofNat] at hm
    rw [hm]
    have h3 : ((3:ℂ)^(3*(n+1):ℕ))^(-s)=(3:ℂ)^((3*(n+1):ℕ)*(-s)) := by
      simpa only [Nat.cast_ofNat] using
        (Complex.natCast_cpow_natCast_mul 3 (3*(n+1)) (-s)).symm
    have hN' : ((N:ℂ)^3)^(-s)=(N:ℂ)^(3*(-s)) := by
      simpa only [Nat.cast_ofNat] using (Complex.natCast_cpow_natCast_mul N 3 (-s)).symm
    rw [h3,hN']
  rw [hsplit]
  have hpoly : (3:ℂ)^(3*(n+1):ℕ)*(N:ℂ)^2 =
      (3:ℂ)^((3*(n+1):ℕ):ℂ)*(N:ℂ)^(2:ℂ) := by
    norm_num only [Complex.cpow_natCast,Complex.cpow_ofNat]
  rw [hpoly]
  calc
    _ = ((3:ℂ)^((3*(n+1):ℕ)*(-s))*(3:ℂ)^((3*(n+1):ℕ):ℂ))*
        ((N:ℂ)^(3*(-s))*(N:ℂ)^(2:ℂ)) := by ring
    _ = (3:ℂ)^((3*(n+1):ℕ)*(-s)+(3*(n+1):ℕ)) * (N:ℂ)^(3*(-s)+2) := by
      rw [← Complex.cpow_add _ _ (by norm_num : (3:ℂ) ≠ 0),← Complex.cpow_add _ _ hNc]
    _ = ramifiedRatio s^(n+1) * (N:ℂ)^(-(3*s-2)) := by
      unfold ramifiedRatio
      rw [← Complex.cpow_mul_nat]
      congr 1 <;> congr 1 <;> push_cast <;> ring

lemma cubeColumn_dirichletTerm (s : ℂ) (b : Bool) (n : ℕ) (I : GoodIdeal) :
    arithmeticDirichletTerm s 0 (cubeColumnMap (b,n,I)).1 =
      ramifiedRatio s^(n+1) * ((idealTotient I.1:ℂ)*unramifiedNormWeight (3*s-2) I.1) := by
  have hI : Ideal.absNorm I.1 ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr (primaryGenerator_ne_zero_ideal I.1 I.2)
  change (if cubeColumn b n I=0 then 0 else
    ((‖eisEmbedding (cubeColumn b n I)‖^2:ℝ):ℂ)^(-s)*
      arithmeticResidueSum 0 (cubeColumn b n I)) = _
  rw [if_neg (cubeColumn_ne_zero b n I),eisEmbedding_norm_sq_eq_absNorm_span,
    Complex.ofReal_natCast,cubeColumn_norm,cubeColumn_arithmetic_sum,
    unramifiedNormWeight_of_good _ _ I.2]
  calc
    _ = (((3^(3*(n+1))*Ideal.absNorm I.1^3:ℕ):ℂ)^(-s) *
        (3^(3*(n+1))*Ideal.absNorm I.1^2:ℕ))*(idealTotient I.1:ℂ) := by
      push_cast
      ring
    _ = (ramifiedRatio s^(n+1)*(Ideal.absNorm I.1:ℂ)^(-(3*s-2)))*(idealTotient I.1:ℂ) := by
      rw [cube_norm_weight_algebra s n (Ideal.absNorm I.1) hI]
    _ = _ := by ring

end CubicEisenstein

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex TruncatedPrincipalPoisson

def squarefreeIdealRange (K : ℝ) : Finset (Ideal O) := (idealsUpTo ⌊K⌋₊).filter Squarefree

end CanonicalQuadraticSieve

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def secondDiagonalMass (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) : ℝ :=
  ∑ G ∈ F.powerset, ‖secondInputCoefficient p hg Ψ m c d H G‖ ^ 2 *
    ∏ i ∈ G, (1 - (1 : ℝ) / Ideal.absNorm (Ideal.span {p i}))

end
section

open ActualEisensteinCubic

def secondDyadicSector {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (F : Finset ι) (K : Finset ι → Finset ι → Finset O) (R : Finset ι)
    (label : Finset ι → SecondExpansionData ι → κ) (j : κ) : Finset (SecondExpansionData ι) :=
  (secondExpansionSector F (fun G E => (K G E).erase 0) R).filter (fun x => label R x = j)

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype κ]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

end

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory
open ActualEisensteinCubic
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

section
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum

theorem ideals_coprime_of_relprime (A B : Ideal O) (h : IsRelPrime A B) : IsCoprime A B := by
  apply Ideal.isCoprime_iff_gcd.mpr
  simpa only [Ideal.one_eq_top] using Ideal.isUnit_iff.mp (h (GCDMonoid.gcd_dvd_left A B) (GCDMonoid.gcd_dvd_right A B))

theorem squarefree_quotient_gcd_coprime (B G : Ideal O) (hB : Squarefree B) :
    IsCoprime (idealQuotient (gcd B G) B) G := by
  let D := gcd B G
  have hDB : D ∣ B := GCDMonoid.gcd_dvd_left B G
  have hDG : D ∣ G := GCDMonoid.gcd_dvd_right B G
  have hD : D ≠ 0 := ne_zero_of_dvd_ne_zero hB.ne_zero hDB
  have hc : IsCoprime (idealQuotient D B) (idealQuotient D G) :=
    (gcd_eq_iff_quotient_coprime D B G hD hDB hDG).mp rfl
  have hmul : Squarefree (D * idealQuotient D B) := by rw [idealQuotient_mul hDB]; exact hB
  have hdq : IsCoprime D (idealQuotient D B) :=
    ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp hmul).1
  have hh := hdq.symm.mul_right hc
  rw [idealQuotient_mul hDG] at hh
  exact hh

theorem gcd_mul_of_coprime_divisor (D H G : Ideal O) (hDG : D ∣ G) (hHG : IsCoprime H G) :
    gcd (D * H) G = D := by
  have hleft : D ∣ gcd (D * H) G := GCDMonoid.dvd_gcd (dvd_mul_right D H) hDG
  have hcop : IsCoprime (gcd (D * H) G) H :=
    (hHG.mono (dvd_refl H) (GCDMonoid.gcd_dvd_right (D * H) G)).symm
  have hright : gcd (D * H) G ∣ D := hcop.dvd_of_dvd_mul_right (GCDMonoid.gcd_dvd_left _ _)
  exact associated_iff_eq.mp (associated_of_dvd_dvd hright hleft)

def squarefreeGcdEquiv (G : Ideal O) (hG : Squarefree G) :
    {B : Ideal O // Squarefree B} ≃
      (idealDivisors G) × {H : Ideal O // Squarefree H ∧ IsCoprime H G} where
  toFun B := (⟨gcd B.val G, (mem_idealDivisors hG.ne_zero).mpr (GCDMonoid.gcd_dvd_right _ _)⟩,
    ⟨idealQuotient (gcd B.val G) B.val,
      B.property.squarefree_of_dvd (idealQuotient_dvd (GCDMonoid.gcd_dvd_left _ _)),
      squarefree_quotient_gcd_coprime B.val G B.property⟩)
  invFun p := ⟨p.1.val * p.2.val, squarefree_mul_iff.mpr
    ⟨(p.2.property.2.mono (dvd_refl _) ((mem_idealDivisors hG.ne_zero).mp p.1.property)).symm.isRelPrime,
      hG.squarefree_of_dvd ((mem_idealDivisors hG.ne_zero).mp p.1.property), p.2.property.1⟩⟩
  left_inv B := Subtype.ext (idealQuotient_mul (GCDMonoid.gcd_dvd_left B.val G))
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact gcd_mul_of_coprime_divisor p.1.val p.2.val G
        ((mem_idealDivisors hG.ne_zero).mp p.1.property) p.2.property.2
    · apply Subtype.ext
      change idealQuotient (gcd (p.1.val * p.2.val) G) (p.1.val * p.2.val) = p.2.val
      rw [gcd_mul_of_coprime_divisor p.1.val p.2.val G
        ((mem_idealDivisors hG.ne_zero).mp p.1.property) p.2.property.2]
      have hD : p.1.val ≠ 0 := ne_zero_of_dvd_ne_zero hG.ne_zero
        ((mem_idealDivisors hG.ne_zero).mp p.1.property)
      exact mul_left_cancel₀ hD (idealQuotient_mul (dvd_mul_right p.1.val p.2.val))

def coprimeSquarefreeRange (G : Ideal O) (K : ℝ) : Finset (Ideal O) :=
  (squarefreeIdealRange K).filter (fun H => IsCoprime H G)

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open IdealMobiusDivisorSum

theorem canonical_quadraticRow_one (I : Ideal O) (hI : Admissible I) : quadraticRow I 1 = 1 := by
  rw [quadraticRow, dif_pos hI]
  simp [idealSexticRow, finiteSquarefreeRow]

theorem unrestrictedPairCharacter_one (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) : unrestrictedPairCharacter I J 1 = 1 := by
  have h := unrestrictedPairCharacter_span I J hI hJ hray 1
  simpa only [Ideal.span_singleton_one, canonical_quadraticRow_one I hI,
    canonical_quadraticRow_one J hJ, one_mul, Ideal.one_eq_top] using h

def normalizedIdealPair (I J lengthScale : Ideal O) : ℂ :=
  unrestrictedPairCharacter I J lengthScale / (Real.sqrt (Ideal.absNorm lengthScale : ℝ) : ℂ)

theorem normalizedIdealPair_mul (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (A B : Ideal O) :
    normalizedIdealPair I J (A * B) = normalizedIdealPair I J A * normalizedIdealPair I J B := by
  simp only [normalizedIdealPair, unrestrictedPairCharacter_mul I J hI hJ hray,
    map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul, div_mul_div_comm]

def normalizedIdealPairHom (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) : Ideal O →* ℂ where
  toFun := normalizedIdealPair I J
  map_one' := by
    rw [normalizedIdealPair, unrestrictedPairCharacter_one I J hI hJ hray, map_one]
    norm_num
  map_mul' := normalizedIdealPair_mul I J hI hJ hray

end
section

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open IdealMobiusDivisorSum QuadraticMainBoundary

def idealNormCutoff (K : ℝ) (H : Ideal O) : ℂ := if (Ideal.absNorm H : ℝ) ≤ K then 1 else 0

def normalizedPairPartial (I J : Ideal O) (K : ℝ) : ℂ :=
  ∑ B : squarefreeIdealRange K, normalizedIdealPair I J B.val

def normalizedPairCoprimePartial (I J G : Ideal O) (K : ℝ) : ℂ :=
  ∑ H : coprimeSquarefreeRange G K, normalizedIdealPair I J H.val

def normalizedPairDivisors (I J G : Ideal O) : ℂ :=
  ∑ E ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius E : ℂ) * normalizedIdealPair I J E

def normalizedPairDensity (I J G : Ideal O) : ℂ :=
  ∏ P ∈ IdealMobiusDivisorSum.primeSupport G,
    (1 - (idealZeroMask I (ConcretePrimeRowBridge.idealGenerator P) *
      idealZeroMask J (ConcretePrimeRowBridge.idealGenerator P)) / (Ideal.absNorm P : ℂ))

end

open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss IdealMobiusDivisorSum

def commonMaskIdeal (D : Ideal O) : Ideal O := ∏ P ∈ gcdMaskPrimes D, P

theorem admissible_of_squarefree_coprime_bad
    (H G : Ideal O) (hH : Squarefree H) (hc : IsCoprime H G)
    (hbad : ∀ P ∈ fixedBadPrimes, P ∣ G) : Admissible H := by
  refine ⟨hH.ne_zero, hH, ?_⟩
  intro P hP
  have hp : Prime P := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  apply (prime_good_iff_not_bad P).mpr
  intro hb
  exact hp.not_isUnit (hc.isRelPrime (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP) (hbad P hb))

end CanonicalQuadraticSieve

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def largePrincipalWindow (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) : ℝ := by
  classical
  exact ∑ D ∈ S, ∑ E ∈ T, ∑ i, if P (D*E) i then
    (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D : ℝ)*(Ideal.absNorm E : ℝ))) *
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k‖ else 0

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def principalDivisorCorrection (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    ∑ d ∈ idealDivisors (left j*right k), if P d i then
      (UniqueFactorizationMonoid.moebius d : ℂ) *
        ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0

def largePrincipalProductAt (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) : ℝ := by
  classical
  exact ∑ i, ∑ d ∈ K, if P d i then
    ‖∑ j, ∑ k, if d ∣ left j*right k then originalTerm rows left right a b 1 1 i j k *
      ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0‖ else 0

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct aLabel b0Label jLabel cubeActiveSupport primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

@[ext] structure CubeCoordinates (ι : Type*) where
  leftExponent : ι →₀ ℕ
  rightExponent : ι →₀ ℕ
  leftDivisor : Finset ι
  rightDivisor : Finset ι

namespace CubeCoordinates
variable {ι : Type*} [DecidableEq ι]

def support (x : CubeCoordinates ι) : Finset ι :=
  x.leftExponent.support ∪ x.rightExponent.support

def leftBit (x : CubeCoordinates ι) (i : ι) : Bool := decide (i ∈ x.leftDivisor)
def rightBit (x : CubeCoordinates ι) (i : ι) : Bool := decide (i ∈ x.rightDivisor)

def Admissible (x : CubeCoordinates ι) : Prop :=
  x.leftDivisor ⊆ x.support ∧ x.rightDivisor ⊆ x.support

end CubeCoordinates

@[ext] structure GlobalSecondData (ι : Type*) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  common : Finset ι
  firstDivisor : Finset ι
  source : SecondExpansionData ι

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct aLabel)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

end SecondPassArithmetic

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal

lemma cusp_height_volume (a : ℝ) (ha : 0<a) :
    (∫⁻v in Set.Ioi a,ENNReal.ofReal ((v^3)⁻¹))=ENNReal.ofReal (1/(2*a^2)) := by
  have hi : IntegrableOn (fun v : ℝ => (v^3)⁻¹) (Set.Ioi a) volume := by
    simpa only [show (-3:ℝ)=-(3:ℕ) by norm_num,Real.rpow_neg_natCast,zpow_neg,
      zpow_natCast] using (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) ha)
  have hn : 0≤ᵐ[volume.restrict (Set.Ioi a)] (fun v : ℝ => (v^3)⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact inv_nonneg.mpr (pow_nonneg (ha.trans hv).le 3)
  rw [←ofReal_integral_eq_lintegral_ofReal hi hn]
  congr 1
  have he := integral_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) ha
  norm_num only at he
  simp only [show (-3:ℝ)=-(3:ℕ) by norm_num,Real.rpow_neg_natCast,zpow_neg,
    zpow_natCast] at he
  rw [he]
  norm_num [show (-3:ℝ)+1=-2 by norm_num]
  ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ENNReal ContDiff

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport UnrestrictedIdealReindex IdealMobiusDivisorSum

def maskedPairIdealDualKernel (G I J : Ideal O) (W : ℝ → ℂ) (M : ℝ) : ℂ :=
  ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ))*
    ∑ q ∈ idealDivisors G,
      ((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
      ∑' B : NonzeroIdeal, unrestrictedPairCharacter I J B.val*paperRadialFourier W
        ((M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*(Ideal.absNorm B.val:ℝ))

end CanonicalQuadraticSieve

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum CompletedGauss
open QuadraticSquarefreeKernel

def liftingPrimeElement : O := ActualEisensteinCoordinates.eval 1 3
def liftingPrime : Ideal O := Ideal.span {liftingPrimeElement}

theorem liftingPrimeElement_norm : ShortDraftLatticeCount.qNat liftingPrimeElement=7 := by
  unfold ShortDraftLatticeCount.qNat liftingPrimeElement
  rw [ShortDraftLatticeCount.coords_eval]
  norm_num [ShortDraftLatticeCount.q]

theorem liftingPrime_norm : Ideal.absNorm liftingPrime=7 := by
  rw [liftingPrime,←qNat_eq_absNorm_span,liftingPrimeElement_norm]

theorem liftingPrime_prime : Prime liftingPrime := by
  apply Ideal.prime_of_isPrime
  · intro h
    have hh := Ideal.absNorm_eq_zero_iff.mpr h
    rw [liftingPrime_norm] at hh
    norm_num at hh
  · exact Ideal.isPrime_of_irreducible_absNorm (by
      rw [liftingPrime_norm,Nat.irreducible_iff_nat_prime]
      exact (by decide : Nat.Prime 7))

theorem supported_pow {I : Ideal O} (hI : Supported I) (k : ℕ) : Supported (I ^k) := by
  induction k with
  | zero =>
    simp only [pow_zero]
    refine ⟨one_ne_zero,?_⟩
    intro P hP
    change P∈UniqueFactorizationMonoid.normalizedFactors (1:Ideal O) at hP
    rw [UniqueFactorizationMonoid.normalizedFactors_one] at hP
    exact (Multiset.notMem_zero P hP).elim
  | succ k hk =>
    rw [pow_succ]
    exact (supported_mul_iff _ _).mpr ⟨hk,hI⟩

theorem exists_lifting_exponent (M : ℝ) (I : Ideal O) (hI : I≠0)
    (hIM : (Ideal.absNorm I:ℝ)≤M) :
    ∃k : ℕ, M<(49:ℝ)^k*(Ideal.absNorm I:ℝ) ∧
      (49:ℝ)^k*(Ideal.absNorm I:ℝ)≤49*M := by
  have hN : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near ((le_div_iff₀ hN).mpr (by simpa using hIM))
    (by norm_num : (1:ℝ)<49)
  refine ⟨k+1,?_,?_⟩
  · exact (div_lt_iff₀ hN).mp hhi
  · have h := (le_div_iff₀ hN).mp hlo
    rw [pow_succ]
    nlinarith

def liftingExponent (M : ℝ) (I : Ideal O) (hI : I≠0) (hIM : (Ideal.absNorm I:ℝ)≤M) : ℕ :=
  (exists_lifting_exponent M I hI hIM).choose

def liftedRow (M : ℝ) (I : Ideal O) (hI : I≠0) (hIM : (Ideal.absNorm I:ℝ)≤M) : Ideal O :=
  (liftingPrime^liftingExponent M I hI hIM)^2*I

end CanonicalQuadraticSieve

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical

section
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss QuadraticSquarefreeKernel

def squarefreeHighRange (M K : ℝ) : Finset (Ideal O) :=
  (idealRange M).filter (fun I => K<(Ideal.absNorm I:ℝ))

def annularLift (M K : ℝ) (I : squarefreeHighRange M K) : Ideal O :=
  liftedRow M I.val (mem_idealRange.mp (Finset.mem_filter.mp I.property).1).1.1
    (mem_idealRange.mp (Finset.mem_filter.mp I.property).1).2

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
open FiniteSieveRestriction

def liftingDivisibleColumns (N : ℝ) : Finset (idealRange N) :=
  Finset.univ.filter (fun J => liftingPrime∣J.val)

def liftingQuotientColumn (N : ℝ) (J : liftingDivisibleColumns N) : idealRange N :=
  ⟨idealQuotient liftingPrime J.val.val, by
    have hd := (Finset.mem_filter.mp J.property).2
    have hj := mem_idealRange.mp J.val.property
    refine mem_idealRange.mpr ⟨admissible_idealQuotient hj.1 hd,?_⟩
    have hn := idealQuotient_norm_le liftingPrime_prime.ne_zero hd N hj.2
    rw [liftingPrime_norm] at hn
    have hN : 0≤N := (Nat.cast_nonneg _).trans hj.2
    exact hn.trans (by norm_num; linarith)⟩

def liftingFreeCoefficient (N : ℝ) (a : idealRange N → ℂ) : idealRange N → ℂ :=
  fun J => if liftingPrime∣J.val then 0 else a J

def liftingDividedCoefficient (N : ℝ) (a : idealRange N → ℂ) : idealRange N → ℂ :=
  extendByZero Finset.univ (liftingQuotientColumn N) (fun J : liftingDivisibleColumns N => a J.val)

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss FiniteSieveOperator

def ballQuadraticEnergy (M N : ℝ) (a : idealRange N → ℂ) : ℝ :=
  ∑I : idealRange M, ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2

end

open ActualEisensteinCubic CompletedGauss

end

section

def cutoffRescaleCoefficient (C η r q : ℝ) : ℝ := C*r*q^2/(r/q)^η

end

open scoped BigOperators Classical

def largeGcdThreshold (α N : ℝ) : ℝ := N^(1-1/α)

end CanonicalQuadraticSieve

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace SecondPassArithmetic

section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm columnLog )
open RayFourExpansion (RayCharacter crossCoeff)

@[ext] structure GlobalCubeBlock (ι : Type*) where
  cube : CubeCoordinates ι
  common : Finset ι
  firstDivisor : Finset ι

variable {ι : Type*} [DecidableEq ι]

variable (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open FirstCauchyArithmetic (supportMobius supportConjugateSum)
open ConcreteTraceCRT (eisEmbedding)

def conjugateMonoid (Ψ : O→*ℂ) : O→*ℂ where
  toFun x := star (Ψ x)
  map_one' := by simp
  map_mul' x y := by simp [map_mul]

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})

variable (hp : ∀i,p i≠0) (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
include hc

end InitialMeanSquare

open scoped BigOperators Classical
namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticSquarefreeKernel UniqueFactorizationMonoid

def PowerfulIdeal (I : Ideal O) : Prop :=
  I≠0 ∧ ∀P∈normalizedFactors I, 2≤(normalizedFactors I).count P

theorem powerful_squarefree_dvd_squarePart (I : Ideal O) (hI : PowerfulIdeal I) :
    squarefreePart I ∣ squarePart I := by
  have ha := squarePart_ne_zero hI.1
  have hb := (squarefree_squarefreePart I).ne_zero
  apply (dvd_iff_normalizedFactors_le_normalizedFactors hb ha).mpr
  apply Multiset.le_iff_count.mpr
  intro P
  have he := congrArg normalizedFactors (squarePart_sq_mul_squarefreePart I)
  rw [normalizedFactors_mul (pow_ne_zero _ ha) hb,normalizedFactors_pow] at he
  have hc := congrArg (Multiset.count P) he
  simp only [Multiset.count_add,Multiset.count_nsmul] at hc
  have hsf := Multiset.nodup_iff_count_le_one.mp
    ((squarefree_iff_nodup_normalizedFactors hb).mp (squarefree_squarefreePart I)) P
  by_cases hzero : (normalizedFactors (squarefreePart I)).count P=0
  · omega
  · have hm : P∈normalizedFactors I := Multiset.count_pos.mp (by omega)
    have hp := hI.2 P hm
    omega

theorem powerful_exists_square_cube (I : Ideal O) (hI : PowerfulIdeal I) :
    ∃A : Ideal O, A≠0 ∧ A^2*squarefreePart I ^3=I := by
  obtain ⟨A,hA⟩ := powerful_squarefree_dvd_squarePart I hI
  have ha : A≠0 := by
    intro hz
    have h := squarePart_ne_zero hI.1
    apply h
    rw [hA,hz,mul_zero]
  refine ⟨A,ha,?_⟩
  calc
    _ = (squarefreePart I*A)^2*squarefreePart I := by ring
    _ = squarePart I ^2*squarefreePart I := by rw [←hA]
    _ = I := squarePart_sq_mul_squarefreePart I

def powerfulBase (I : Ideal O) : Ideal O :=
  if hI : PowerfulIdeal I then (powerful_exists_square_cube I hI).choose else 0

end

open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticSquarefreeKernel

end CompletedGauss

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open FirstPassCubeLabels (primeProductNorm columnLog)

def outsideSquarefreeIdeals (S : Finset (Ideal O)) (D : ℕ) : Finset (Ideal O) :=
  (outsideIdealsUpTo S D).filter Squarefree

theorem outsideSquarefree_admissible (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) : ∀ I ∈ outsideSquarefreeIdeals S D, Admissible I := by
  intro I hI
  obtain ⟨ho,hs⟩ := Finset.mem_filter.mp hI
  have hn := outsideIdealsUpTo_ne_bot S D I ho
  refine ⟨hn,hs,?_⟩
  intro P hP
  obtain ⟨hp,hd⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  apply (prime_good_iff_not_bad P).mpr
  intro hPb
  exact (mem_outsideIdealsUpTo.mp ho).2.2 P (hbad hPb) hd

end InitialMeanSquare

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient)
open FirstPassCubeLabels

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda∉Ideal.span {p i})

def canonicalSourceCoefficient (Ψ : O→*ℂ) (m f : O)
    (H : Finset ι→ℂ) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S * Ψ (∏i∈S,p i) *
    rowCoprimeMask (fun i => Ideal.span {p i}) S m *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S f^4 * H S

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open MixedCrossSeparation (columnCoefficient columnPrimeCoprime)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def canonicalPairMode (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (d h : O) : ℂ :=
  (V₁ (columnLog p X₁ N)*V₂ (columnLog p X₂ P))*
    ((K:ℂ)/(‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖:ℂ))*
    paperRadialFourier W (K*‖eisEmbedding h‖^2/
      (‖eisEmbedding d‖^2*primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h

def disjointCanonicalSource (F M B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ) (X₁ X₂ K : ℝ) : ℂ :=
  ∑N∈F.powerset,∑P∈F.powerset,if Disjoint N P then
    (V₁ (columnLog p X₁ N)*V₂ (columnLog p X₂ P))*
      (star (columnCoefficient p hp hcop hg N*C₁ N)*(columnCoefficient p hp hcop hg P*C₂ P))*
      (∑'z:O,rowCoprimeMask (fun i=>Ideal.span {p i}) M z*
        blockRow p hg ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)
          (threeBlockExponent N P v ε₁ ε₂) z*W (‖eisEmbedding z‖^2/K)) else 0

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels
open MixedCrossSeparation (columnCoefficient)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def canonicalCubeSourcePair (B S T : Finset ι) (v₁ v₂ : ι→ℕ)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  star (canonicalSourceCoefficient p hp hcop hg Ψ₁ m₁ f H₁ S)*
    canonicalSourceCoefficient p hp hcop hg Ψ₂ m₂ f H₂ T*
    ∑'z:O,(star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z)*
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg T z*
      star (multiplicityRow (fun i=>Ideal.span {p i}) hg B v₂ z^3)*
      multiplicityRow (fun i=>Ideal.span {p i}) hg B v₁ z^3)*W (‖eisEmbedding z‖^2/K)

def canonicalCubeOuter (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) : ℂ :=
  star (canonicalSourceCoefficient p hp hcop hg Ψ₁ m₁ f (fun _=>1) (b.rightDivisor∪C))*
    canonicalSourceCoefficient p hp hcop hg Ψ₂ m₂ f (fun _=>1) (b.leftDivisor∪C)

def canonicalCubeResidual (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ) : Finset ι→ℂ :=
  originalLabelColumn p hg b.support b.leftBit b.rightBit negative
    (multiplicativeCoreColumn p Ψ m (fun S=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪S)))
    (∏i∈C,p i) f

def canonicalCubeBeforePoisson (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
    disjointCanonicalSource p hp hcop hg (pool\(b.support∪C))
      (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
      b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
      (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
      W (fun _=>1) (fun _=>1) 1 1 K

def canonicalCubeCorrelation (pool B : Finset ι) (v₁ v₂ : ι→ℕ)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑S∈pool.powerset,∑T∈pool.powerset,
    canonicalCubeSourcePair p hp hcop hg B S T v₁ v₂ Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K

end SecondPassArithmetic

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def canonicalCubeDualZero (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
    ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)*
      actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
        W (fun _=>1) (fun _=>1) 1 1 K
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) 0

end

open ActualEisensteinCubic
open FirstPassCubeLabels

end SecondPassArithmetic

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels

variable {ι:Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

def canonicalCubeDualFinite (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (T:Finset ι→Finset O):ℂ:=
  canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
    ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)*
      ∑h∈(T D).erase 0,actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
        W (fun _=>1) (fun _=>1) 1 1 K
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h

def canonicalCubeDualTail (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (T:Finset ι→Finset O):ℂ:=
  canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
    ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)*
      ∑'h:{h:O // h∉T D},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
        W (fun _=>1) (fun _=>1) 1 1 K
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val

end

open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

end SecondPassArithmetic

open MeasureTheory
open scoped BigOperators Classical

open MeasureTheory
open scoped BigOperators Classical ContDiff

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

namespace CompletedHeight

section

open MeasureTheory Filter Set
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff Topology
open FourierBridge JointLogSeparation

def fixedLogReturnCLM (a b : ℝ) (ha : 0 < a) : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ (positiveCutoff a b ha)).comp
    (SchwartzMap.compCLM ℝ
      (patchedLog_temperate (a/2) (max a b+a/2) (by linarith))
      (patchedLog_proper (a/2) (max a b+a/2) (by linarith)))

lemma fixedLogReturnCLM_apply (a b : ℝ) (ha : 0 < a) (g : 𝓢(ℝ,ℂ)) (x : ℝ) :
    fixedLogReturnCLM a b ha g x = positiveCutoff a b ha x •
      g (patchedLog (a/2) (max a b+a/2) (by linarith) x) := by
  rw [fixedLogReturnCLM,ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply
      ((positiveCutoff a b ha).hasCompactSupport.hasTemperateGrowth (positiveCutoff a b ha).contDiff)]
  rfl

lemma positiveCutoff_support_bounds (a b : ℝ) (ha : 0 < a) (x : ℝ)
    (hx : positiveCutoff a b ha x ≠ 0) : x ∈ Icc (a/2) (max a b+a/2) := by
  have hm : x ∈ Function.support (positiveCutoff a b ha) := hx
  rw [(positiveCutoff a b ha).support_eq] at hm
  change dist x ((a+max a b)/2) < (max a b-a)/2+a/2 at hm
  rw [Real.dist_eq,abs_lt] at hm
  constructor <;> linarith [hm.1,hm.2]

def uniformTwistedSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  fixedLogReturnCLM a b ha (frequencyTwist (CubicReflectionKernel.logSchwartz W a b ha hs hW) t)

lemma uniformTwistedSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W) (t x : ℝ) :
    uniformTwistedSchwartz W a b ha hs hW t x = normTwistedSource W t x := by
  rw [uniformTwistedSchwartz,fixedLogReturnCLM_apply,frequencyTwist_apply,
    CubicReflectionKernel.logSchwartz_apply]
  by_cases hc : positiveCutoff a b ha x=0
  · have hx : W x=0 := by
      by_contra hx
      have := positiveCutoff_one a b ha x (hs hx)
      exact zero_ne_one (hc.symm.trans this)
    simp only [hc,zero_smul,normTwistedSource,hx,mul_zero]
  · have hb := positiveCutoff_support_bounds a b ha x hc
    have hx : 0 < x := by linarith [hb.1]
    rw [patchedLog_eq_log _ _ _ x hb,Real.exp_log hx]
    by_cases hw : W x=0
    · simp only [hw,mul_zero,smul_zero,normTwistedSource]
    · rw [positiveCutoff_one a b ha x (hs hw),one_smul]
      rfl

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open CompletedGauss

end CompletedHeight

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CompletedUnitRows
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open UnrestrictedIdealReindex (unitIdealEquiv span_unit_generator)
local instance instFintypeUnitsO : Fintype ActualEisensteinCubic.Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def rowUnit (z : ActualEisensteinCubic.O) : ActualEisensteinCubic.Oˣ :=
  if hz : z=0 then 1 else (unitIdealEquiv.symm ⟨z,hz⟩).1

def unitIdealPoint (z : ActualEisensteinCubic.O) : ActualEisensteinCubic.Oˣ × Ideal ActualEisensteinCubic.O := (rowUnit z,Ideal.span {z})

end CompletedUnitRows

end

end OAI
end

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def elementCharacter (I : Ideal O) (hI : primaryGenerator I ≠ 0) : O →* ℂ where
  toFun x := eisEmbedding (CubicJacobiGlobal.idealSymbol I x)
  map_one' := by rw [CubicJacobiGlobal.idealSymbol_map_one I hI, map_one]
  map_mul' x y := by rw [CubicJacobiGlobal.idealSymbol_map_mul I hI, map_mul]

def goodPart (I : Ideal O) : Ideal O := CanonicalQuadraticSieve.goodSquarefreePart I

def badPart (I : Ideal O) : Ideal O :=
  ∏ P ∈ CanonicalQuadraticSieve.badPrimeSupport I, P

def extractedGenerator (I : Ideal O) : O :=
  primaryGenerator (goodPart (firstPart I)) *
    primaryGenerator (goodPart (secondPart I)) ^ 2 *
    idealGenerator (cubePart I) ^ 3 *
    (idealGenerator (badPart (firstPart I)) * idealGenerator (badPart (secondPart I)) ^ 2)

end
end SevenEighths.CubicSieve

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge EisensteinSchwartzPoisson JointLogSeparation
noncomputable section

def inverseNormWindow (V : ℝ → ℂ) (y : ℝ) : ℂ := V y / (Real.exp y : ℂ)
def inverseRootWindow (V : ℝ → ℂ) (y : ℝ) : ℂ := V y / (Real.sqrt (Real.exp y) : ℂ)

def firstRootWindows (V : Fin 9 → ℝ → ℂ) : Fin 9 → ℝ → ℂ :=
  ![V 0, V 1, V 2, inverseNormWindow (V 3), inverseRootWindow (V 4),
    inverseNormWindow (V 5), V 6, inverseRootWindow (V 7), inverseRootWindow (V 8)]

def firstLeftSlope : Fin 9 → ℝ := ![1, 0, 1, 0, 0, 1, 0, 1, 0]
def firstRightSlope : Fin 9 → ℝ := ![0, 1, 1, 0, 0, 1, 0, 0, 1]
def firstKernelSlope : Fin 9 → ℝ := ![0, 0, 0, -1, -1, -2, 1, -1, -1]

def secondRootWindows (V : Fin 6 → ℝ → ℂ) : Fin 6 → ℝ → ℂ :=
  ![V 0, inverseNormWindow (V 1), inverseNormWindow (V 2), V 3,
    inverseRootWindow (V 4), inverseRootWindow (V 5)]

def secondLeftSlope : Fin 6 → ℝ := ![1, 0, 1, 0, 1, 0]
def secondRightSlope : Fin 6 → ℝ := ![1, 0, 1, 0, 0, 1]
def secondKernelSlope : Fin 6 → ℝ := ![0, -1, -2, 1, -1, -1]

def firstPoissonProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 9 → ℝ → ℂ) (R : ℝ) (y : Fin 9 → ℝ) : ℂ :=
  (∏ i, firstRootWindows V i (y i)) *
    W₁ (Real.exp (∑ i, firstLeftSlope i * y i)) *
    W₂ (Real.exp (∑ i, firstRightSlope i * y i)) *
    paperRadialFourier Φ (R * Real.exp (∑ i, firstKernelSlope i * y i))

def secondPoissonProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (∏ i, secondRootWindows V i (y i)) *
    W₁ (Real.exp (∑ i, secondLeftSlope i * y i)) *
    W₂ (Real.exp (∑ i, secondRightSlope i * y i)) *
    paperRadialFourier Φ (R * Real.exp (∑ i, secondKernelSlope i * y i))

def profileMode {ι : Type*} [Fintype ι] (V : ι → ℝ → ℂ)
    (a₁ a₂ ak : ι → ℝ) (y : ι → ℝ) (t : Frequency) : ℂ :=
  ∏ i, V i (y i) * logPhase t.1 (a₁ i * y i) *
    logPhase t.2.1 (a₂ i * y i) * logPhase t.2.2 (ak i * y i)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

variable {ι : Type*} [Fintype ι]

def coordinateDensity (g : ι → 𝓢(ℝ, ℂ)) (t : ι → ℝ) : ℂ :=
  ∏ i, (𝓕 (g i)) (t i)

def coordinatePhase (t y : ι → ℝ) : ℂ := ∏ i, logPhase (t i) (y i)

def pureProfileMode (a₁ a₂ ak : ι → ℝ) (y : ι → ℝ)
    (t : Frequency) (u : ι → ℝ) : ℂ :=
  ∏ i, logPhase (u i) (y i) * logPhase t.1 (a₁ i * y i) *
    logPhase t.2.1 (a₂ i * y i) * logPhase t.2.2 (ak i * y i)

def fullProfileDensity (g : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (p : Frequency × (ι → ℝ)) : ℂ :=
  tripleCoefficient b₁ b₂ b₃ p.1 * coordinateDensity g p.2

def tripleHeight (J : ℕ) (t : Frequency) : ℝ :=
  (1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J

def coordinateHeight (J : ℕ) (u : ι → ℝ) : ℝ := ∏ i, (1 + ‖u i‖)^J

def profileHeight (a₁ a₂ ak : ι → ℝ) (t : Frequency) (u : ι → ℝ) (i : ι) : ℝ :=
  u i + a₁ i * t.1 + a₂ i * t.2.1 + ak i * t.2.2

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

structure SecondProfileData (ι : Type*) where
  common : Finset ι
  overlap : Finset ι
  extractedLeft : Finset ι
  extractedRight : Finset ι
  rayLeft : Eis →* ℂ
  rayRight : Eis →* ℂ
  puncture : Eis
  quotient : Eis
  oldLabel : Eis
  oldDivisor : Eis
  divisor : Eis
  frequency : Eis

def secondActualNorms {ι : Type*} (p : ι → Eis) (x : SecondProfileData ι)
    (N M : Finset ι) : Fin 6 → ℝ :=
  ![primeProductNorm p x.common, ‖eisEmbedding x.divisor‖^2,
    primeProductNorm p x.overlap, ‖eisEmbedding x.frequency‖^2,
    primeProductNorm p N, primeProductNorm p M]

def secondActualCoefficient {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ) (N M : Finset ι) : ℂ :=
  star (secondChildColumn p hp hcop hg x.rayLeft (x.puncture*x.quotient)
    (x.oldLabel*x.divisor*∏ i ∈ x.overlap,p i) (x.oldDivisor*x.divisor*x.frequency) (fun _ => 1) N) *
  secondChildColumn p hp hcop hg x.rayRight (x.puncture*x.quotient)
    (x.oldLabel*x.divisor*∏ i ∈ x.overlap,p i) (x.oldDivisor*x.divisor*(-x.frequency)) (fun _ => 1) M *
  (star (primeMark slots₁ lists₁ a₁ (x.extractedLeft ∪ (x.overlap ∪ N))) *
    primeMark slots₂ lists₂ a₂ (x.extractedRight ∪ (x.overlap ∪ M)))

def actualSecondProfileRow {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X : ℝ) : ℂ :=
  (‖eisEmbedding x.divisor‖^2 : ℂ)⁻¹ *
  secondChildKernelPair p hp hcop hg F x.overlap x.rayLeft x.rayRight x.puncture x.quotient
    x.oldLabel x.oldDivisor x.divisor x.frequency (-x.frequency)
    (secondSourcePairKernel p x.divisor x.frequency
      (fun U => primeMark slots₁ lists₁ a₁ (x.extractedLeft ∪ U)*
        W₁ (primeProductNorm p x.common*primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ (x.extractedRight ∪ U)*
        W₂ (primeProductNorm p x.common*primeProductNorm p U/X)) Φ Y)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondProfileIndices {κ ι : Type*} [DecidableEq ι]
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) :
    Finset (Σ _ : κ, Finset ι × Finset ι) :=
  source.sigma (fun j => (F \ (x j).overlap).powerset ×ˢ (F \ (x j).overlap).powerset)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseAmbientProfileTower
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open SevenEighths.InverseMoment
noncomputable section

abbrev Ambient (ι : Type*) := Frequency × (ι → ℝ)

def ambientWeight {ι : Type*} [Fintype ι] (J : ℕ) (p : Ambient ι) : ℝ :=
  ((1 + ‖p.1.1‖)^J * (1 + ‖p.1.2.1‖)^J * (1 + ‖p.1.2.2‖)^J) *
    ∏ i, (1 + ‖p.2 i‖)^J

def inheritedLeft {ι : Type*} (i : ι) (p : Ambient ι) : ℝ :=
  p.2 i + p.1.1 - p.1.2.2

def inheritedRight {ι : Type*} (i : ι) (p : Ambient ι) : ℝ :=
  -(p.2 i + p.1.2.1 - p.1.2.2)

def twistedFullDensity {ι : Type*} [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (θ : ℝ × ℝ) (p : Ambient ι) : ℂ :=
  fullProfileDensity g (𝓕 (frequencyTwist g₁ θ.1))
    (𝓕 (frequencyTwist g₂ θ.2)) b₃ p

end
end SevenEighths.InverseAmbientProfileTower

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
open SevenEighths.InverseMoment

namespace SevenEighths.InverseInitialProfile

def clippedTwist (g : 𝓢(ℝ, ℂ)) (c θ : ℝ) : 𝓢(ℝ, ℂ) :=
  frequencyTwist (SchwartzMap.compSubConstCLM ℂ (-Real.log c) g) θ

@[simp] theorem clippedTwist_apply (g : 𝓢(ℝ, ℂ)) (c θ y : ℝ) :
    clippedTwist g c θ y = logPhase θ y * g (y + Real.log c) := by
  simp [clippedTwist]

def sourceDensity (g : 𝓢(ℝ, ℂ)) (c θ t : ℝ) : ℂ :=
  logPhase (t-θ) (Real.log c) * (𝓕 g) (t-θ)

def clippedSource (W : ℝ → ℂ) (c θ x : ℝ) : ℂ :=
  logPhase θ (Real.log x) * W (c*x)

def normalizedProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (Real.exp (-3*L) : ℂ) * secondPoissonProfile W₁ W₂ Φ V R y

def familyDensity (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Frequency × (Fin 6 → ℝ)) : ℂ :=
  (Real.exp (-3*L) : ℂ) * fullProfileDensity g
    (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p

def logFamilyProfile (g₁ g₂ : 𝓢(ℝ, ℂ)) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (Real.exp (-3*L) : ℂ) *
    ((∏ i, secondRootWindows V i (y i)) *
      clippedTwist g₁ c₁ θ₁ (∑ i, secondLeftSlope i*y i) *
      clippedTwist g₂ c₂ θ₂ (∑ i, secondRightSlope i*y i) *
      paperRadialFourier Φ (R*Real.exp (∑ i, secondKernelSlope i*y i)))

def columnCenter (D B v : ℝ) : ℝ := D-B-v
def prefactorCenter (m D B θ : ℝ) : ℝ := m-2*D+B-θ
def radialCenter (m H θ D B : ℝ) : ℝ := m+H-θ-2*(D-B)

def physicalKernel (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (Z D m : ℝ) (q : Fin 6 → ℝ) : ℂ :=
  ((Z^(-D)*Z^m/(q 1*q 2*Real.sqrt (q 4*q 5)) : ℝ) : ℂ) *
    W₁ (q 0*q 2*q 4/Z^D) * W₂ (q 0*q 2*q 5/Z^D) *
      paperRadialFourier Φ (Z^m*q 3/(q 1*(q 2)^2*q 4*q 5))

def relativeNorm (q : Fin 6 → ℝ) (Z D B v θ H : ℝ) : Fin 6 → ℝ :=
  secondRelativeNorm q (Z^B) (Z^θ) (Z^v) (Z^H) (Z^(columnCenter D B v))

def relativeLog (q : Fin 6 → ℝ) (Z D B v θ H : ℝ) (i : Fin 6) : ℝ :=
  Real.log (relativeNorm q Z D B v θ H i)

def PhysicalIdentityAt (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (Z D B v m θ H η c₁ c₂ θ₁ θ₂ : ℝ) : Prop :=
  ∀ (w₁ w₂ : ℝ → ℂ) (q : Fin 6 → ℝ), (∀ i, 0 < q i) →
    (clippedSource W₁ c₁ θ₁
      (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
        relativeNorm q Z D B v θ H 4) ≠ 0 → w₁ (relativeNorm q Z D B v θ H 4) = 1) →
    (clippedSource W₂ c₂ θ₂
      (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
        relativeNorm q Z D B v θ H 5) ≠ 0 → w₂ (relativeNorm q Z D B v θ H 5) = 1) →
    (w₁ (relativeNorm q Z D B v θ H 4) ≠ 0 →
      w₂ (relativeNorm q Z D B v θ H 5) ≠ 0 →
      ∀ i, V i (relativeLog q Z D B v θ H i) = 1) →
    physicalKernel (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m q =
      (Z^(prefactorCenter m D B θ + 3*η) : ℝ) *
        (w₁ (relativeNorm q Z D B v θ H 4)*w₂ (relativeNorm q Z D B v θ H 5)) *
        ∫ p : Frequency × (Fin 6 → ℝ),
          familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) p *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
              (relativeLog q Z D B v θ H) p.1 p.2

end SevenEighths.InverseInitialProfile

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open SevenEighths.InverseMoment
namespace SevenEighths.InverseInitialClippedColumns
local notation "Eis" => ActualEisensteinCubic.O

def clippedTest (w : ℝ → ℂ) (c h : ℝ) : ℝ → ℂ :=
  childLogTest (fun x => w (c*x)) h

section Arithmetic
variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def freshColumns (pool : Finset ι) (w : ℝ → ℂ) (X : ℝ) : Finset (Finset ι) :=
  pool.powerset.filter (fun U => w (primeProductNorm p U/X) ≠ 0)

def columnEnergy (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (W : ℝ → ℂ) (X : ℝ) : ℝ :=
  ∑ f ∈ labels, D f * ∑ k ∈ rows,
    ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator f) k
      slots lists a W X‖^2

def normalizedColumnEnergy (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (W : ℝ → ℂ) (X Z F : ℝ) : ℝ :=
  ∑ f ∈ labels, D f * ∑ k ∈ rows,
    ‖((Z^(-F/2) : ℝ) : ℂ) *
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator f) k
        slots lists a W X‖^2

end Arithmetic

def leftHeight (z : Frequency × (Fin 6 → ℝ)) : ℝ := z.2 4+z.1.1-z.1.2.2
def rightHeight (z : Frequency × (Fin 6 → ℝ)) : ℝ := z.2 5+z.1.2.1-z.1.2.2

def outerCutoff (ψ : Fin 4 → ℝ → ℂ) (x : Fin 6 → ℝ) : ℂ :=
  ψ 0 (x 0)*ψ 1 (x 1)*ψ 2 (x 2)*ψ 3 (x 3)

end SevenEighths.InverseInitialClippedColumns

end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def expansionProfileData (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (A₁ A₂ : Finset ι) (x : SecondExpansionData ι) : SecondProfileData ι where
  common := x.sourceCommon
  overlap := x.overlap
  extractedLeft := A₁ ∪ x.sourceCommon
  extractedRight := A₂ ∪ x.sourceCommon
  rayLeft := secondRayMinus Ψ z
  rayRight := secondRayPlus Ψ z
  puncture := m
  quotient := secondExpansionQuotient p x
  oldLabel := c
  oldDivisor := d
  divisor := primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor
  frequency := x.frequency

def expansionProfileWeight (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (Y : ℝ) (x : SecondExpansionData ι) : ℂ :=
  (Y : ℂ) * (‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) x.sourceCommon‖^2 : ℝ) *
    (UniqueFactorizationMonoid.moebius (∏ i ∈ x.divisor, Ideal.span {p i}) : ℂ) *
    secondTotalWeight p hp hcop hg Ψ Ψ m (secondExpansionQuotient p x) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (z,x.overlap)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondSignedSourceWeight (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (x : SecondExpansionData ι) : ℂ :=
  (‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) x.sourceCommon‖^2 : ℝ) *
    (UniqueFactorizationMonoid.moebius (∏ i ∈ x.divisor, Ideal.span {p i}) : ℂ) *
    secondCommonWeight p hp hcop hg (secondRayMinus Ψ z) (secondRayPlus Ψ z)
      m (secondExpansionQuotient p x) c d (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
      x.frequency (-x.frequency) x.overlap

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
open scoped ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentLattice
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open QuadraticInitialBound

theorem logPhase_eq_normPower (t x : ℝ) (hx : 0 < x) :
    FourierBridge.logPhase (t / (2 * Real.pi)) (Real.log x) =
      (x : ℂ) ^ (Complex.I * t) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))]
  unfold FourierBridge.logPhase
  rw [← Complex.ofReal_log hx.le]
  congr 1
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  push_cast
  field_simp

def normPowerProfile (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) : 𝓢(ℝ, ℂ) :=
  CompletedHeight.uniformTwistedSchwartz W a b ha hs hW (t / (2 * Real.pi))

theorem normPowerProfile_apply (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t x : ℝ) :
    normPowerProfile W a b ha hs hW t x = (x : ℂ) ^ (Complex.I * t) * W x := by
  rw [normPowerProfile, CompletedHeight.uniformTwistedSchwartz_apply]
  unfold CompletedHeight.normTwistedSource
  by_cases hx : W x = 0
  · simp only [hx, mul_zero]
  · rw [logPhase_eq_normPower t x (lt_of_lt_of_le ha (hs hx).1)]

end SevenEighths.CenteredMomentLattice
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentTwist
open ActualEisensteinCubic EisensteinSchwartzPoisson
open CenteredMomentLattice

lemma normPowerProfile_support (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    Function.support (normPowerProfile W a b ha hs hW t : ℝ → ℂ) ⊆ Function.support W := by
  intro x hx hz
  exact hx (by rw [normPowerProfile_apply, hz, mul_zero])

end SevenEighths.CenteredMomentTwist
end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstBlockedPhysicalRows (F : Finset ι) (selector : Finset ι → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (A₁ A₂ C R K : ℝ) (d h : Eis) : ℂ :=
  ∑ j ∈ firstCommonIndices F, selector j.2.1 * firstCommonWeight p hg C₁ C₂ h j *
    firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K (firstCommonNorms p A₁ A₂ C R d h j)

def firstBlockedSeparatedRow (F : Finset ι) (selector : Finset ι → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ)
    (d h : Eis) (s : Fin 9 → ℝ) (z : Frequency × (Fin 9 → ℝ)) : ℂ :=
  let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
  ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
    ∑ D ∈ F.powerset, selector D * supportMobius (fun i => Ideal.span {p i}) D *
      rowCoprimeMask (fun i => Ideal.span {p i}) D h *
      firstOuterPhase H (firstCommonOuterLog p A₁ A₂ C R d h D s) *
      star (firstCommonColumn p hg F D C₁ true r.1 ω₁ (s 7) (H 7) h) *
      firstCommonColumn p hg F D C₂ false r.2 ω₂ (s 8) (H 8) h

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι κ : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstFamilySeparatedRow (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : κ → ℝ) (d h : κ → Eis)
    (s : Fin 9 → ℝ) (z : Frequency × (Fin 9 → ℝ)) : ℂ :=
  ∑ x∈source,w x*firstBlockedSeparatedRow p hg F (selector x) (C₁ x) (C₂ x)
    ω₁ ω₂ (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) s z

def firstFamilyEnergy (source : Finset κ) (F : Finset ι)
    (selector C : κ → Finset ι → ℂ) (w : κ → ℂ)
    (negative : Bool) (ω : ℝ → ℂ) (X t : ℝ) (h : κ → Eis) : ℝ :=
  ∑ x∈source,‖w x‖*firstBlockEnergy p hg F (selector x) (C x) negative ω X t (h x)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstCubePhysicalMode (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (d h : O) : ℂ :=
  (K:ℂ)*cubeBaseFactor p hp hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit d h *
    firstPhysicalCommonRows p hg (pool\(b.support∪C))
      (cubeMinusCoefficient p hp hcop hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁) d)
      (cubePlusCoefficient p hp hcop hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂) d)
      (fun x=>star (W₁ x)) W₂ Φ
      (‖eisEmbedding (aLabel p b.support b.rightBit)‖^2)
      (‖eisEmbedding (aLabel p b.support b.leftBit)‖^2)
      (primeProductNorm p C)
      (primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)) K d h

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def retainedCubeWeight (b : CubeCoordinates ι) (C : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ)
    (m₁ m₂ d : O) (a : Ideal O×O→ℂ) (x : Ideal O×O) : ℂ :=
  a x * canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator x.1) *
    cubeBaseFactor p hp hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit d x.2

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι κ : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstFamilyPhysicalRows (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ → ℝ) (K : ℝ)
    (d h : κ → Eis) (s : Fin 9 → ℝ) : ℂ :=
  ∑ x∈source,w x*firstBlockedPhysicalRows p hg F (selector x) (C₁ x) (C₂ x)
    (fun y => W₁ (y/(s 0*s 2*s 5*s 7))) (fun y => W₂ (y/(s 1*s 2*s 5*s 8)))
    Φ (A₁ x) (A₂ x) (C x) (R x) K (d x) (h x)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstCanonicalCoefficient (b : CubeCoordinates ι) (C : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m d : O) (H : Finset ι→ℂ) (x : Ideal O×O) : Finset ι→ℂ :=
  firstBareCubeCoefficient p hp hg hcop b.support (fun i=>b.leftExponent i+b.rightExponent i)
    b.leftBit b.rightBit negative
    (canonicalCubeResidual p hg b C negative Ψ m (ConcretePrimeRowBridge.idealGenerator x.1) H) d

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
noncomputable section
local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstCanonicalSecondEnergy (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (H selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) : ℝ :=
  (32*512)*∑ r : RayCharacter×RayCharacter,∑ D∈F.powerset,
    (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ core : FirstCoreIndex,
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D core‖ *
      (firstFreshSecondPoisson p hp hg hinj F D b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative (if negative then r.1 else r.2) Ψ m
        (fun U=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪U)) ω X (∏i∈C,p i) d core t Y).re

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstWholePrioritySecondEnergy (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) : ℝ :=
  let A := extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  (32*512)*(2:ℝ)^slots.card * ∑ r : RayCharacter×RayCharacter,∑ D∈F.powerset,
    (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ core : FirstCoreIndex,
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D core‖ *
      ∑ J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2 *
        (firstFreshSecondPoisson p hp hg hinj F D b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative (if negative then r.1 else r.2) Ψ m
          (fun U=>primeMark (slots\J) (fun i=>lists i\(A∪D)) a U)
          ω X (∏i∈C,p i) d core t Y).re

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InversePrincipalEnergy
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open SecondPassArithmetic FirstPassCubeLabels IdealMobiusDivisorSum
open InverseMoment
local notation "Eis" => ActualEisensteinCubic.O

section
variable {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))

def supportIdeal (G : Finset ι) : Ideal Eis := ∏ i ∈ G, Ideal.span {p i}

def principalFrequency (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ((Y : ℂ) / (‖eisEmbedding (∏ i ∈ (∅ : Finset ι) ∪ ∅, p i)‖ : ℂ)) *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * primeProductNorm p ((∅ : Finset ι) ∪ ∅))) *
    secondGaussTerm p hp hg hinj Ψ Ψ m r c d e k H₁ H₂ ∅ ∅

def restorationTerm (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (G : Finset ι) (E : G.powerset) (k : Eis) : ℂ :=
  secondSourceCommonCoefficient p hg Ψ m c d G E.val *
    principalFrequency p hg hinj hp Ψ m
      (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
      (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y

def principalRestoration (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (θ : Finset ι → Finset ι → Eis → ℂ) : ℂ :=
  ∑ G ∈ F.powerset, ∑ E : G.powerset, ∑' k : {k : Eis // k ≠ 0},
    θ G E.val k.val * restorationTerm p hg hinj hp Ψ m c d H W Y G E k.val

def markedRadial {σ : Type*} [DecidableEq σ]
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) (V : 𝓢(ℝ, ℂ)) (X : ℝ) (G : Finset ι) : ℂ :=
  primeMark slots lists a (A ∪ G) * V (primeProductNorm p G / X)

end

end SevenEighths.InversePrincipalEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseSecondPrincipalCaller
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FourierBridge
open SecondPassIntegration CompletedHeight
open InverseMoment InversePrincipalEnergy RayFourExpansion
local notation "Eis" => ActualEisensteinCubic.O

def principalWindow (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  if negative then conjugateProfile (uniformTwistedSchwartz om a b ha hs (om.smooth ⊤) t)
  else uniformTwistedSchwartz om a b ha hs (om.smooth ⊤) t

end SevenEighths.InverseSecondPrincipalCaller

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondPrincipalCaller
open FourierBridge CompletedHeight SecondPassIntegration
local notation "O" => ActualEisensteinCubic.O

def priorityLogWindow (om:𝓢(ℝ,ℂ)) (a b:ℝ) (ha:0<a)
    (hs:Function.support om⊆Set.Icc a b) (negative:Bool):𝓢(ℝ,ℂ) :=
  if negative then conjugateProfile (CubicReflectionKernel.logSchwartz om a b ha hs (om.smooth ⊤))
  else CubicReflectionKernel.logSchwartz om a b ha hs (om.smooth ⊤)

def priorityHeight (negative:Bool) (t:ℝ):ℝ := if negative then -t else t

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.InverseMoment
open InverseInitialClippedColumns JointLogSeparation InverseAmbientProfileTower
local notation "O"=>ActualEisensteinCubic.O

def secondChildHeight (right:Bool)(t:Ambient (Fin 6)):ℝ :=
  if right then profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2 5
  else -profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2 4

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
section
variable {ι:Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstLocalPhysicalTail (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ))
    (K:ℝ) (T:Finset ι→Finset O) (D:Finset ι):ℂ :=
  ∑'h:{h:O // h∉T D},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
    (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
    (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂) W (fun _=>1) (fun _=>1) 1 1 K
    (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val

end

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def varyingReopenedRow (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : (ι→₀ℕ)→ℂ)
    (Ψ : O→*ℂ) (m f : O) (H : (ι→₀ℕ)→Finset ι→ℂ) (z : O) : ℂ :=
  ∑v∈Q,∑S∈pool.powerset,
    (β v*canonicalSourceCoefficient p hp hcop hg Ψ m f (H v) S)*
    (multiplicityRow (fun i=>Ideal.span {p i}) hg pool v z^3*
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseWholePriorityValidSource
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment
open RayFourExpansion InversePrincipalEnergy InverseSecondPrincipalCaller
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ}

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

variable (hp : ∀ i,p i≠0) (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def wholePriorityPoisson (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C E extra : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : ℝ→ℂ) (X t Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex) (D : Finset ι) : ℂ :=
  firstFreshSecondPoisson p hp hg hinj pool D b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
    (if negative then r.1 else r.2) Ψ m
    (fun U=>primeMark (slots\J)
      (fun i=>lists i\((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)) a U)
    om X (∏ i∈C,p i) (primeSubsetGenerator (fun i=>Ideal.span {p i}) E) core t Y

variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))

end SevenEighths.InverseWholePriorityValidSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

def extra (negative : Bool) (c : CubeCoordinates ι) : Finset ι :=
  if negative then c.rightExponent.support else c.leftExponent.support

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def highSupport (I J K L : Id) : Prop :=
  Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported L

lemma span_primaryGenerator_of_supported (I : Id) (hI : Supported I) :
    Ideal.span {primaryGenerator I}=I :=
  (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).1

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily UniqueFactorizationMonoid

def SixthFree (I : Ideal O) : Prop := ∀ P, (normalizedFactors I).count P<6

theorem ideal_decomposition_unique {I J A B : Ideal O}
    (hI : I≠0) (hJ : J≠0) (hA : A≠0) (hB : B≠0)
    (hIf : SixthFree I) (hJf : SixthFree J) (he : I*A^6=J*B^6) :
    I=J ∧ A=B := by
  have hf := congrArg normalizedFactors he
  rw [normalizedFactors_mul hI (pow_ne_zero _ hA),
    normalizedFactors_mul hJ (pow_ne_zero _ hB),normalizedFactors_pow,normalizedFactors_pow] at hf
  have hc (P : Ideal O) := congrArg (Multiset.count P) hf
  have hcounts (P : Ideal O) :
      (normalizedFactors I).count P=(normalizedFactors J).count P ∧
      (normalizedFactors A).count P=(normalizedFactors B).count P := by
    have hh := hc P
    simp only [Multiset.count_add,Multiset.count_nsmul] at hh
    have hi := hIf P
    have hj := hJf P
    omega
  have hIJ : normalizedFactors I=normalizedFactors J :=
    Multiset.ext.mpr (fun P => (hcounts P).1)
  have hAB : normalizedFactors A=normalizedFactors B :=
    Multiset.ext.mpr (fun P => (hcounts P).2)
  constructor
  · simpa only [Ideal.prod_normalizedFactors_eq_self hI,Ideal.prod_normalizedFactors_eq_self hJ]
      using congrArg Multiset.prod hIJ
  · simpa only [Ideal.prod_normalizedFactors_eq_self hA,Ideal.prod_normalizedFactors_eq_self hB]
      using congrArg Multiset.prod hAB

abbrev FreeRow := {u : O // u≠0 ∧ SixthFree (Ideal.span {u})}
abbrev NonzeroIdeal := UnrestrictedIdealReindex.NonzeroIdeal

def rowMap (p : FreeRow×NonzeroIdeal) : O :=
  p.1.val*(ConcretePrimeRowBridge.idealGenerator p.2.val)^6

theorem rowMap_ne_zero (p : FreeRow×NonzeroIdeal) : rowMap p≠0 :=
  mul_ne_zero p.1.property.1 (pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero
    p.2.val p.2.property))

theorem rowMap_span (p : FreeRow×NonzeroIdeal) :
    Ideal.span {rowMap p}=Ideal.span {p.1.val}*p.2.val^6 := by
  unfold rowMap
  rw [←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_pow,
    ConcretePrimeRowBridge.span_idealGenerator]

theorem rowMap_injective : Function.Injective rowMap := by
  intro p q hpq
  have he := congrArg (fun u : O => Ideal.span {u}) hpq
  rw [rowMap_span,rowMap_span] at he
  have hd := ideal_decomposition_unique
    (Ideal.span_singleton_eq_bot.not.mpr p.1.property.1)
    (Ideal.span_singleton_eq_bot.not.mpr q.1.property.1)
    p.2.property q.2.property p.1.property.2 q.1.property.2 he
  have ha : p.2=q.2 := Subtype.ext hd.2
  apply Prod.ext
  · apply Subtype.ext
    change p.1.val*(ConcretePrimeRowBridge.idealGenerator p.2.val)^6=
      q.1.val*(ConcretePrimeRowBridge.idealGenerator q.2.val)^6 at hpq
    rw [ha] at hpq
    exact mul_right_cancel₀ (pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero
      q.2.val q.2.property)) hpq
  · exact ha

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def canonicalSlotSupport (T : Finset PrimeIdeal) : Finset O :=
  T.image (fun P=>primaryGenerator P.val)

lemma primaryPrime_injective {P Q : PrimeIdeal} (hP : Supported P.val) (hQ : Supported Q.val)
    (h : primaryGenerator P.val=primaryGenerator Q.val) : P=Q := by
  apply Subtype.ext
  have hh := congrArg (fun a : O=>Ideal.span {a}) h
  simpa only [span_primaryGenerator_of_supported _ hP,span_primaryGenerator_of_supported _ hQ] using hh

def canonicalSlotEquiv (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val) :
    ↥T ≃ ↥(canonicalSlotSupport T) :=
  Equiv.ofBijective
    (fun P=>⟨primaryGenerator P.val.val,Finset.mem_image.mpr ⟨P.val,P.property,rfl⟩⟩)
    ⟨by
      intro P Q h
      apply Subtype.ext
      exact primaryPrime_injective (hT P.val P.property) (hT Q.val Q.property) (congrArg Subtype.val h),by
      intro a
      obtain ⟨P,hP,he⟩ := Finset.mem_image.mp a.property
      exact ⟨⟨P,hP⟩,Subtype.ext he⟩⟩

@[simp] lemma canonicalSlotEquiv_val (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (P : T) : (canonicalSlotEquiv T hT P).val=primaryGenerator P.val.val := rfl

def canonicalTupleEquiv {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) :
    (∀i,↥(T i)) ≃ (∀i,↥(canonicalSlotSupport (T i))) :=
  Equiv.piCongrRight (fun i=>canonicalSlotEquiv (T i) (hT i))

@[simp] lemma canonicalTupleEquiv_val {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (P : ∀i,↥(T i)) (i : Fin K) :
    (canonicalTupleEquiv T hT P i).val=primaryGenerator (P i).val.val := rfl

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
abbrev SupportedIdeal := {I : Id // Supported I}

lemma gram_supported_divisor (I D : Id) (hI : Supported I) (hd : D∣I) : Supported D := by
  obtain ⟨J,rfl⟩ := hd
  exact (supported_mul_iff D J).mp hI |>.1

lemma gram_supported_quotient (I D : Id) (hI : Supported I) (hd : D∣I) :
    Supported (idealQuotient D I) := gram_supported_divisor I _ hI (idealQuotient_dvd hd)

def gcdCommon (I J : SupportedIdeal) : SupportedIdeal :=
  ⟨gcd I.val J.val,gram_supported_divisor I.val _ I.property (gcd_dvd_left _ _)⟩

def gcdLeft (I J : SupportedIdeal) : SupportedIdeal :=
  ⟨idealQuotient (gcdCommon I J).val I.val,
    gram_supported_quotient I.val _ I.property (gcd_dvd_left _ _)⟩

def gcdRight (I J : SupportedIdeal) : SupportedIdeal :=
  ⟨idealQuotient (gcdCommon I J).val J.val,
    gram_supported_quotient J.val _ J.property (gcd_dvd_right _ _)⟩

lemma gcd_residual_coprime (I J : SupportedIdeal) : IsCoprime (gcdLeft I J).val (gcdRight I J).val :=
  (gcd_eq_iff_quotient_coprime _ _ _ (gcdCommon I J).property.1
    (gcd_dvd_left _ _) (gcd_dvd_right _ _)).mp rfl

abbrev CoprimeTriple := {t : SupportedIdeal×SupportedIdeal×SupportedIdeal // IsCoprime t.2.1.val t.2.2.val}

def gcdTriple (p : SupportedIdeal×SupportedIdeal) : CoprimeTriple :=
  ⟨(gcdCommon p.1 p.2,gcdLeft p.1 p.2,gcdRight p.1 p.2),gcd_residual_coprime p.1 p.2⟩

def multiplyTriple (t : CoprimeTriple) : SupportedIdeal×SupportedIdeal :=
  (⟨t.val.1.val*t.val.2.1.val,(supported_mul_iff _ _).mpr ⟨t.val.1.property,t.val.2.1.property⟩⟩,
   ⟨t.val.1.val*t.val.2.2.val,(supported_mul_iff _ _).mpr ⟨t.val.1.property,t.val.2.2.property⟩⟩)

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev DivisibleSupported (D : SupportedIdeal) := {I : SupportedIdeal // D.val∣I.val}

def supportedIdealProduct (D J : SupportedIdeal) : SupportedIdeal :=
  ⟨D.val*J.val,(supported_mul_iff _ _).mpr ⟨D.property,J.property⟩⟩

def supportedDilationEquiv (D : SupportedIdeal) : SupportedIdeal≃DivisibleSupported D where
  toFun J := ⟨supportedIdealProduct D J,dvd_mul_right _ _⟩
  invFun I := ⟨idealQuotient D.val I.val.val,gram_supported_quotient I.val.val D.val I.val.property I.property⟩
  left_inv J := by
    apply Subtype.ext
    exact mul_left_cancel₀ D.property.1 (idealQuotient_mul (dvd_mul_right D.val J.val))
  right_inv I := by
    apply Subtype.ext
    apply Subtype.ext
    exact idealQuotient_mul I.property

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

 def frequencyScale (C : SupportedIdeal) (k : O) (Y Q : ℝ) : ℝ :=
  (Ideal.absNorm C.val:ℝ)*‖eisEmbedding k‖^2/(Y^2/Q)

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum UniqueFactorizationMonoid
open CenteredMomentMobiusRegroup
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma divisorPool_supported (G : Finset SupportedIdeal) (D : Id) (hD : D∈divisorPool G Subtype.val) :
    Supported D := by
  obtain ⟨J,hJ,hd⟩ := Finset.mem_biUnion.mp hD
  exact gram_supported_divisor J.val D J.property ((mem_idealDivisors J.property.1).mp hd)

def poolDivisor (G : Finset SupportedIdeal) (D : Id) : SupportedIdeal :=
  if hD : D∈divisorPool G Subtype.val then ⟨D,divisorPool_supported G D hD⟩
  else ⟨1,by
    constructor
    · exact one_ne_zero
    · intro P hP
      change P∈normalizedFactors (1:Id) at hP
      rw [normalizedFactors_one] at hP
      simp at hP⟩

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open ConcreteTraceCRT CenteredMomentMobiusRegroup UniqueFactorizationMonoid
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

def commonResidualScale (C : SupportedIdeal) (Y : ℝ) : ℝ := Y/Ideal.absNorm C.val
lemma commonResidualScale_pos (C : SupportedIdeal) (Y : ℝ) (hY : 0<Y) : 0<commonResidualScale C Y :=
  div_pos hY (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr C.property.1))

end SevenEighths.ProbeGramCommon
end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical SchwartzMap
namespace SevenEighths.InverseInitialProfileBounds
open InverseInitialProfile InverseMoment FourierBridge

theorem childLogTest_eq_clipped (W:ℝ→ℂ)(θ:ℝ):childLogTest W θ=clippedSource W 1 θ:=by
  funext x
  simp only [childLogTest,clippedSource,mul_comm,mul_one]

end SevenEighths.InverseInitialProfileBounds

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentRetainedProfile
open CenteredMomentLattice CenteredMomentTwist
open HeckeFamily
open EisensteinSchwartzPoisson QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O

def dilated (W : ℝ → ℂ) (c : ℝ) : ℝ → ℂ := fun x => W (c * x)

theorem dilated_contDiff (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (c : ℝ) :
    ContDiff ℝ ∞ (dilated W c) :=
  hW.comp (contDiff_const.mul contDiff_id)

theorem dilated_support (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) :
    Function.support (dilated W c) ⊆ Set.Icc (a / B) b := by
  intro x hx
  have hv := hs hx
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hx0 : 0 < x := (mul_pos_iff.mp (lt_of_lt_of_le ha hv.1)).resolve_right
    (by intro h; linarith [h.1]) |>.2
  constructor
  · apply (div_le_iff₀ hB0).mpr
    exact hv.1.trans (by nlinarith)
  · exact (show x ≤ c * x by nlinarith).trans hv.2

def clippedScale (S : ℝ) : ℝ := max 1 S

def clipDilation (S : ℝ) : ℝ := clippedScale S / S

theorem clipDilation_ge_one (S : ℝ) (hS : 0 < S) : 1 ≤ clipDilation S := by
  rw [clipDilation, le_div_iff₀ hS, one_mul]
  exact le_max_right _ _

theorem clipDilation_le (b S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) :
    clipDilation S ≤ max 1 b := by
  rw [clipDilation, div_le_iff₀ hS]
  apply max_le
  · exact hret.trans (by nlinarith [le_max_right (1 : ℝ) b])
  · nlinarith [le_max_left (1 : ℝ) b]

def retainedProfile (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t : ℝ) : 𝓢(ℝ, ℂ) :=
  normPowerProfile (dilated W (clipDilation S)) (a / max 1 b) b
    (div_pos ha (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    (dilated_support W a b (max 1 b) (clipDilation S) ha (le_max_left _ _)
      (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) hs)
    (dilated_contDiff W hW (clipDilation S)) t

theorem retainedProfile_support (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t : ℝ) :
    Function.support (retainedProfile W a b ha hs hW S hS hret t : ℝ → ℂ) ⊆
      Set.Icc (a / max 1 b) b := by
  apply (normPowerProfile_support _ _ _ _ _ _ _).trans
  exact dilated_support W a b (max 1 b) (clipDilation S) ha (le_max_left _ _)
    (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) hs

end SevenEighths.CenteredMomentRetainedProfile

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentUnequal
open CenteredMomentCorrelation CenteredMomentCommonSupport

section Eisenstein
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve
open CompletedGauss
open ConcretePrimeRowBridge hiding O
local notation "O" => ActualEisensteinCubic.O

theorem supported_power (p : O) (hp : Supported (Ideal.span {p})) (i : ℕ) :
    Supported (Ideal.span {p ^ i}) := by
  rw [← Ideal.span_singleton_pow]
  exact supported_pow hp i

end Eisenstein

end SevenEighths.CenteredMomentUnequal

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification UniqueFactorizationMonoid
local instance instIsPrincipalIdealRingO_solutions : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

def unitPart (u : FreeRow) (p : O) (hp : Prime p) : O :=
  Classical.choose ((FiniteMultiplicity.of_prime_left hp u.property.1).exists_eq_pow_mul_and_not_dvd)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

def contourArithmeticCost {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→PrimeIdeal) : ℝ :=
  (η.modulus.absNorm:ℝ)^2*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^6*(∏i,(P i).val.absNorm:ℝ)^3

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def cubeBinRows (R : Finset FreeRow) (idx grid : FreeRow→ℕ) (i k : ℕ) : Finset FreeRow :=
  R.filter (fun u=>idx u=i ∧ grid u=k)

@[simp] lemma mem_cubeBinRows (R : Finset FreeRow) (idx grid : FreeRow→ℕ) (i k : ℕ) (u : FreeRow) :
    u∈cubeBinRows R idx grid i k ↔ u∈R ∧ idx u=i ∧ grid u=k := by simp [cubeBinRows]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end


