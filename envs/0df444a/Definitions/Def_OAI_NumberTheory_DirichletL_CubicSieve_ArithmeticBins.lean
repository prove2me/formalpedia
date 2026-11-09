-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ArithmeticBins
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_ArithmeticBins
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T04:19:50.945503+00:00
-- url     : https://prove2.me/theorems/f3d48dac-f2b8-4a98-a33e-fb173aa7cd6e
-- title:
--   Arithmetic Bins
-- statement:
--   Definitions and structural lemmas for Arithmetic Bins, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/ArithmeticBins.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonComparison
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
namespace SecondPassArithmetic
section
open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)
open SecondPassIntegration (densityChildEnergy)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
def globalArithmeticBin (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex) : Finset (GlobalSecondData ι) :=
  s.filter (fun x => globalSecondFixedTriple p x=q ∧ globalScaleIndex p side x=j)
def globalSquarefreeBin (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex) : Finset (GlobalSecondData ι) :=
  (globalArithmeticBin p s side q j).filter (fun x => Squarefree (newLabel (globalSecondTuple p x)))
def globalArithmeticTargets (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex) : Finset (Ideal O × O) :=
  (globalSquarefreeBin p s side q j).image (fun x => (newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x)))
def globalBinZ (ell : ℝ) (side : Bool) (j : GlobalLogIndex) (x : GlobalSecondData ι) : ℝ :=
  secondSectorZ p (globalActualResidualScale p ell side x) (globalPooledColumnScale ell j)
    (expansionSupportData x.common x.firstDivisor x.source)
def globalBinUd (j : GlobalLogIndex) (x : GlobalSecondData ι) : ℝ :=
  secondSectorUd p (globalLogRep j 5) (expansionSupportData x.common x.firstDivisor x.source)
def globalBinUe (j : GlobalLogIndex) (x : GlobalSecondData ι) : ℝ :=
  secondSectorUe p (globalLogRep j 6) (expansionSupportData x.common x.firstDivisor x.source)
def globalBinUv (j : GlobalLogIndex) (x : GlobalSecondData ι) : ℝ :=
  secondSectorUv p (globalLogRep j 7) (expansionSupportData x.common x.firstDivisor x.source)
def globalBinKap (j : GlobalLogIndex) (x : GlobalSecondData ι) : ℝ :=
  secondSectorKap p (globalLogRep j 8) (expansionSupportData x.common x.firstDivisor x.source)
def globalBinRadial (ell Y : ℝ) (j : GlobalLogIndex) : ℝ :=
  Y*globalLogRep j 8/(globalLogRep j 5*(globalLogRep j 6)^2*(globalLogRep j 7)^2*(globalPooledColumnScale ell j)^2)
def globalArithmeticBinSource (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (ell Y : ℝ) : ℂ :=
  globalSecondRawSource p hp hcop hg (globalArithmeticBin p s side q j)
    (globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side)
    F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) m A₁ A₂ W V
    (globalBinZ p ell side j) (globalBinUd p j) (globalBinUe p j) (globalBinUv p j) (globalBinKap p j)
    (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (globalBinRadial ell Y j)
end
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
def fixedDepthRank (Z K : ℝ) : ℕ := ⌈1000*Real.log K/Real.log Z⌉₊
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
end SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
def activeGcdColumns (N : ℝ) (a : idealRange N → ℂ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    gcdRaySupport (fun I : idealRange N => I.val) a D c → Ideal O :=
  fun j => idealQuotient D j.val.val
def activeGcdCoefficient (N : ℝ) (a : idealRange N → ℂ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    gcdRaySupport (fun I : idealRange N => I.val) a D c → ℂ := fun j => a j.val
end
def selectedPoissonT (C M X η : ℝ) : ℝ := C*(M*X)^η
def selectedPoissonK (C M X η : ℝ) : ℝ := selectedPoissonT C M X η*X^2/M
end CanonicalQuadraticSieve
open Filter MeasureTheory EuclideanGeometry
open scoped BigOperators Classical Topology InnerProductSpace ENNReal
namespace CubicEisenstein
abbrev EuclideanSpatial := EuclideanSpace ℝ (Fin 3)
def euclideanUpperHalf : Set EuclideanSpatial := {p | 0<p 2}
def hyperbolicDensity (p : EuclideanSpatial) : ℝ≥0∞ := ENNReal.ofReal ((p 2)^3)⁻¹
def hyperbolicEuclideanVolume : Measure EuclideanSpatial :=
  (volume.restrict euclideanUpperHalf).withDensity hyperbolicDensity
def euclideanInversion : EuclideanSpatial → EuclideanSpatial := inversion 0 1
def euclideanInversionDeriv (p : EuclideanSpatial) : EuclideanSpatial →L[ℝ] EuclideanSpatial :=
  (1/‖p‖)^2 • (((ℝ ∙ p)ᗮ).reflection : EuclideanSpatial →L[ℝ] EuclideanSpatial)
end CubicEisenstein
end
end OAI


