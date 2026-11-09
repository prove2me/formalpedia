-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ScaleCaps
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_ScaleCaps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T03:45:34.62396+00:00
-- url     : https://prove2.me/theorems/6b5b27e6-7f20-4dda-b146-159146727751
-- title:
--   Scale Caps
-- statement:
--   Definitions and structural lemmas for Scale Caps, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/ScaleCaps.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CommonMasks
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_QuotientTopology
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
namespace SecondPassArithmetic
section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct bit parity retained b0Exponent aLabel jLabel j2Label squarefreeLabel b0Label)
variable {ι : Type*} [DecidableEq ι]
def finiteBlockExponent (B : Finset ι) (v : ι → ℕ) : ι →₀ ℕ :=
  Finsupp.onFinset B (fun i => if i∈B then v i else 0) (by
    intro i hi
    by_contra hn
    exact hi (if_neg hn))
def cubeCoordinatesOfBlock (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) : CubeCoordinates ι where
  leftExponent := finiteBlockExponent B v₁
  rightExponent := finiteBlockExponent B v₂
  leftDivisor := B.filter (fun i => ε₁ i)
  rightDivisor := B.filter (fun i => ε₂ i)
def globalSecondOfBlock (B A₀ C D : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondExpansionData ι) : GlobalSecondData ι where
  cube := cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂
  firstCommon := A₀
  common := C
  firstDivisor := D
  source := x
variable (p : ι → OAI.SecondPassArithmetic.O) [∀ i,(Ideal.span {p i}).IsMaximal]
end
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
abbrev GlobalLogIndex := Fin 10 → ℕ
def globalLogRep (j : GlobalLogIndex) (i : Fin 10) : ℝ := normLogScale (j i)
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
def globalScaleVector (side : Bool) (x : GlobalSecondData ι) : Fin 10 → ℝ :=
  ![primeProductNorm p (x.cube.sideDivisor side),primeProductNorm p x.common,
    primeProductNorm p x.firstCommon,primeProductNorm p (x.source.sourceCommon\x.source.divisor),
    globalCubeJNorm p x,primeProductNorm p x.firstDivisor,primeProductNorm p x.source.divisor,
    primeProductNorm p x.source.overlap,‖eisEmbedding (SecondPassFiber.newRow (globalSecondTuple p x))‖^2,
    (globalCubeActiveRoot p x)^2]
def globalScaleIndex (side : Bool) (x : GlobalSecondData ι) : GlobalLogIndex :=
  fun i => normLogBin (globalScaleVector p side x i)
def globalLogSector (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex) : Finset (GlobalSecondData ι) :=
  s.filter (fun x => globalScaleIndex p side x=j)
end
def globalLogBox (U : Fin 10 → ℝ) : Finset GlobalLogIndex :=
  Fintype.piFinset (fun i => Finset.range (normLogBin (U i)+1))
def globalPooledColumnScale (ell : ℝ) (j : GlobalLogIndex) : ℝ :=
  ell/(globalLogRep j 0*globalLogRep j 1*globalLogRep j 2*globalLogRep j 3*globalLogRep j 6*globalLogRep j 7)
def globalPooledLabelScale (j : GlobalLogIndex) : ℝ :=
  globalLogRep j 1*globalLogRep j 4*globalLogRep j 6*globalLogRep j 7*Real.exp 4
def globalPooledRowScale (K ell B F : ℝ) (j : GlobalLogIndex) : ℝ :=
  Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4)
def globalPooledDelta (B F : ℝ) (j : GlobalLogIndex) : ℝ :=
  B*F*globalLogRep j 0*globalLogRep j 2*globalLogRep j 3
def globalPooledNaturalRow (K B F : ℝ) (j : GlobalLogIndex) : ℝ :=
  K*globalLogRep j 4/((globalPooledDelta B F j)^2*B^2)
end SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
end CanonicalQuadraticSieve
open scoped BigOperators Classical
namespace SecondPassArithmetic
section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
def globalActualResidualScale (ell : ℝ) (side : Bool) (x : GlobalSecondData ι) : ℝ :=
  globalFirstColumnScale p ell x side/
    (primeProductNorm p x.firstCommon*primeProductNorm p x.source.divisor*
      primeProductNorm p (x.source.sourceCommon\x.source.divisor))
end
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
def globalNormCaps (ell B Y M Z : ℝ) : Fin 10 → ℝ :=
  let lengthScale := ell*Real.exp M
  ![lengthScale,lengthScale,lengthScale,lengthScale,B^2,lengthScale*B^2,lengthScale,lengthScale,3*lengthScale^2*B^2*((⌈Z*lengthScale^2/Y⌉₊ : ℝ)+1)^2,B^2]
end SecondPassArithmetic
end
end OAI


