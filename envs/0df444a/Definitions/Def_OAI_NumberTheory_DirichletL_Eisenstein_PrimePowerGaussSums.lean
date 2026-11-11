-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_PrimePowerGaussSums
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_PrimePowerGaussSums
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T21:32:29.510042+00:00
-- url     : https://prove2.me/theorems/69bdd3a8-57e7-49f1-babf-1d9faaf74f75
-- title:
--   Prime Power Gauss Sums
-- statement:
--   Definitions and structural lemmas for Prime Power Gauss Sums, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/PrimePowerGaussSums.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ResidualCuspDecay
import Theorems.Thm_OAI_CubicEisenstein_cuspHeightQuotientCompact_isCompact

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace CubicEisenstein
section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O
end
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O
structure SubexponentialBesselCoefficients where
  value : ActualEisensteinCubic.O→ℂ
  growth : ∀epsilon : ℝ,0<epsilon → ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
    ‖value h‖≤C*Real.exp (epsilon*‖cuspFrequency h‖)
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)
def term (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) : ℂ :=
  if h=0 then 0 else (coeff.value h/cubicBesselNormalizer h)*(p.1:ℂ)^(2/3:ℂ)*
    sourceFourierKernel (4/3) (cuspFrequency h*p.1)*ShortDraftTrace.breveE (cuspFrequency h*p.2)
def amplitude (v : ℝ) (h : ActualEisensteinCubic.O) : ℂ :=
  if h=0 then 0 else coeff.value h*(v:ℂ)*
    schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)
def series (p : ℝ × ℂ) : ℂ := ∑'h : ActualEisensteinCubic.O,coeff.term h p
def function (w : HyperbolicSpace) : ℂ := coeff.series (hyperbolicHeight w,hyperbolicHorizontal w)
end SubexponentialBesselCoefficients
end
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)
def fullFunction (constant : ℂ) (w : HyperbolicSpace) : ℂ :=
  constant*(hyperbolicHeight w:ℂ)^(2/3:ℂ)+coeff.function w
end SubexponentialBesselCoefficients
end CubicEisenstein
open scoped BigOperators Classical
namespace ShortDraftCRT
variable {R : Type*} [CommRing R]
end ShortDraftCRT
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
namespace CubicEisenstein
open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O
def translatedHeightCompact (M:levelTwo) (a b:ℝ) : Set KernelQuotient :=
  kernelSourceAction M '' cuspHeightQuotientCompact a b
lemma translatedHeightCompact_isCompact (M:levelTwo) (a b:ℝ) (ha:0<a) :
    IsCompact (translatedHeightCompact M a b) :=
  (cuspHeightQuotientCompact_isCompact a b ha).image (kernelSourceAction_continuous M)
def translatedHeightFourier (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) : KernelQuotientL2→L[ℂ]ℂ :=
  (kernelCuspHeightFourier a b ha ρ h).comp (kernelSourcePullback M).toContinuousLinearMap
def translatedHeightFamily (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (s:ℂ) : ℂ :=
  translatedHeightFourier a b ha ρ h M
    (kernelLocalCorrectedSeed (translatedHeightCompact M a b)
      (translatedHeightCompact_isCompact M a b ha) 2 3 (by norm_num) (by norm_num) s)
end CubicEisenstein
end
end OAI


