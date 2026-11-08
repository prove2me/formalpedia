-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_TwistedProfiles
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_TwistedProfiles
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:53:06.137987+00:00
-- url     : https://prove2.me/theorems/5329c8c2-2184-418e-b648-b0f64b4ad92c
-- title:
--   Twisted Profiles
-- statement:
--   Definitions and structural lemmas for Twisted Profiles, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/TwistedProfiles.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_TruncatedSecondTransfer
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_SecondPassIntegration_exists_fixed_twisted_normalized_child_tests
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply


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
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassArithmetic
section
open ActualEisensteinCubic
open JointLogSeparation
open FirstPassCubeLabels (jLabel)
open SecondPassIntegration (exists_fixed_twisted_normalized_child_tests elementNorm)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
end
section
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic
open FirstPassCubeLabels (b0Label firstLogDensity)
open SecondPassIntegration (childGeometricMean)
open JointLogSeparation
end
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)
open FourierBridge (logPhase)
open SecondPassIntegration (conjugateProfile)
def firstCoreBaseProfile (g V : 𝓢(ℝ, ℂ)) (negative : Bool) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (if negative then conjugateProfile V else V) g
def firstCoreModeHeight (negative : Bool) (t : ℝ) : ℝ := if negative then t else -t
def firstCoreModeProfile (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (t : ℝ) : 𝓢(ℝ, ℂ) :=
  frequencyTwist (firstCoreBaseProfile g V negative) (firstCoreModeHeight negative t)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hp
end SecondPassArithmetic
namespace CubicEisenstein
open Filter
open scoped BigOperators Classical MatrixGroups Matrix Topology
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT
abbrev UpperCoordinates := {p : ℂ × ℝ // 0 < p.2}
def coordinateSection (w : UpperCoordinates) : SL(2,ℂ) :=
  upperSection w.1.1 w.1.2 w.2
end CubicEisenstein
open Filter
open scoped BigOperators Classical Topology
namespace CubicEisenstein
def logRatioPower (s : ℂ) (v q : ℝ) : ℂ :=
  Complex.exp (s * ((Real.log v - Real.log q : ℝ) : ℂ))
def quadraticHeightDenominator (A B C D x y v : ℝ) : ℝ :=
  A*(x^2+y^2+v^2)+2*(B*x+C*y)+D
def spatialHeightPower (s : ℂ) (A B C D x y v : ℝ) : ℂ :=
  logRatioPower s v (quadraticHeightDenominator A B C D x y v)
def heightLogDx (A B C D x y v : ℝ) : ℝ :=
  -(2*(A*x+B)/quadraticHeightDenominator A B C D x y v)
def heightLogDy (A B C D x y v : ℝ) : ℝ :=
  -(2*(A*y+C)/quadraticHeightDenominator A B C D x y v)
def heightLogDv (A B C D x y v : ℝ) : ℝ :=
  1/v - 2*A*v/quadraticHeightDenominator A B C D x y v
def heightLogDxx (A B C D x y v : ℝ) : ℝ :=
  -((2*A*quadraticHeightDenominator A B C D x y v -
    (2*(A*x+B))*(2*(A*x+B)))/(quadraticHeightDenominator A B C D x y v)^2)
def heightLogDyy (A B C D x y v : ℝ) : ℝ :=
  -((2*A*quadraticHeightDenominator A B C D x y v -
    (2*(A*y+C))*(2*(A*y+C)))/(quadraticHeightDenominator A B C D x y v)^2)
def heightLogDvv (A B C D x y v : ℝ) : ℝ :=
  -(1/v^2) - ((2*A*quadraticHeightDenominator A B C D x y v -
    (2*A*v)*(2*A*v))/(quadraticHeightDenominator A B C D x y v)^2)
def hyperbolicLaplacian (f : ℝ → ℝ → ℝ → ℂ) (x y v : ℝ) : ℂ :=
  (v:ℂ)^2 * (deriv (deriv (fun t => f t y v)) x +
    deriv (deriv (fun t => f x t v)) y + deriv (deriv (f x y)) v) -
    (v:ℂ)*deriv (f x y) v
def actualHeightPower (s : ℂ) (u : Fin 2 → ℂ) (x y v : ℝ) : ℂ :=
  ((transformedHeight ((x:ℂ)+(y:ℂ)*Complex.I) v u : ℝ) : ℂ)^s
end CubicEisenstein
end
end OAI


