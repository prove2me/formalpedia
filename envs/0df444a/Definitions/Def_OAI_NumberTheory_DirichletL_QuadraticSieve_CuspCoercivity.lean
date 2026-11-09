-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CuspCoercivity
-- name    : OAI_NumberTheory_DirichletL_QuadraticSieve_CuspCoercivity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-08T19:31:13.350334+00:00
-- url     : https://prove2.me/theorems/208c3c4c-9c34-499b-ad0e-5a17d68aecd8
-- title:
--   Cusp Coercivity
-- statement:
--   Definitions and structural lemmas for Cusp Coercivity, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/CuspCoercivity.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PrincipalDensity
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
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
end CanonicalQuadraticSieve
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace
namespace CubicEisenstein
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ENNReal
abbrev CuspChartCoordinates := (ℝ×ℝ)×ℝ
def cuspBaseArea : Measure (ℝ×ℝ) := volume.restrict cuspRectangle
instance cuspBaseArea_sFinite : SFinite cuspBaseArea := by unfold cuspBaseArea; infer_instance
def cuspChartVolume (a : ℝ) : Measure CuspChartCoordinates :=
  (cuspBaseArea.prod (volume.restrict (Set.Ioi a))).withDensity
    (fun q => ENNReal.ofReal ((q.2^3)⁻¹))
abbrev CuspChartL2 (a : ℝ) := Lp ℂ 2 (cuspChartVolume a)
example (a : ℝ) : InnerProductSpace ℂ (CuspChartL2 a) := inferInstance
example (a : ℝ) : CompleteSpace (CuspChartL2 a) := inferInstance
def cuspVerticalDerivative (F : CuspChartCoordinates → ℂ) (q : CuspChartCoordinates) : ℂ :=
  deriv (fun v => F (q.1,v)) q.2
def cuspVerticalVelocity (F : CuspChartCoordinates → ℂ) (q : CuspChartCoordinates) : ℂ :=
  (q.2:ℂ)*cuspVerticalDerivative F q
def cuspCoordinateVelocity (F : CuspChartCoordinates → ℂ)
    (q : CuspChartCoordinates) : Fin 3 → ℂ :=
  ![(q.2:ℂ)*deriv (fun x => F ((x,q.1.2),q.2)) q.1.1,
    (q.2:ℂ)*deriv (fun y => F ((q.1.1,y),q.2)) q.1.2,
    cuspVerticalVelocity F q]
def cuspDirichletEnergy (F : CuspChartCoordinates → ℂ) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻q,∑j : Fin 3,ENNReal.ofReal (‖cuspCoordinateVelocity F q j‖^2) ∂cuspChartVolume a
end
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
end
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ENNReal ContDiff
def cuspCoordinateVector : Fin 3 → CuspChartCoordinates := ![((1,0),0),((0,1),0),((0,0),1)]
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


