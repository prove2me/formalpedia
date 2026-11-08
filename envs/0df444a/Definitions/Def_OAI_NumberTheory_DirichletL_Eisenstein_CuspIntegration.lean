-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspIntegration
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_CuspIntegration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T15:12:37.128706+00:00
-- url     : https://prove2.me/theorems/18d2107b-4f75-4dd6-883b-1b7688221499
-- title:
--   Cusp Integration
-- statement:
--   Definitions and structural lemmas for Cusp Integration, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CuspIntegration.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LogarithmicTargets
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
namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology
def spatialTriple (x y v : ℝ) : SpatialCoordinates := ![x,y,v]
def cuspCylinderMeasure (a b : ℝ) : Measure (ℝ × (ℝ × ℝ)) :=
  (volume.restrict (Set.Icc a b)).prod
    ((volume.restrict (Set.Icc 0 (3*Real.sqrt 3))).prod
      (volume.restrict (Set.Icc 0 3)))
def cuspBoxIntegral (a b : ℝ) (f : SpatialCoordinates → ℂ) : ℂ :=
  ∫q, f (spatialTriple q.2.2 q.2.1 q.1) ∂cuspCylinderMeasure a b
def greenSecondField (s t : ℂ) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  greenSecondTerm (axisSlice (upperEisensteinField s) p j)
    (axisSlice (upperEisensteinField t) p j) (p j)
def greenWronskianField (s t : ℂ) (p : SpatialCoordinates) : ℂ :=
  greenWronskian (axisSlice (upperEisensteinField s) p 2)
    (axisSlice (upperEisensteinField t) p 2) (p 2)
def greenAxisDensity (s t : ℂ) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  greenSecondField s t j p/(p 2:ℂ)
def greenVerticalDensity (s t : ℂ) (p : SpatialCoordinates) : ℂ :=
  greenAxisDensity s t 2 p-greenWronskianField s t p/(p 2:ℂ)^2
def greenBoundaryFlux (s t : ℂ) (p : SpatialCoordinates) : ℂ :=
  greenWronskianField s t p/(p 2:ℂ)
def clampHeight (deltaLoss : ℝ) (p : SpatialCoordinates) : SpatialCoordinates :=
  spatialTriple (p 0) (p 1) (max deltaLoss (p 2))
def extendAboveHeight (deltaLoss : ℝ) (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) : ℂ :=
  f (clampHeight deltaLoss p)
def eisensteinHermitianDensity (s t : ℂ) (p : SpatialCoordinates) : ℂ :=
  upperEisensteinField s p*star (upperEisensteinField t p)/(p 2:ℂ)^3
end CubicEisenstein
open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum
end
open ActualEisensteinCubic
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum
variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
def originalTruncatedMiddle (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) (Y i) (Z i) lengthScale
end CanonicalQuadraticSieve
end
end OAI


