-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_IdealQuotients
-- name    : OAI_NumberTheory_DirichletL_QuadraticSieve_IdealQuotients
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:20:41.679587+00:00
-- url     : https://prove2.me/theorems/cd3d1800-5418-40c0-8037-c05070b233b5
-- title:
--   Ideal Quotients
-- statement:
--   Definitions and structural lemmas for Ideal Quotients, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/IdealQuotients.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoprimeBilinearBound
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RayExpansion
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
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
namespace CanonicalQuadraticSieve
section
open ConcretePrimeRowBridge ActualEisensteinCubic CompletedGauss ConcreteTraceCRT
end
open ActualEisensteinCubic CompletedGauss
def idealQuotient (D I : Ideal O) : Ideal O := if h : D ∣ I then h.choose else 0
def quotientMatrix {m n : Type*} (D : Ideal O) (rows : m → Ideal O) (cols : n → Ideal O) :
    Matrix m n ℂ := fun i j => if D ∣ cols j then
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)) else 0
end CanonicalQuadraticSieve
section
open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff
namespace FourierBridge
def fourierSeminormBound (k : ℕ) (C : ℝ) : ℝ :=
  (2 : ℝ) ^ k * (k + 1) *
    (2 ^ (volume : Measure ℝ).integrablePower *
      ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C
def fourierPointBound (k : ℕ) (C : ℝ) : ℝ :=
  2 ^ k * (fourierSeminormBound 0 C + fourierSeminormBound k C)
end FourierBridge
namespace LocalLogFourier
end LocalLogFourier
namespace EisensteinSchwartzPoisson
end EisensteinSchwartzPoisson
end
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius supportRay supportIdealFamily supportIdealFamily_pos
  supportIdealFamily_good recoveredSupport)
open ConcretePrimeRowBridge (conjugateIdealRowSum)
open RayFourExpansion (RayCharacter crossCoeff)
open ConcreteTraceCRT (eisEmbedding)
def rayIdealRow {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : Finset ι → ℂ) (negative : Bool)
    (χ : RayCharacter) (D : Finset ι) (h : O) : ℂ :=
  let P := fun i => Ideal.span {p i}
  conjugateIdealRowSum (supportIdealFamily P (F \ D))
    (supportIdealFamily_pos P (F \ D)) (supportIdealFamily_good P hg (F \ D))
    (fun I => (if negative then star (supportRay p χ (recoveredSupport P (F \ D) I))
      else supportRay p χ (recoveredSupport P (F \ D) I)) *
        C (D ∪ recoveredSupport P (F \ D) I)) h
def rayPairWeight {ι : Type*} (p : ι → O)
    (r : RayCharacter × RayCharacter) (D : Finset ι) (h : O) : ℂ :=
  crossCoeff r.1 r.2 * (supportMobius (fun i => Ideal.span {p i}) D *
    rowCoprimeMask (fun i => Ideal.span {p i}) D h * supportRay p r.1 D * supportRay p r.2 D)
def rayIdealEnergy {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : Finset ι → ℂ) (negative : Bool) (h : O) : ℝ :=
  ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
    ‖rayPairWeight p r D h‖ *
      ‖rayIdealRow p hg F C negative (if negative then r.1 else r.2) D h‖ ^ 2
def cubeLogCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (d : O) :
    Finset ι → ℂ :=
  if negative then cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C V y t) d
  else cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C V y t) d
end FirstPassCubeLabels
end
end OAI


