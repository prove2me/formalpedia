-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0068_1_1
-- name    : PNT_ZeroFree_433_0068_1_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T20:39:08.497473+00:00
-- url     : https://prove2.me/theorems/df7b48ba-f558-40a9-a7d0-e3d1662d2f45
-- title:
--   Zero-free region foundations: Reciprocity.RamifiedSymbol [0068_1_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Reciprocity.RamifiedSymbol
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/RamifiedSymbol.lean#L158-L240

import Definitions.Def_PNT_ZeroFree_433_0068_1_1_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/RamifiedSymbol.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

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

namespace CubicRamified
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss


theorem symbol_lambda_eq_linearRay (y : O) (hy : lambda ^ 2 ∣ y-1) :
    symbol lambda y = linearRay 1 0 y := by
  apply symbol_eq_linearRay_of_prime lambda 1 0 _ y hy
  intro p hp hprimary
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  obtain ⟨A,B,hpAB⟩ := exists_primaryCoord p hprimary
  rw [symbol, idealSymbol_prime _ hg]
  have hc := cubicValue_lambda_primary (Ideal.span {p}) hg A B (by rw [hpAB])
  rw [hc, hpAB, linearRay_primaryCoord]
  simp [cubicExp]

theorem symbol_omega_eq_linearRay (y : O) (hy : lambda ^ 2 ∣ y-1) :
    symbol omega y = linearRay 2 (-1) y := by
  apply symbol_eq_linearRay_of_prime omega 2 (-1) _ y hy
  intro p hp hprimary
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  obtain ⟨A,B,hpAB⟩ := exists_primaryCoord p hprimary
  rw [symbol, idealSymbol_prime _ hg]
  have hc := cubicValue_omega_primary (Ideal.span {p}) hg A B (by rw [hpAB])
  rw [hc, hpAB, linearRay_primaryCoord]
  simp [cubicExp, sub_eq_add_neg]

theorem cubicValue_traceLambda_primary (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (A B : ℤ) (hP : P = Ideal.span {primaryCoord A B}) :
    cubicChar P hg (Ideal.Quotient.mk P traceLambda) = cubicExp (-B) := by
  have htrace : traceLambda = -omega * lambda := by
    change 1 + 2 * omega = -omega * (omega - 1)
    linear_combination omega_sq_for_norm
  rw [htrace, map_mul, map_mul, cubicValue_neg,
    cubicValue_omega_primary P hg A B hP, cubicValue_lambda_primary P hg A B hP]
  change cubicExp (2*A-B) * cubicExp A = cubicExp (-B)
  rw [← cubicExp_add]
  exact cubicExp_eq_of_dvd_sub ⟨A, by ring⟩

theorem symbol_traceLambda_eq_linearRay (y : O) (hy : lambda ^ 2 ∣ y-1) :
    symbol traceLambda y = linearRay 0 (-1) y := by
  apply symbol_eq_linearRay_of_prime traceLambda 0 (-1) _ y hy
  intro p hp hprimary
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  obtain ⟨A,B,hpAB⟩ := exists_primaryCoord p hprimary
  rw [symbol, idealSymbol_prime _ hg]
  have hc := cubicValue_traceLambda_primary (Ideal.span {p}) hg A B (by rw [hpAB])
  rw [hc, hpAB, linearRay_primaryCoord]
  simp

theorem linearRay_congr_mod_nine (u v : ℤ) (x y : O)
    (hx : lambda ^ 2 ∣ x-1) (hy : lambda ^ 2 ∣ y-1) (hxy : (9 : O) ∣ x-y) :
    linearRay u v x = linearRay u v y := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord x hx
  obtain ⟨C,D,rfl⟩ := exists_primaryCoord y hy
  obtain ⟨z,hz⟩ := hxy
  obtain ⟨E,F,hEF⟩ := ActualEisensteinCoordinates.exists_coordinates z
  change z = (E : O) + (F : O) * omega at hEF
  have hcoords : ActualEisensteinCoordinates.eval (3*(A-C)) (3*(B-D)) =
      ActualEisensteinCoordinates.eval (9*E) (9*F) := by
    have he (a b : ℤ) : ActualEisensteinCoordinates.eval a b =
        (a : O) + (b : O) * omega := rfl
    simp only [he]
    rw [hEF, primaryCoord_eq, primaryCoord_eq] at hz
    push_cast
    linear_combination hz
  have hab := ActualEisensteinCoordinates.unique_coordinates hcoords
  have ha : A-C = 3*E := by omega
  have hb : B-D = 3*F := by omega
  rw [linearRay_primaryCoord, linearRay_primaryCoord]
  apply cubicExp_eq_of_dvd_sub
  refine ⟨u*E+v*F, ?_⟩
  linear_combination u*ha + v*hb

theorem symbol_lambda_congr_mod_nine (x y : O)
    (hx : lambda ^ 2 ∣ x-1) (hy : lambda ^ 2 ∣ y-1) (hxy : (9 : O) ∣ x-y) :
    symbol lambda x = symbol lambda y := by
  rw [symbol_lambda_eq_linearRay x hx, symbol_lambda_eq_linearRay y hy]
  exact linearRay_congr_mod_nine 1 0 x y hx hy hxy


end CubicRamified

namespace CubicJacobiGlobal
open ActualEisensteinCubic CompletedGauss CubicRamified


end CubicJacobiGlobal

namespace PrimaryIdealUnitReindex
open ActualEisensteinCubic ActualEisensteinCoordinates ShortDraftLatticeCount


end PrimaryIdealUnitReindex

open scoped BigOperators Classical SchwartzMap
namespace QuadraticUnitInvariance
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open GaussGeneratorTransport QuadraticGaussRay EisensteinSchwartzPoisson
open PrimaryIdealUnitReindex CompletedGauss


end QuadraticUnitInvariance

namespace GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase


end GaussGeneratorTransport

namespace QuadraticUnitInvariance
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open QuadraticGaussRay MixedCrossSeparation QuadraticInitialBound
open GaussGeneratorTransport EisensteinSchwartzPoisson


end QuadraticUnitInvariance

open scoped BigOperators Classical SchwartzMap
namespace EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT


end EisensteinSchwartzPoisson

end

end OAI

end


