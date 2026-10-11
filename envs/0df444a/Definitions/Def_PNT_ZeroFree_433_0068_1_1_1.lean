-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0068_1_1_1
-- name    : PNT_ZeroFree_433_0068_1_1_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T16:46:24.457598+00:00
-- url     : https://prove2.me/theorems/7db16fe7-a62b-40ac-9975-4d9c844dc3e0
-- title:
--   Zero-free region foundations: Reciprocity.RamifiedSymbol [0068_1_1_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Reciprocity.RamifiedSymbol
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/RamifiedSymbol.lean#L78-L156

import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0067

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

def cubicExp (n : ℤ) : O := omega ^ (n % 3).toNat

lemma cubicExp_eq_of_dvd_sub {a b : ℤ} (h : 3 ∣ a - b) : cubicExp a = cubicExp b := by
  obtain ⟨k, hk⟩ := h
  have heq : a % 3 = b % 3 := by omega
  simp only [cubicExp, heq]

lemma cubicExp_add (a b : ℤ) : cubicExp (a + b) = cubicExp a * cubicExp b := by
  simp only [cubicExp, ← pow_add]
  apply ((omega_primitive.isOfFinOrder (by decide)).pow_inj_mod).mpr
  rw [← omega_primitive.eq_orderOf]
  omega

@[simp] lemma cubicExp_zero : cubicExp 0 = 1 := by simp [cubicExp]

def linearRay (u v : ℤ) (x : O) : O :=
  cubicExp (u * (((ActualEisensteinCoordinates.coords x).1 - 1) / 3) +
    v * ((ActualEisensteinCoordinates.coords x).2 / 3))

lemma linearRay_primaryCoord (u v A B : ℤ) :
    linearRay u v (primaryCoord A B) = cubicExp (u*A + v*B) := by
  simp only [linearRay, primaryCoord, ShortDraftLatticeCount.coords_eval]
  rw [show (1 + 3*A - 1) / 3 = A by omega,
    show 3*B / 3 = B by omega]

lemma exists_primaryCoord (x : O) (hx : lambda ^ 2 ∣ x - 1) :
    ∃ A B : ℤ, x = primaryCoord A B := by
  have hthree : (3 : O) ∣ lambda ^ 2 := by
    refine ⟨-omega, ?_⟩
    rw [lambda_def]
    linear_combination omega_sq_for_norm
  obtain ⟨z, hz⟩ := hthree.trans hx
  obtain ⟨A, B, hAB⟩ := ActualEisensteinCoordinates.exists_coordinates z
  change z = (A : O) + (B : O) * omega at hAB
  refine ⟨A, B, ?_⟩
  rw [primaryCoord_eq]
  rw [hAB] at hz
  linear_combination hz

lemma primaryCoord_mul (A B C D : ℤ) :
    primaryCoord A B * primaryCoord C D =
      primaryCoord (A+C+3*(A*C-B*D)) (B+D+3*(A*D+B*C-B*D)) := by
  simp only [primaryCoord, ActualEisensteinCoordinates.eval_mul]
  congr 1 <;> ring

lemma linearRay_one (u v : ℤ) : linearRay u v 1 = 1 := by
  have hone : (1 : O) = primaryCoord 0 0 := by rw [primaryCoord_eq]; simp
  conv_lhs => rw [hone, linearRay_primaryCoord]
  simp

lemma linearRay_mul (u v : ℤ) (x y : O)
    (hx : lambda ^ 2 ∣ x - 1) (hy : lambda ^ 2 ∣ y - 1) :
    linearRay u v (x*y) = linearRay u v x * linearRay u v y := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord x hx
  obtain ⟨C,D,rfl⟩ := exists_primaryCoord y hy
  rw [primaryCoord_mul]
  simp only [linearRay_primaryCoord]
  rw [← cubicExp_add]
  apply cubicExp_eq_of_dvd_sub
  refine ⟨u*(A*C-B*D)+v*(A*D+B*C-B*D), ?_⟩
  ring

theorem symbol_eq_linearRay_of_prime (x : O) (u v : ℤ)
    (hprime : ∀ p : O, Prime p → lambda ^ 2 ∣ p-1 → symbol x p = linearRay u v p)
    (y : O) (hy : lambda ^ 2 ∣ y-1) : symbol x y = linearRay u v y := by
  obtain ⟨A,B,hyAB⟩ := exists_primaryCoord y hy
  have hy0 : y ≠ 0 := by rw [hyAB]; exact primaryCoord_ne_zero A B
  obtain ⟨s,hsprod,hs⟩ := exists_primary_prime_factorization y hy0 hy
  rw [← hsprod]
  clear hsprod hyAB hy hy0 A B y
  induction s using Multiset.induction_on with
  | empty => simp only [Multiset.prod_zero, symbol_one, linearRay_one]
  | @cons p s ih =>
    have hp := hs p (Multiset.mem_cons_self _ _)
    have hss : ∀ r ∈ s, Prime r ∧ lambda ^ 2 ∣ r-1 :=
      fun r hr => hs r (Multiset.mem_cons_of_mem hr)
    rw [Multiset.prod_cons, symbol_mul_denominator,
      hprime p hp.1 hp.2, ih hss,
      linearRay_mul u v p s.prod hp.2 (primary_multiset_prod s (fun r hr => (hss r hr).2))]


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


