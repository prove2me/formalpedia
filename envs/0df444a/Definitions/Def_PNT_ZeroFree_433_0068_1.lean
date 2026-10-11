-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0068_1
-- name    : PNT_ZeroFree_433_0068_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T20:40:54.583983+00:00
-- url     : https://prove2.me/theorems/0bf89373-eb0c-4c6c-b445-385f8ea09fdc
-- title:
--   Zero-free region foundations: Reciprocity.RamifiedSymbol [0068_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Reciprocity.RamifiedSymbol
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/RamifiedSymbol.lean#L242-L419

import Definitions.Def_PNT_ZeroFree_433_0068_1_1

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


theorem symbol_traceLambda_congr_mod_nine (x y : O)
    (hx : lambda ^ 2 ∣ x-1) (hy : lambda ^ 2 ∣ y-1) (hxy : (9 : O) ∣ x-y) :
    symbol traceLambda x = symbol traceLambda y := by
  rw [symbol_traceLambda_eq_linearRay x hx, symbol_traceLambda_eq_linearRay y hy]
  exact linearRay_congr_mod_nine 0 (-1) x y hx hy hxy

end CubicRamified

namespace CubicJacobiGlobal
open ActualEisensteinCubic CompletedGauss CubicRamified

theorem primary_ne_zero (a : O) (ha : lambda ^ 2 ∣ a-1) : a ≠ 0 := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord a ha
  exact primaryCoord_ne_zero A B

theorem symbol_one_numerator (a : O) (ha : lambda ^ 2 ∣ a-1) : symbol 1 a = 1 := by
  apply idealSymbol_map_one
  rw [primaryGenerator_span a (primary_ne_zero a ha) ha]
  exact primary_ne_zero a ha

theorem symbol_mul_numerator (x y a : O) (ha : lambda ^ 2 ∣ a-1) :
    symbol (x*y) a = symbol x a * symbol y a := by
  apply idealSymbol_map_mul
  rw [primaryGenerator_span a (primary_ne_zero a ha) ha]
  exact primary_ne_zero a ha

theorem symbol_pow_numerator (x a : O) (ha : lambda ^ 2 ∣ a-1) (n : ℕ) :
    symbol (x^n) a = symbol x a ^ n := by
  induction n with
  | zero => simp only [pow_zero, symbol_one_numerator a ha]
  | succ n ih => rw [pow_succ, symbol_mul_numerator _ _ a ha, ih, pow_succ]

theorem symbol_neg_one (a : O) (ha : lambda ^ 2 ∣ a-1) : symbol (-1) a = 1 := by
  have h := symbol_eq_linearRay_of_prime (-1) 0 0 (fun p hp hprimary => by
    let : (Ideal.span {p} : Ideal O).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
      primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
    rw [symbol, idealSymbol_prime _ hg, map_neg, map_one, A3_cubicChar_neg_one]
    simp [linearRay]) a ha
  simpa [linearRay] using h

theorem symbol_neg_numerator (x a : O) (ha : lambda ^ 2 ∣ a-1) :
    symbol (-x) a = symbol x a := by
  rw [neg_eq_neg_one_mul, symbol_mul_numerator _ _ a ha, symbol_neg_one a ha, one_mul]

theorem symbol_isUnit_ne_zero (x a : O) (hx : IsUnit x) (ha : lambda ^ 2 ∣ a-1) :
    symbol x a ≠ 0 := by
  obtain ⟨u,rfl⟩ := hx
  have h : symbol (u : O) a * symbol (↑u⁻¹ : O) a = 1 := by
    rw [← symbol_mul_numerator _ _ a ha, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, symbol_one_numerator a ha]
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

theorem symbol_unit_congr_mod_nine (x a b : O) (hx : IsUnit x)
    (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1) (hab : (9 : O) ∣ a-b) :
    symbol x a = symbol x b := by
  obtain ⟨u,rfl⟩ := hx
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η : O) = omega := rfl
  have hu : u ∈ ([1, -1, η, -η, η^2, -η^2] : List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  have hω : symbol omega a = symbol omega b := by
    rw [symbol_omega_eq_linearRay a ha, symbol_omega_eq_linearRay b hb]
    exact linearRay_congr_mod_nine 2 (-1) a b ha hb hab
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with h | h | h | h | h | h
  · simp only [h, Units.val_one, symbol_one_numerator _ ha, symbol_one_numerator _ hb]
  · simp only [h, Units.val_neg, Units.val_one, symbol_neg_one _ ha, symbol_neg_one _ hb]
  · simpa only [h, hη] using hω
  · simpa only [h, Units.val_neg, hη, symbol_neg_numerator _ _ ha,
      symbol_neg_numerator _ _ hb] using hω
  · simpa only [h, Units.val_pow_eq_pow_val, hη, symbol_pow_numerator _ _ ha,
      symbol_pow_numerator _ _ hb] using congrArg (fun t : O => t^2) hω
  · simpa only [h, Units.val_neg, Units.val_pow_eq_pow_val, hη,
      symbol_neg_numerator _ _ ha, symbol_neg_numerator _ _ hb,
      symbol_pow_numerator _ _ ha, symbol_pow_numerator _ _ hb]
      using congrArg (fun t : O => t^2) hω

private theorem associated_congr_denominator {x y a b : O} (hxy : Associated x y)
    (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1) (hab : (9 : O) ∣ a-b)
    (hy : symbol y a = symbol y b) : symbol x a = symbol x b := by
  obtain ⟨u,hu⟩ := hxy
  apply mul_right_cancel₀ (symbol_isUnit_ne_zero (u : O) a u.isUnit ha)
  calc
    symbol x a * symbol (u : O) a = symbol y a := by
      rw [← symbol_mul_numerator _ _ a ha, hu]
    _ = symbol y b := hy
    _ = symbol x b * symbol (u : O) b := by rw [← hu, symbol_mul_numerator _ _ b hb]
    _ = symbol x b * symbol (u : O) a := by
      rw [symbol_unit_congr_mod_nine (u : O) b a u.isUnit hb ha (by simpa only [neg_sub] using dvd_neg.mpr hab)]

private theorem ramified_prime : Prime lambda := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'

private theorem symbol_prime_denominator_congr (p a b : O) (hp : Prime p)
    (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1)
    (h9 : (9 : O) ∣ a-b) (hpab : p ∣ a-b) : symbol p a = symbol p b := by
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  by_cases hg : lambda ∉ (Ideal.span {p} : Ideal O)
  · obtain ⟨q,hq,hprimary,-⟩ := cubicJacobi_exists_primary_generator (Ideal.span {p}) hg
    have hpq : Associated p q := Ideal.span_singleton_eq_span_singleton.mp hq
    apply associated_congr_denominator hpq ha hb h9
    have hq0 : q ≠ 0 := (hpq.prime_iff.mp hp).ne_zero
    rw [symbol_reciprocity q a hq0 (primary_ne_zero a ha) hprimary ha,
      symbol_reciprocity q b hq0 (primary_ne_zero b hb) hprimary hb]
    exact symbol_congr (hpq.dvd'.trans hpab)
  · have hdiv : p ∣ lambda := Ideal.mem_span_singleton.mp (not_not.mp hg)
    apply associated_congr_denominator (hp.associated_of_dvd ramified_prime hdiv) ha hb h9
    exact symbol_lambda_congr_mod_nine a b ha hb h9

theorem symbol_denominator_congr (x a b : O)
    (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1)
    (h9 : (9 : O) ∣ a-b) (hx : x ∣ a-b) : symbol x a = symbol x b := by
  induction x using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => have heq : a = b := sub_eq_zero.mp (zero_dvd_iff.mp hx); rw [heq]
  | h₂ u hu => exact symbol_unit_congr_mod_nine u a b hu ha hb h9
  | h₃ x p hx0 hp ih =>
    have hpab : p ∣ a-b := (dvd_mul_right p x).trans hx
    have hxab : x ∣ a-b := (dvd_mul_left x p).trans hx
    rw [symbol_mul_numerator _ _ a ha, symbol_mul_numerator _ _ b hb,
      symbol_prime_denominator_congr p a b hp ha hb h9, ih hxab]
    exact hpab

end CubicJacobiGlobal

namespace PrimaryIdealUnitReindex
open ActualEisensteinCubic ActualEisensteinCoordinates ShortDraftLatticeCount

def unitCoordinates : Finset (ℤ × ℤ) :=
  {(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)}

theorem q_eq_one_iff_unitCoordinates (z : ℤ × ℤ) : q z = 1 ↔ z ∈ unitCoordinates := by
  rcases z with ⟨a, b⟩
  constructor
  · intro h
    have hs := coordinate_squares a b 1 (by norm_num) (le_of_eq h)
    have ha : -1 ≤ a ∧ a ≤ 1 := by constructor <;> nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]
    have hb : -1 ≤ b ∧ b ≤ 1 := by constructor <;> nlinarith [sq_nonneg (b - 1), sq_nonneg (b + 1)]
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    interval_cases a <;> interval_cases b <;> norm_num [q, unitCoordinates] at *
  · intro h
    simp only [unitCoordinates, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h | h | h <;> rw [h] <;> norm_num [q]

theorem unit_coordinate_mem (u : Oˣ) : coords u.val ∈ unitCoordinates := by
  apply (q_eq_one_iff_unitCoordinates _).mp
  have hn := (rational_qNat_eq_one_iff u.val).mpr u.isUnit
  have hz := qO_nonneg u.val
  change (q (coords u.val)).toNat = 1 at hn
  have hi : ((q (coords u.val)).toNat : ℤ) = 1 := by exact_mod_cast hn
  simpa only [Int.toNat_of_nonneg hz] using hi

def unitCoordinateMap (u : Oˣ) : {z : ℤ × ℤ // z ∈ unitCoordinates} :=
  ⟨coords u.val, unit_coordinate_mem u⟩

theorem unitCoordinateMap_bijective : Function.Bijective unitCoordinateMap := by
  constructor
  · intro u v huv
    apply Units.ext
    have hc := congrArg Subtype.val huv
    have he := congrArg (fun z : ℤ × ℤ => eval z.1 z.2) hc
    simpa only [unitCoordinateMap, eval_coords] using he
  · intro z
    have hq := (q_eq_one_iff_unitCoordinates z.val).mpr z.property
    have hu : IsUnit (eval z.val.1 z.val.2) := by
      apply (rational_qNat_eq_one_iff _).mp
      simp only [qNat, coords_eval, hq]
      norm_num
    refine ⟨hu.unit, Subtype.ext ?_⟩
    change coords hu.unit.val = z.val
    rw [hu.unit_spec, coords_eval]


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


