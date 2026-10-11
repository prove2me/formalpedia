-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0067
-- name    : PNT_ZeroFree_433_0067
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T15:05:40.783477+00:00
-- url     : https://prove2.me/theorems/f16651eb-9cb2-4b45-9e5f-04ffbb552123
-- title:
--   Zero-free region foundations: Reciprocity.CubicJacobi [0067]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Reciprocity.CubicJacobi
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/CubicJacobi.lean#L75-L763

import Definitions.Def_PNT_ZeroFree_433_0048

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/CubicJacobi.lean#L75-L763
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Reciprocity.CubicJacobi
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

namespace CubicJacobiGlobal
abbrev O := ActualEisensteinCubic.O
abbrev K := ActualEisensteinCubic.K
open ActualEisensteinCubic CompletedGauss

def primeValue (P : Ideal O) (x : O) : O :=
  if h : P.IsMaximal ∧ lambda ∉ P then
    letI : P.IsMaximal := h.1
    cubicChar P h.2 (Ideal.Quotient.mk P x)
  else 0

@[simp] theorem primeValue_eq (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (x : O) :
    primeValue P x = cubicChar P hgood (Ideal.Quotient.mk P x) := by
  simp only [primeValue, dif_pos (show P.IsMaximal ∧ lambda ∉ P from
    ⟨inferInstance, hgood⟩)]

def idealSymbol (I : Ideal O) (x : O) : O :=
  if I = 0 then 0 else
    ((UniqueFactorizationMonoid.normalizedFactors I).map (fun P => primeValue P x)).prod

@[simp] theorem idealSymbol_zero (x : O) : idealSymbol 0 x = 0 := by simp [idealSymbol]
@[simp] theorem idealSymbol_bot (x : O) : idealSymbol ⊥ x = 0 := idealSymbol_zero x
@[simp] theorem idealSymbol_one (x : O) : idealSymbol 1 x = 1 := by
  rw [idealSymbol, if_neg one_ne_zero, UniqueFactorizationMonoid.normalizedFactors_one]
  rfl
@[simp] theorem idealSymbol_top (x : O) : idealSymbol ⊤ x = 1 := by
  simpa only [Ideal.one_eq_top] using idealSymbol_one x

theorem idealSymbol_mul (I J : Ideal O) (x : O) :
    idealSymbol (I * J) x = idealSymbol I x * idealSymbol J x := by
  classical
  by_cases hI : I = 0
  · simp [hI]
  by_cases hJ : J = 0
  · simp [hJ]
  simp only [idealSymbol, if_neg hI, if_neg hJ, if_neg (mul_ne_zero hI hJ),
    UniqueFactorizationMonoid.normalizedFactors_mul hI hJ, Multiset.map_add,
    Multiset.prod_add]

def symbol (x y : O) : O := idealSymbol (Ideal.span {y}) x

@[simp] theorem symbol_one (x : O) : symbol x 1 = 1 := by simp [symbol]
@[simp] theorem symbol_zero (x : O) : symbol x 0 = 0 := by simp [symbol]

theorem symbol_mul_denominator (x y z : O) :
    symbol x (y * z) = symbol x y * symbol x z := by
  rw [symbol, ← Ideal.span_singleton_mul_span_singleton, idealSymbol_mul]
  rfl

theorem idealSymbol_prime (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) (x : O) :
    idealSymbol P x = cubicChar P hgood (Ideal.Quotient.mk P x) := by
  have hP0 : P ≠ 0 := NeZero.ne _
  have hp : Prime P := Ideal.prime_of_isPrime hP0 (inferInstance : P.IsPrime)
  rw [idealSymbol, if_neg hP0,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hp.irreducible]
  simpa using primeValue_eq P hgood x

private theorem factor_good (I : Ideal O) (hI : primaryGenerator I ≠ 0)
    (P : Ideal O) (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    P.IsMaximal ∧ lambda ∉ P := by
  exact ⟨(primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI hP)).1,
    (primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI hP)).2.1⟩

theorem idealSymbol_map_mul (I : Ideal O) (hI : primaryGenerator I ≠ 0) (x y : O) :
    idealSymbol I (x * y) = idealSymbol I x * idealSymbol I y := by
  have hI0 := primaryGenerator_ne_zero_ideal I hI
  simp only [idealSymbol, if_neg hI0]
  rw [← Multiset.prod_map_mul]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  have hg := factor_good I hI P hP
  let : P.IsMaximal := hg.1
  simp only [primeValue_eq P hg.2, map_mul]

theorem idealSymbol_map_one (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    idealSymbol I 1 = 1 := by
  have hI0 := primaryGenerator_ne_zero_ideal I hI
  rw [idealSymbol, if_neg hI0]
  apply Multiset.prod_eq_one
  intro y hy
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hy
  have hg := factor_good I hI P hP
  let : P.IsMaximal := hg.1
  simp only [primeValue_eq P hg.2, map_one]

theorem idealSymbol_map_multiset_prod (I : Ideal O) (hI : primaryGenerator I ≠ 0)
    (s : Multiset O) :
    idealSymbol I s.prod = (s.map (idealSymbol I)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [idealSymbol_map_one I hI]
  | @cons a s ih => simp [idealSymbol_map_mul I hI, ih]

theorem symbol_prime (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1) (x : O) :
    symbol x p = primeValue (Ideal.span {p}) x := by
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  rw [symbol, idealSymbol_prime _ hg, primeValue_eq _ hg]

theorem idealSymbol_reciprocity (I J : Ideal O)
    (hI : primaryGenerator I ≠ 0) (hJ : primaryGenerator J ≠ 0) :
    idealSymbol I (primaryGenerator J) = idealSymbol J (primaryGenerator I) := by
  classical
  have hI0 := primaryGenerator_ne_zero_ideal I hI
  have hJ0 := primaryGenerator_ne_zero_ideal J hJ
  rw [primaryGenerator, if_neg hJ0, idealSymbol_map_multiset_prod I hI,
    primaryGenerator, if_neg hI0, idealSymbol_map_multiset_prod J hJ]
  simp only [Multiset.map_map, Function.comp_def, idealSymbol, if_neg hI0, if_neg hJ0]
  rw [Multiset.prod_map_prod_map]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro Q hQ
  have hgP := factor_good I hI P hP
  have hgQ := factor_good J hJ Q hQ
  let : P.IsMaximal := hgP.1
  let : Q.IsMaximal := hgQ.1
  have hp := (primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI hP)).2.2
  have hq := (primaryPrime_spec Q (primaryPrime_factor_ne_zero J Q hJ hQ)).2.2
  rw [primeValue_eq P hgP.2, primeValue_eq Q hgQ.2]
  exact cubic_reciprocity_primary P Q hgP.2 hgQ.2
    (primaryPrime P) (primaryPrime Q) hp.1.symm hq.1.symm hp.2 hq.2

theorem symbol_reciprocity (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hap : lambda ^ 2 ∣ a - 1) (hbp : lambda ^ 2 ∣ b - 1) :
    symbol a b = symbol b a := by
  have haG := primaryGenerator_span a ha hap
  have hbG := primaryGenerator_span b hb hbp
  have h := idealSymbol_reciprocity (Ideal.span {b}) (Ideal.span {a})
    (by rwa [hbG]) (by rwa [haG])
  simpa only [symbol, haG, hbG] using h

theorem idealSymbol_congr (I : Ideal O) {x y : O} (hxy : x - y ∈ I) :
    idealSymbol I x = idealSymbol I y := by
  classical
  by_cases hI : I = 0
  · simp only [hI, idealSymbol_zero]
  simp only [idealSymbol, if_neg hI]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  have hle := ((Ideal.mem_normalizedFactors_iff hI).mp hP).2
  by_cases hg : P.IsMaximal ∧ lambda ∉ P
  · let : P.IsMaximal := hg.1
    rw [primeValue_eq P hg.2, primeValue_eq P hg.2,
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (hle hxy)]
  · simp only [primeValue, dif_neg hg]

theorem symbol_congr {x y d : O} (hxy : d ∣ x - y) :
    symbol x d = symbol y d :=
  idealSymbol_congr _ (Ideal.mem_span_singleton.mpr hxy)

end CubicJacobiGlobal

namespace CubicRamified

abbrev O := ActualEisensteinCubic.O
abbrev K := ActualEisensteinCubic.K
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss

lemma lambda_def : lambda = omega - 1 := rfl

theorem cubicValue_cube (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (x : O) (hx : x ∉ P) :
    (cubicChar P hg (Ideal.Quotient.mk P x)) ^ 3 = 1 := by
  rw [← MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), cubicChar_pow_three]
  exact MulChar.one_apply (isUnit_iff_ne_zero.mpr
    (Ideal.Quotient.eq_zero_iff_mem.not.mpr hx))

theorem cubicValue_ne_zero (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (x : O) (hx : x ∉ P) :
    cubicChar P hg (Ideal.Quotient.mk P x) ≠ 0 := by
  have h := cubicValue_cube P hg x hx
  intro hz
  rw [hz, zero_pow (by decide)] at h
  exact zero_ne_one h

theorem ramified_comparison
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hgP : lambda ∉ P) (hgQ : lambda ∉ Q)
    (p q u r : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hp : lambda ^ 2 ∣ p - 1) (hq : lambda ^ 2 ∣ q - 1)
    (hqP : q ∉ P) (_hpQ : p ∉ Q)
    (hr0 : r ≠ 0) (hr : lambda ^ 2 ∣ r - 1)
    (hfactor : p - q = lambda ^ 2 * u * r) :
    (cubicChar P hgP (Ideal.Quotient.mk P lambda)) ^ 2 *
        cubicChar P hgP (Ideal.Quotient.mk P u) =
      (cubicChar Q hgQ (Ideal.Quotient.mk Q lambda)) ^ 2 *
        cubicChar Q hgQ (Ideal.Quotient.mk Q u) := by
  have hp0 : p ≠ 0 := by
    intro hz
    apply (NeZero.ne P)
    simp [hP, hz]
  have hq0 : q ≠ 0 := by
    intro hz
    apply (NeZero.ne Q)
    simp [hQ, hz]
  have hpP : p ∈ P := by rw [hP]; exact Ideal.subset_span (by simp)
  have hqQ : q ∈ Q := by rw [hQ]; exact Ideal.subset_span (by simp)
  have hrP : r ∉ P := by
    intro hrP
    have hd : p - q ∈ P := by rw [hfactor]; exact P.mul_mem_left _ hrP
    have hmem := P.sub_mem hpP hd
    exact hqP (by convert! hmem using 1 ; ring)
  have hrr : cubicChar P hgP (Ideal.Quotient.mk P r) =
      cubicChar Q hgQ (Ideal.Quotient.mk Q r) := by
    have heq : symbol p r = symbol q r := symbol_congr
      (by rw [hfactor]; exact dvd_mul_left r _)
    have h := (symbol_reciprocity r p hr0 hp0 hr hp).trans
      (heq.trans (symbol_reciprocity q r hq0 hr0 hq hr))
    simpa only [symbol, ← hP, ← hQ, idealSymbol_prime _ hgP,
      idealSymbol_prime _ hgQ] using h
  have heq : cubicChar P hgP (Ideal.Quotient.mk P (p - q)) =
      cubicChar Q hgQ (Ideal.Quotient.mk Q (p - q)) := by
    rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hpP, zero_sub,
      neg_eq_neg_one_mul, map_mul, A3_cubicChar_neg_one P hgP, one_mul,
      map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hqQ, sub_zero]
    exact cubic_reciprocity_primary P Q hgP hgQ p q hP hQ hp hq
  simp only [hfactor, map_mul, map_pow] at heq
  rw [← hrr] at heq
  exact mul_right_cancel₀ (cubicValue_ne_zero P hgP r hrP) heq

def sevenPrime : O := 1 + 3 * omega
def sevenIdeal : Ideal O := Ideal.span {sevenPrime}

theorem sevenPrime_norm : ShortDraftLatticeCount.qNat sevenPrime = 7 := by
  change ShortDraftLatticeCount.qNat (ActualEisensteinCoordinates.eval 1 3) = 7
  unfold ShortDraftLatticeCount.qNat
  rw [ShortDraftLatticeCount.coords_eval]
  norm_num [ShortDraftLatticeCount.q] <;> decide

theorem sevenPrime_ne_zero : sevenPrime ≠ 0 := by
  intro hz
  change ActualEisensteinCoordinates.eval 1 3 = 0 at hz
  have hh : ActualEisensteinCoordinates.eval 1 3 =
      ActualEisensteinCoordinates.eval 0 0 :=
    hz.trans (by simp [ActualEisensteinCoordinates.eval])
  have h := (ActualEisensteinCoordinates.unique_coordinates hh).1
  norm_num at h

theorem sevenIdeal_norm : Ideal.absNorm sevenIdeal = 7 := by
  rw [sevenIdeal, ← qNat_eq_absNorm_span, sevenPrime_norm]

instance sevenIdeal_isMaximal : sevenIdeal.IsMaximal := by
  have hp : sevenIdeal.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by
    rw [sevenIdeal_norm, Nat.irreducible_iff_nat_prime]
    decide)
  exact hp.isMaximal (Ideal.span_singleton_eq_bot.not.mpr sevenPrime_ne_zero)

theorem sevenPrime_primary : lambda ^ 2 ∣ sevenPrime - 1 := by
  refine ⟨-1, ?_⟩
  rw [lambda_def]
  dsimp [sevenPrime]
  linear_combination omega_sq_for_norm

theorem sevenIdeal_good : lambda ∉ sevenIdeal :=
  primary_maximal_divisor_good sevenPrime sevenPrime_primary sevenIdeal
    (Ideal.subset_span (by simp []))

theorem twoIdeal_card : Nat.card (O ⧸ cubicTwoIdeal) = 4 := by
  change Ideal.absNorm cubicTwoIdeal = 4
  rw [cubicTwoIdeal, ← qNat_eq_absNorm_span]
  rw [show (-2 : O) = ActualEisensteinCoordinates.eval (-2) 0 by
    simp [ActualEisensteinCoordinates.eval]]
  unfold ShortDraftLatticeCount.qNat
  rw [ShortDraftLatticeCount.coords_eval]
  norm_num [ShortDraftLatticeCount.q] <;> decide

theorem sevenIdeal_card : Nat.card (O ⧸ sevenIdeal) = 7 := sevenIdeal_norm

theorem cubicValue_lambda_two :
    cubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal lambda) =
      omega ^ 2 := by
  have heq : Ideal.Quotient.mk cubicTwoIdeal lambda =
      Ideal.Quotient.mk cubicTwoIdeal (omega ^ 2) := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    rw [cubicTwoIdeal, Ideal.mem_span_singleton]
    refine ⟨-omega, ?_⟩
    rw [lambda_def]
    linear_combination -omega_sq_for_norm
  rw [heq, map_pow, map_pow, cubicChar_omega, twoIdeal_card]
  norm_num

theorem cubicValue_lambda_seven :
    cubicChar sevenIdeal sevenIdeal_good (Ideal.Quotient.mk sevenIdeal lambda) = 1 := by
  apply cubic_roots_reduce_injective sevenIdeal sevenIdeal_good
    (cubicValue_cube sevenIdeal sevenIdeal_good lambda sevenIdeal_good) (by simp)
  rw [cubicChar_reduce, sevenIdeal_card]
  norm_num only [Nat.reduceSub, Nat.reduceDiv]
  rw [← map_pow]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [sevenIdeal, Ideal.mem_span_singleton]
  refine ⟨-1, ?_⟩
  rw [lambda_def]
  dsimp [sevenPrime]
  linear_combination omega_sq_for_norm

open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss

def primaryCoord (A B : ℤ) : O := ActualEisensteinCoordinates.eval (1 + 3 * A) (3 * B)

theorem primaryCoord_eq (A B : ℤ) :
    primaryCoord A B = 1 + 3 * (A : O) + 3 * (B : O) * omega := by
  simp only [primaryCoord, ActualEisensteinCoordinates.eval]
  push_cast
  rfl

theorem primaryCoord_primary (A B : ℤ) : lambda ^ 2 ∣ primaryCoord A B - 1 := by
  rw [primaryCoord_eq]
  apply lambda_sq_dvd_three.trans
  exact ⟨(A : O) + (B : O) * omega, by ring⟩

theorem primaryCoord_ne_zero (A B : ℤ) : primaryCoord A B ≠ 0 := by
  intro hz
  have hcoord : ActualEisensteinCoordinates.eval (1 + 3 * A) (3 * B) =
      ActualEisensteinCoordinates.eval 0 0 := by
    exact hz.trans (by simp [ActualEisensteinCoordinates.eval])
  have h := (ActualEisensteinCoordinates.unique_coordinates hcoord).1
  omega

lemma primary_card_exponent (N : ℕ) (A B : ℤ) (hN : 1 < N)
    (hn : (N : ℤ) = 1 + 9*(A^2-A*B+B^2)+3*(2*A-B)) :
    ((N-1)/3)%3 = ((2*A-B)%3).toNat %3 := by
  have hsub : ((N-1 : ℕ) : ℤ) = (N : ℤ)-1 := by omega
  have hdiv : (((N-1)/3 : ℕ) : ℤ) = 3*(A^2-A*B+B^2)+(2*A-B) := by
    rw [Int.natCast_ediv, hsub]
    have hh : (N : ℤ)-1 = 3*(3*(A^2-A*B+B^2)+(2*A-B)) := by omega
    rw [hh]
    omega
  have hrem : (((2*A-B)%3).toNat : ℤ) = (2*A-B)%3 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  omega

theorem cubicValue_omega_primary (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (A B : ℤ) (hP : P = Ideal.span {primaryCoord A B}) :
    cubicChar P hg (Ideal.Quotient.mk P omega) =
      omega ^ ((2 * A - B) % 3).toNat := by
  have hn : (Nat.card (O ⧸ P) : ℤ) =
      (1 + 3 * A)^2 - (1 + 3 * A)*(3 * B) + (3 * B)^2 := by
    change (Ideal.absNorm P : ℤ) = _
    rw [hP, ← qNat_eq_absNorm_span]
    unfold ShortDraftLatticeCount.qNat
    rw [Int.toNat_of_nonneg (ShortDraftLatticeCount.qO_nonneg _)]
    rw [primaryCoord, ShortDraftLatticeCount.coords_eval]
    rfl
  have hn' : (Nat.card (O ⧸ P) : ℤ) =
      1 + 9*(A^2 - A*B + B^2) + 3*(2*A-B) := by nlinarith [hn]
  rw [cubicChar_omega]
  apply ((omega_primitive.isOfFinOrder (by decide)).pow_inj_mod).mpr
  rw [← omega_primitive.eq_orderOf]
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hcard : 1 < Nat.card (O ⧸ P) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  exact primary_card_exponent (Nat.card (O ⧸ P)) A B hcard hn'

theorem ramified_comparison_of_factor
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hgP : lambda ∉ P) (hgQ : lambda ∉ Q)
    (p q u r : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hp : lambda ^ 2 ∣ p - 1) (hq : lambda ^ 2 ∣ q - 1)
    (hu : u ≠ 0) (hr0 : r ≠ 0) (hr : lambda ^ 2 ∣ r - 1)
    (hfactor : p - q = lambda ^ 2 * u * r) :
    (cubicChar P hgP (Ideal.Quotient.mk P lambda)) ^ 2 *
        cubicChar P hgP (Ideal.Quotient.mk P u) =
      (cubicChar Q hgQ (Ideal.Quotient.mk Q lambda)) ^ 2 *
        cubicChar Q hgQ (Ideal.Quotient.mk Q u) := by
  have hlam : lambda ≠ 0 := fun hz => hgP (hz ▸ P.zero_mem)
  have hne : P ≠ Q := by
    intro heq
    have hpq : p = q := primary_associated_eq p q
      (Ideal.span_singleton_eq_span_singleton.mp (hP.symm.trans (heq.trans hQ))) hp hq
    have hz : lambda ^ 2 * u * r = 0 := by rw [← hfactor, hpq, sub_self]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hlam) hu) hr0 hz
  exact ramified_comparison P Q hgP hgQ p q u r hP hQ hp hq
    (prime_generator_not_mem_of_ne P Q hne q hQ)
    (prime_generator_not_mem_of_ne Q P hne.symm p hP) hr0 hr hfactor

open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss

lemma omega_ne_zero : omega ≠ 0 := omega_primitive.ne_zero (by decide)
lemma omega_isUnit : IsUnit omega := omega_primitive.isUnit (by decide)
lemma omega_four : omega ^ 4 = omega := by
  calc
    _ = omega ^ 3 * omega := by ring
    _ = omega := by rw [omega_primitive.pow_eq_one, one_mul]
lemma omega_five : omega ^ 5 = omega ^ 2 := by
  calc
    _ = omega ^ 3 * omega ^ 2 := by ring
    _ = _ := by rw [omega_primitive.pow_eq_one, one_mul]

lemma cubicValue_neg (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P) (x : O) :
    cubicChar P hg (Ideal.Quotient.mk P (-x)) =
      cubicChar P hg (Ideal.Quotient.mk P x) := by
  rw [map_neg, neg_eq_neg_one_mul, map_mul, A3_cubicChar_neg_one, one_mul]

lemma cubicValue_omega_two :
    cubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal omega) =
      omega := by rw [cubicChar_omega, twoIdeal_card] ; norm_num
lemma cubicValue_omega_seven :
    cubicChar sevenIdeal sevenIdeal_good (Ideal.Quotient.mk sevenIdeal omega) =
      omega ^ 2 := by rw [cubicChar_omega, sevenIdeal_card]

lemma eq_of_cube_one_of_sq_eq (z w : O) (hz : z ^ 3 = 1)
    (hw : w ^ 3 = 1) (hsq : z ^ 2 = w ^ 2) : z = w := by
  have hw0 : w ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at hw; exact zero_ne_one hw
  apply mul_right_cancel₀ (pow_ne_zero 2 hw0)
  calc
    z * w ^ 2 = z ^ 3 := by rw [← hsq]; ring
    _ = 1 := hz
    _ = w * w ^ 2 := by rw [← hw]; ring

lemma supplement_of_factor
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hgP : lambda ∉ P) (hgQ : lambda ∉ Q)
    (p q u r : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hp : lambda ^ 2 ∣ p - 1) (hq : lambda ^ 2 ∣ q - 1)
    (hu : IsUnit u) (hr0 : r ≠ 0) (hr : lambda ^ 2 ∣ r - 1)
    (hfactor : p - q = lambda ^ 2 * u * r)
    (j : ℕ)
    (hscalar : (cubicChar Q hgQ (Ideal.Quotient.mk Q lambda)) ^ 2 *
        cubicChar Q hgQ (Ideal.Quotient.mk Q u) =
      (omega ^ j)^2 * cubicChar P hgP (Ideal.Quotient.mk P u)) :
    cubicChar P hgP (Ideal.Quotient.mk P lambda) = omega ^ j := by
  apply eq_of_cube_one_of_sq_eq
  · exact cubicValue_cube P hgP lambda hgP
  · rw [← pow_mul, Nat.mul_comm j, pow_mul, omega_primitive.pow_eq_one, one_pow]
  · apply mul_right_cancel₀ (cubicValue_ne_zero P hgP u (Ideal.notMem_of_isUnit P hu))
    exact (ramified_comparison_of_factor P Q hgP hgQ p q u r hP hQ hp hq
      hu.ne_zero hr0 hr hfactor).trans hscalar

lemma omega_six : omega ^ 6 = 1 := by
  calc
    _ = omega ^ 3 * omega ^ 3 := by ring
    _ = 1 := by rw [omega_primitive.pow_eq_one, one_mul]

lemma omega_seven : omega ^ 7 = omega := by
  calc
    _ = omega ^ 3 * omega ^ 4 := by ring
    _ = omega := by rw [omega_primitive.pow_eq_one, one_mul] ; exact omega_four

lemma omega_eight : omega ^ 8 = omega ^ 2 := by
  calc
    _ = omega ^ 3 * omega ^ 5 := by ring
    _ = omega ^ 2 := by rw [omega_primitive.pow_eq_one, one_mul] ; exact omega_five

private theorem supplement_case00 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+0) (3*l+0)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 0 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 0 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+0) (3*l+0)) (-2) (-(omega ^ 2))
    (primaryCoord (k) (l)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 2).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 0 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [omega_five, omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg, map_pow, cubicValue_lambda_two,
      cubicValue_omega_two, hw, pow_zero, ]
    all_goals ring_nf
    all_goals simp only [  omega_six,
      ]

private theorem supplement_case01 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+0) (3*l+1)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 0 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 2 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+0) (3*l+1)) (-2) (omega ^ 1)
    (primaryCoord (l) (-k + l)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 1) (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 0 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [ omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [  cubicValue_lambda_two,
      cubicValue_omega_two, hw, pow_zero, pow_one]
    all_goals ring_nf
    all_goals simp only [   omega_five,
       omega_sq_for_norm]

private theorem supplement_case02 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+0) (3*l+2)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 0 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 1 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P sevenIdeal hg sevenIdeal_good
    (primaryCoord (3*k+0) (3*l+2)) sevenPrime (-(omega ^ 0))
    (primaryCoord (-k + l) (-k)) hP rfl (primaryCoord_primary _ _) sevenPrime_primary
    (omega_isUnit.pow 0).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 0 ?_
  · simp only [primaryCoord_eq, lambda_def, sevenPrime]
    push_cast
    all_goals ring_nf
    all_goals simp only [  omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg,  cubicValue_lambda_seven,
        pow_zero,  map_one]

private theorem supplement_case10 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+1) (3*l+0)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 1 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 2 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+1) (3*l+0)) (-2) (omega ^ 2)
    (primaryCoord (-k - 1) (-l)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 2) (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 1 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [omega_five, omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [ map_pow, cubicValue_lambda_two,
      cubicValue_omega_two, hw,  pow_one]
    all_goals ring_nf

private theorem supplement_case11 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+1) (3*l+1)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 1 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 1 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P sevenIdeal hg sevenIdeal_good
    (primaryCoord (3*k+1) (3*l+1)) sevenPrime (-(omega ^ 2))
    (primaryCoord (k) (l)) hP rfl (primaryCoord_primary _ _) sevenPrime_primary
    (omega_isUnit.pow 2).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 1 ?_
  · simp only [primaryCoord_eq, lambda_def, sevenPrime]
    push_cast
    all_goals ring_nf
    all_goals simp only [omega_five, omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg, map_pow, cubicValue_lambda_seven,
      cubicValue_omega_seven, hw,  pow_one]
    all_goals ring_nf

private theorem supplement_case12 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+1) (3*l+2)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 1 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 0 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+1) (3*l+2)) (-2) (-(omega ^ 1))
    (primaryCoord (-l - 1) (k - l)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 1).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 1 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [ omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg,  cubicValue_lambda_two,
      cubicValue_omega_two, hw, pow_zero, pow_one]
    all_goals ring_nf
    all_goals simp only [   omega_five,
       omega_sq_for_norm]

private theorem supplement_case20 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+2) (3*l+0)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 2 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 1 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P sevenIdeal hg sevenIdeal_good
    (primaryCoord (3*k+2) (3*l+0)) sevenPrime (-(omega ^ 1))
    (primaryCoord (-l) (k - l + 1)) hP rfl (primaryCoord_primary _ _) sevenPrime_primary
    (omega_isUnit.pow 1).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 2 ?_
  · simp only [primaryCoord_eq, lambda_def, sevenPrime]
    push_cast
    all_goals ring_nf
    all_goals simp only [ omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg,  cubicValue_lambda_seven,
      cubicValue_omega_seven, hw,  pow_one]
    all_goals ring_nf
    all_goals simp only [   omega_five,
       omega_sq_for_norm]

private theorem supplement_case21 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+2) (3*l+1)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 2 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 0 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+2) (3*l+1)) (-2) (-(omega ^ 0))
    (primaryCoord (-k + l - 1) (-k - 1)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 0).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 2 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [  omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg,  cubicValue_lambda_two,
        pow_zero,  map_one]

private theorem supplement_case22 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+2) (3*l+2)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 2 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 2 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+2) (3*l+2)) (-2) (omega ^ 0)
    (primaryCoord (k - l) (k + 1)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 0) (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 2 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [  omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [  cubicValue_lambda_two,
        pow_zero,  map_one]

theorem cubicValue_lambda_primary (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (A B : ℤ)
    (hP : P = Ideal.span {primaryCoord A B}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ (A % 3).toNat := by
  have hA : A = 3 * (A / 3) + A % 3 := by omega
  have hB : B = 3 * (B / 3) + B % 3 := by omega
  have hAa : A % 3 = 0 ∨ A % 3 = 1 ∨ A % 3 = 2 := by omega
  have hBb : B % 3 = 0 ∨ B % 3 = 1 ∨ B % 3 = 2 := by omega
  rcases hAa with ha | ha | ha <;> rcases hBb with hb | hb | hb
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+0) (3*(B/3)+0)} := by
      rw [show 3*(A/3)+0 = A by omega, show 3*(B/3)+0 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case00 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+0) (3*(B/3)+1)} := by
      rw [show 3*(A/3)+0 = A by omega, show 3*(B/3)+1 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case01 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+0) (3*(B/3)+2)} := by
      rw [show 3*(A/3)+0 = A by omega, show 3*(B/3)+2 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case02 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+1) (3*(B/3)+0)} := by
      rw [show 3*(A/3)+1 = A by omega, show 3*(B/3)+0 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case10 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+1) (3*(B/3)+1)} := by
      rw [show 3*(A/3)+1 = A by omega, show 3*(B/3)+1 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case11 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+1) (3*(B/3)+2)} := by
      rw [show 3*(A/3)+1 = A by omega, show 3*(B/3)+2 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case12 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+2) (3*(B/3)+0)} := by
      rw [show 3*(A/3)+2 = A by omega, show 3*(B/3)+0 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case20 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+2) (3*(B/3)+1)} := by
      rw [show 3*(A/3)+2 = A by omega, show 3*(B/3)+1 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case21 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+2) (3*(B/3)+2)} := by
      rw [show 3*(A/3)+2 = A by omega, show 3*(B/3)+2 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case22 P hg (A/3) (B/3) hp

end CubicRamified

end

end OAI

end


