-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0014
-- name    : PNT_ZeroFree_433_0014
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T12:15:23.571867+00:00
-- url     : https://prove2.me/theorems/0e0c9a84-f0f5-4706-9b37-90a8a42d4246
-- title:
--   Zero-free region foundations: Arithmetic.LatticeCount [0014]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Arithmetic.LatticeCount
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Arithmetic/LatticeCount.lean#L20-L565

import Definitions.Def_PNT_ZeroFree_433_0013

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Arithmetic/LatticeCount.lean#L20-L565
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Arithmetic.LatticeCount
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

namespace ShortDraftLatticeCount

def q (x : ℤ × ℤ) : ℤ := x.1 ^ 2 - x.1 * x.2 + x.2 ^ 2

theorem coordinate_squares (a b D : ℤ) (hD : 0 ≤ D)
    (h : a ^ 2 - a * b + b ^ 2 ≤ D) :
    a ^ 2 ≤ 2 * D ∧ b ^ 2 ≤ 2 * D := by
  constructor <;> nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (2 * a - b)]

theorem finite_lattice_count (S : Finset (ℤ × ℤ)) (D R : ℕ)
    (hR : 2 * D < R ^ 2)
    (hS : ∀ x ∈ S, q x ≤ D) :
    S.card ≤ (2 * R + 1) ^ 2 := by
  let I : Finset ℤ := Finset.Icc (-(R : ℤ)) (R : ℤ)
  have hbox : S ⊆ I.product I := by
    intro x hx
    rcases x with ⟨a, b⟩
    have hD : (0 : ℤ) ≤ D := by positivity
    obtain ⟨ha, hb⟩ := coordinate_squares a b D hD (hS (a, b) hx)
    have hR' : 2 * (D : ℤ) < (R : ℤ) ^ 2 := by exact_mod_cast hR
    have hRnonneg : (0 : ℤ) ≤ R := by positivity
    apply Finset.mem_product.mpr
    constructor <;> simp only [I, Finset.mem_Icc] <;> constructor <;>
      nlinarith [sq_nonneg (a - R),
      sq_nonneg (a + R), sq_nonneg (b - R), sq_nonneg (b + R)]
  have hI : I.card = 2 * R + 1 := by
    dsimp [I]
    rw [Int.card_Icc]
    have hcast : (R : ℤ) + 1 + (R : ℤ) = ((R + 1 + R : ℕ) : ℤ) := by
      push_cast
      ring
    rw [sub_neg_eq_add, hcast, Int.toNat_natCast]
    ring
  calc
    S.card ≤ (I.product I).card := Finset.card_le_card hbox
    _ = I.card * I.card := Finset.card_product _ _
    _ = (2 * R + 1) ^ 2 := by rw [hI]; ring

theorem finite_lattice_count_linear (S : Finset (ℤ × ℤ)) (D : ℕ)
    (hS : ∀ x ∈ S, q x ≤ D) :
    S.card ≤ 64 * (D + 1) := by
  have hR : 2 * D < (Nat.sqrt (2 * D) + 1) ^ 2 := by
    exact Nat.lt_succ_sqrt' _
  have hcount := finite_lattice_count S D (Nat.sqrt (2 * D) + 1) hR hS
  have hsquare : (Nat.sqrt (2 * D)) ^ 2 ≤ 2 * D := Nat.sqrt_le' _
  have hroot : Nat.sqrt (2 * D) ≤ 2 * D := Nat.sqrt_le_self _
  nlinarith

theorem actual_eisenstein_count
    (S : Finset ActualEisensteinCoordinates.O) (D : ℕ)
    (hS : ∀ x ∈ S, q (ActualEisensteinCoordinates.coords x) ≤ D) :
    S.card ≤ 64 * (D + 1) := by
  have hinj : Function.Injective ActualEisensteinCoordinates.coords := by
    intro x y hxy
    calc
      x = ActualEisensteinCoordinates.eval
          (ActualEisensteinCoordinates.coords x).1
          (ActualEisensteinCoordinates.coords x).2 :=
        (ActualEisensteinCoordinates.eval_coords x).symm
      _ = ActualEisensteinCoordinates.eval
          (ActualEisensteinCoordinates.coords y).1
          (ActualEisensteinCoordinates.coords y).2 := by rw [hxy]
      _ = y := ActualEisensteinCoordinates.eval_coords y
  have himage : (S.image ActualEisensteinCoordinates.coords).card = S.card :=
    Finset.card_image_of_injective S hinj
  have hbound : ∀ v ∈ S.image ActualEisensteinCoordinates.coords,
      q v ≤ D := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact hS x hx
  calc
    S.card = (S.image ActualEisensteinCoordinates.coords).card := himage.symm
    _ ≤ 64 * (D + 1) := finite_lattice_count_linear _ D hbound

end ShortDraftLatticeCount

namespace ActualEisensteinCubic

open ShortDraftCusp

theorem A3_cubicChar_neg_one
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) :
    cubicChar P hgood (-1 : O ⧸ P) = 1 := by
  let χ := cubicChar P hgood
  have hcube : χ (-1 : O ⧸ P) ^ 3 = 1 := by
    rw [← χ.pow_apply' (by decide), cubicChar_pow_three P hgood]
    exact MulChar.one_apply isUnit_neg_one
  have hminus : (-1 : O ⧸ P) ^ 3 = -1 := by ring
  calc
    χ (-1 : O ⧸ P) = χ ((-1 : O ⧸ P) ^ 3) := by rw [hminus]
    _ = χ (-1 : O ⧸ P) ^ 3 := by rw [map_pow]
    _ = 1 := hcube

theorem A3_ramified_local_character
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (a b c d u : O) (hdet : a * d - b * c = 1)
    (hA : a - u * b ∈ P) :
    cubicChar P hgood (Ideal.Quotient.mk P a) *
      cubicChar P hgood (Ideal.Quotient.mk P (c - u * d)) =
      cubicChar P hgood (Ideal.Quotient.mk P (-u)) := by
  have hA0 : Ideal.Quotient.mk P (a - u * b) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hA
  have hrel := congrArg (Ideal.Quotient.mk P)
    (A3_ramified_det_relation a b c d u hdet)
  simp only [map_sub, map_mul, map_neg, hA0, mul_zero, sub_zero] at hrel
  have hh := congrArg (cubicChar P hgood) hrel
  simpa only [map_mul, map_sub, map_neg] using hh

theorem A3_ramified_reciprocity_local_character
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (a b cprime d u : O)
    (hdet : a * d - b * (u * cprime) = 1)
    (ha : a ∈ P) :
    cubicChar P hgood (Ideal.Quotient.mk P (a - u * b)) *
      cubicChar P hgood (Ideal.Quotient.mk P cprime) = 1 := by
  have ha0 : Ideal.Quotient.mk P a = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr ha
  have hrel := congrArg (Ideal.Quotient.mk P)
    (A3_ramified_reciprocity_congr a b cprime d u hdet)
  simp only [map_sub, map_mul, map_add, map_one, ha0, zero_mul,
    add_zero] at hrel
  have hh := congrArg (cubicChar P hgood) hrel
  simpa only [map_mul, map_sub, map_one, ha0, zero_sub, add_zero] using hh

theorem A3_unramified_local_character
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (a b c d : O) (hdet : a * d - b * c = 1)
    (hb : -b ∈ P) :
    cubicChar P hgood (Ideal.Quotient.mk P a) *
      cubicChar P hgood (Ideal.Quotient.mk P d) = 1 := by
  have hb0 : Ideal.Quotient.mk P (-b) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hb
  have hrel := congrArg (Ideal.Quotient.mk P)
    (A3_unramified_inverse_congr a b c d hdet)
  simp only [map_mul, map_add, map_one] at hrel
  have hbb : Ideal.Quotient.mk P b = 0 := by
    have h := congrArg Neg.neg hb0
    simpa only [map_neg, neg_zero, neg_neg] using h
  simp only [hbb, zero_mul, add_zero] at hrel
  have hh := congrArg (cubicChar P hgood) hrel
  simpa only [map_mul, map_one] using hh

end ActualEisensteinCubic

namespace ShortDraftCusp

variable {R : Type*} [CommRing R]

theorem A3_coprime_a_c (a b c d : R)
    (hdet : a * d - b * c = 1) : IsCoprime a c := by
  refine ⟨d, -b, ?_⟩
  linear_combination hdet

theorem A3_coprime_a_b (a b c d : R)
    (hdet : a * d - b * c = 1) : IsCoprime a b := by
  refine ⟨d, -c, ?_⟩
  linear_combination hdet

theorem A3_ramified_coprime_a_A (a b cprime d u : R)
    (hdet : a * d - b * (u * cprime) = 1) :
    IsCoprime a (a - u * b) := by
  refine ⟨d - cprime, cprime, ?_⟩
  linear_combination hdet

theorem A3_unramified_coprime_a_minus_b (a b c d : R)
    (hdet : a * d - b * c = 1) : IsCoprime a (-b) := by
  refine ⟨d, c, ?_⟩
  linear_combination hdet

end ShortDraftCusp

namespace ShortDraftLatticeCount

open ActualEisensteinCoordinates

theorem coords_eval (a b : ℤ) :
    coords (eval a b) = (a, b) := by
  have h := unique_coordinates (eval_coords (eval a b))
  exact Prod.ext h.1 h.2

theorem qO_mul (x y : O) :
    q (coords (x * y)) = q (coords x) * q (coords y) := by
  have hxy : x * y = eval
      ((coords x).1 * (coords y).1 - (coords x).2 * (coords y).2)
      ((coords x).1 * (coords y).2 + (coords x).2 * (coords y).1 -
        (coords x).2 * (coords y).2) := by
    calc
      x * y = eval (coords x).1 (coords x).2 *
          eval (coords y).1 (coords y).2 := by rw [eval_coords, eval_coords]
      _ = _ := eval_mul _ _ _ _
  rw [hxy, coords_eval]
  exact ShortDraft.eisenstein_norm_mul (coords x) (coords y)

theorem qO_nonneg (x : O) : 0 ≤ q (coords x) := by
  exact ShortDraft.eisenstein_norm_nonneg (coords x)

theorem qO_pos {x : O} (hx : x ≠ 0) : 0 < q (coords x) := by
  have hne : q (coords x) ≠ 0 := by
    intro hzero
    have hc : coords x = (0, 0) :=
      (ShortDraft.eisenstein_norm_eq_zero_iff (coords x)).mp hzero
    apply hx
    calc
      x = eval (coords x).1 (coords x).2 := (eval_coords x).symm
      _ = 0 := by simp [hc, eval]
  exact lt_of_le_of_ne (qO_nonneg x) (Ne.symm hne)

def qNat (x : O) : ℕ := (q (coords x)).toNat

theorem qNat_mul (x y : O) : qNat (x * y) = qNat x * qNat y := by
  unfold qNat
  rw [qO_mul]
  exact Int.toNat_mul (qO_nonneg x) (qO_nonneg y)

theorem qNat_pos {x : O} (hx : x ≠ 0) : 0 < qNat x := by
  unfold qNat
  have hcast := Int.toNat_of_nonneg (qO_nonneg x)
  have hpos := qO_pos hx
  omega

theorem finite_multiples_count
    (p : O) (hp : p ≠ 0) (T : Finset O) (D : ℕ)
    (hT : ∀ x ∈ T, qNat (p * x) ≤ D) :
    T.card ≤ 64 * (D / qNat p + 1) := by
  have hbound : ∀ x ∈ T, q (coords x) ≤ (D / qNat p : ℕ) := by
    intro x hx
    have hmul := hT x hx
    rw [qNat_mul] at hmul
    have hdiv : qNat x ≤ D / qNat p :=
      (Nat.le_div_iff_mul_le (qNat_pos hp)).mpr (by
        simpa [mul_comm] using hmul)
    have hnat : qNat x = (q (coords x)) :=
      Int.toNat_of_nonneg (qO_nonneg x)
    have hdiv' : (qNat x : ℤ) ≤ (D / qNat p : ℕ) := by
      exact_mod_cast hdiv
    simpa only [hnat] using hdiv'
  exact actual_eisenstein_count T (D / qNat p) hbound

end ShortDraftLatticeCount

namespace AnalyticBridge

private def CRTChoice.childPair (q : CRTChoice) : ℕ × ℕ :=
  (q.d * q.e * q.kpp, q.J * q.C * q.e * q.v)

theorem second_passage_weighted_fiber
    (Q : Finset CRTChoice) (F K b0 : ℕ)
    (hF : F ≠ 0) (hK : K ≠ 0) (hb0 : b0 ≠ 0)
    (hQ : ∀ q ∈ Q,
      q.J * q.C * q.e * q.v = F ∧
      q.J = q.s * q.J2 ∧
      q.b1 * q.b2 = b0 ^ 2 * q.J2 ^ 2 * q.s ∧
      q.A1 ∣ q.b1 * q.b2 ∧ q.A2 ∣ q.b1 * q.b2 ∧
      q.d ∣ F * b0 ∧ q.d * q.e * q.kpp = K)
    (w : CRTChoice → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hw : ∀ q ∈ Q, w q ≤ M) :
    (∑ q ∈ Q, w q) ≤ M *
      ((F.divisors.card ^ 6 *
        (b0 ^ 2 * F ^ 3).divisors.card ^ 4 *
        (F * b0).divisors.card * K.divisors.card : ℕ) : ℝ) := by
  have hcard := fixed_crt_choice_count Q F K b0 hF hK hb0 hQ
  calc
    (∑ q ∈ Q, w q) ≤ ∑ q ∈ Q, M := by
      apply Finset.sum_le_sum
      intro q hq
      exact hw q hq
    _ = (Q.card : ℝ) * M := by simp
    _ ≤ ((F.divisors.card ^ 6 *
        (b0 ^ 2 * F ^ 3).divisors.card ^ 4 *
        (F * b0).divisors.card * K.divisors.card : ℕ) : ℝ) * M := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM
    _ = _ := by ring

theorem second_passage_positive_reassembly
    (Q : Finset CRTChoice) (T : Finset (ℕ × ℕ)) (b0 : ℕ)
    (hb0 : b0 ≠ 0)
    (w : CRTChoice → ℝ) (A : (ℕ × ℕ) → ℂ)
    (wmax M : ℝ) (hwmax : 0 ≤ wmax)
    (hweight : ∀ q ∈ Q, w q ≤ wmax)
    (hvalid : ∀ q ∈ Q,
      q.J = q.s * q.J2 ∧
      q.b1 * q.b2 = b0 ^ 2 * q.J2 ^ 2 * q.s ∧
      q.A1 ∣ q.b1 * q.b2 ∧ q.A2 ∣ q.b1 * q.b2 ∧
      q.d ∣ (CRTChoice.childPair q).2 * b0)
    (hmap : ∀ q ∈ Q, CRTChoice.childPair q ∈ T)
    (hT : ∀ a ∈ T, a.1 ≠ 0 ∧ a.2 ≠ 0 ∧
      wmax *
        (((a.2.divisors.card ^ 6 *
          (b0 ^ 2 * a.2 ^ 3).divisors.card ^ 4 *
          (a.2 * b0).divisors.card * a.1.divisors.card : ℕ) : ℝ)) ≤ M) :
    (∑ q ∈ Q, w q * ‖A (CRTChoice.childPair q)‖ ^ 2) ≤
      M * (∑ a ∈ T, ‖A a‖ ^ 2) := by
  apply fiber_mass_bound Q T CRTChoice.childPair w A M hmap
  intro a ha
  obtain ⟨hK, hF, hbound⟩ := hT a ha
  let S := Q.filter (fun q => CRTChoice.childPair q = a)
  have hS : ∀ q ∈ S,
      q.J * q.C * q.e * q.v = a.2 ∧
      q.J = q.s * q.J2 ∧
      q.b1 * q.b2 = b0 ^ 2 * q.J2 ^ 2 * q.s ∧
      q.A1 ∣ q.b1 * q.b2 ∧ q.A2 ∣ q.b1 * q.b2 ∧
      q.d ∣ a.2 * b0 ∧ q.d * q.e * q.kpp = a.1 := by
    intro q hq
    have hqQ : q ∈ Q := (Finset.mem_filter.mp hq).1
    have hqa : CRTChoice.childPair q = a := (Finset.mem_filter.mp hq).2
    obtain ⟨hJ, hb, hA1, hA2, hd⟩ := hvalid q hqQ
    have hrow : q.d * q.e * q.kpp = a.1 := congrArg Prod.fst hqa
    have hlabel : q.J * q.C * q.e * q.v = a.2 := congrArg Prod.snd hqa
    simp only [CRTChoice.childPair] at hrow hlabel hd
    rw [hlabel] at hd
    exact ⟨hlabel, hJ, hb, hA1, hA2, hd, hrow⟩
  have hsum := second_passage_weighted_fiber S a.2 a.1 b0
    hF hK hb0 hS w wmax hwmax (by
      intro q hq
      exact hweight q (Finset.mem_filter.mp hq).1)
  exact hsum.trans hbound

end AnalyticBridge

namespace ShortDraftLatticeCount

open ActualEisensteinCoordinates

theorem finite_divisible_count
    (p : O) (hp : p ≠ 0) (S : Finset O) (D : ℕ)
    (hdiv : ∀ n ∈ S, p ∣ n)
    (hnorm : ∀ n ∈ S, qNat n ≤ D) :
    S.card ≤ 64 * (D / qNat p + 1) := by
  classical
  let quotient : (x : {n : O // n ∈ S}) → O :=
    fun x => Classical.choose (hdiv x.1 x.2)
  have hrep : ∀ x : {n : O // n ∈ S}, x.1 = p * quotient x := by
    intro x
    exact Classical.choose_spec (hdiv x.1 x.2)
  have hinj : Function.Injective quotient := by
    intro x y hxy
    apply Subtype.ext
    calc
      x.1 = p * quotient x := hrep x
      _ = p * quotient y := by rw [hxy]
      _ = y.1 := (hrep y).symm
  let T : Finset O := S.attach.image quotient
  have hcard : T.card = S.card := by
    simpa [T] using Finset.card_image_of_injective S.attach hinj
  have hT : ∀ m ∈ T, qNat (p * m) ≤ D := by
    intro m hm
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hm
    rw [← hrep x]
    exact hnorm x.1 x.2
  calc
    S.card = T.card := hcard.symm
    _ ≤ 64 * (D / qNat p + 1) := finite_multiples_count p hp T D hT

end ShortDraftLatticeCount

namespace IdealGaussCRT
open AddChar MulChar

private theorem leftAddChar_mulShift {T R S : Type*}
    [CommRing T] [CommRing R] [CommRing S]
    (e : T ≃+* R × S) (ψ : AddChar T ℂ) (h : T) :
    leftAddChar e (ψ.mulShift h) =
      (leftAddChar e ψ).mulShift (e h).1 := by
  ext z
  change ψ (h * e.symm (z, 0)) = ψ (e.symm ((e h).1 * z, 0))
  congr 1
  apply e.injective
  ext <;> simp

private theorem rightAddChar_mulShift {T R S : Type*}
    [CommRing T] [CommRing R] [CommRing S]
    (e : T ≃+* R × S) (ψ : AddChar T ℂ) (h : T) :
    rightAddChar e (ψ.mulShift h) =
      (rightAddChar e ψ).mulShift (e h).2 := by
  ext z
  change ψ (h * e.symm (0, z)) = ψ (e.symm (0, (e h).2 * z))
  congr 1
  apply e.injective
  ext <;> simp

theorem gauss_transform_crt {T R S : Type*}
    [CommRing T] [Field R] [Field S]
    [Fintype T] [Fintype R] [Fintype S]
    (e : T ≃+* R × S)
    (χR : MulChar R ℂ) (χS : MulChar S ℂ)
    (ψ : AddChar T ℂ) (hχR : χR ≠ 1) (hχS : χS ≠ 1)
    (h : T) :
    (∑ x : T, χR (e x).1 * χS (e x).2 * ψ (h * x)) =
      (if (e h).1 = 0 then 0 else
        (χR (e h).1)⁻¹ * gaussSum χR (leftAddChar e ψ)) *
      (if (e h).2 = 0 then 0 else
        (χS (e h).2)⁻¹ * gaussSum χS (rightAddChar e ψ)) := by
  have hbase := gauss_sum_crt e χR χS (ψ.mulShift h)
  simp only [AddChar.mulShift_apply] at hbase
  rw [leftAddChar_mulShift, rightAddChar_mulShift] at hbase
  have hR := ShortDraftFiniteGaussFourier.gauss_transform χR
    (leftAddChar e ψ) hχR (e h).1
  have hS := ShortDraftFiniteGaussFourier.gauss_transform χS
    (rightAddChar e ψ) hχS (e h).2
  have hR' : gaussSum χR ((leftAddChar e ψ).mulShift (e h).1) =
      (if (e h).1 = 0 then 0 else
        (χR (e h).1)⁻¹ * gaussSum χR (leftAddChar e ψ)) := by
    simpa only [gaussSum, AddChar.mulShift_apply] using hR
  have hS' : gaussSum χS ((rightAddChar e ψ).mulShift (e h).2) =
      (if (e h).2 = 0 then 0 else
        (χS (e h).2)⁻¹ * gaussSum χS (rightAddChar e ψ)) := by
    simpa only [gaussSum, AddChar.mulShift_apply] using hS
  rw [hR', hS'] at hbase
  exact hbase

theorem gauss_transform_ideal_crt {A : Type*} [CommRing A]
    (I J : Ideal A) (hc : IsCoprime I J)
    [I.IsMaximal] [J.IsMaximal]
    [Fintype (A ⧸ I * J)] [Fintype (A ⧸ I)] [Fintype (A ⧸ J)]
    (χI : MulChar (A ⧸ I) ℂ) (χJ : MulChar (A ⧸ J) ℂ)
    (ψ : AddChar (A ⧸ I * J) ℂ)
    (hχI : χI ≠ 1) (hχJ : χJ ≠ 1)
    (h : A ⧸ I * J) :
    (∑ x : A ⧸ I * J,
      χI (Ideal.Quotient.factor (Ideal.mul_le_left : I * J ≤ I) x) *
      χJ (Ideal.Quotient.factor (Ideal.mul_le_right : I * J ≤ J) x) *
      ψ (h * x)) =
      (if Ideal.Quotient.factor (Ideal.mul_le_left : I * J ≤ I) h = 0
        then 0 else
        (χI (Ideal.Quotient.factor (Ideal.mul_le_left : I * J ≤ I) h))⁻¹ *
          gaussSum χI
            (leftAddChar (Ideal.quotientMulEquivQuotientProd I J hc) ψ)) *
      (if Ideal.Quotient.factor (Ideal.mul_le_right : I * J ≤ J) h = 0
        then 0 else
        (χJ (Ideal.Quotient.factor (Ideal.mul_le_right : I * J ≤ J) h))⁻¹ *
          gaussSum χJ
            (rightAddChar (Ideal.quotientMulEquivQuotientProd I J hc) ψ)) := by
  let : Field (A ⧸ I) := Ideal.Quotient.field I
  let : Field (A ⧸ J) := Ideal.Quotient.field J
  let e := Ideal.quotientMulEquivQuotientProd I J hc
  convert! gauss_transform_crt e χI χJ ψ hχI hχJ h using 1 <;>
    simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
      Ideal.quotientMulEquivQuotientProd_snd]

end IdealGaussCRT

namespace ActualEisensteinCubic

section

open ShortDraftLatticeCount

theorem prime_sixth_row_approx
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ) (p : O) (hp : p ≠ 0) (D : ℕ)
    (hfactor : ∀ n ∈ columns,
      (∃ i ∈ support n, p ∈ P i) → p ∣ n)
    (hcolnorm : ∀ n ∈ columns, qNat n ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1) :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p ^ 6))‖ ≤
      (64 * (D / qNat p + 1) : ℕ) := by
  classical
  let S := columns.filter (fun n => ∃ i ∈ support n, p ∈ P i)
  have hdiv : ∀ n ∈ S, p ∣ n := by
    intro n hn
    obtain ⟨hcol, hsupp⟩ := Finset.mem_filter.mp hn
    exact hfactor n hcol hsupp
  have hnorm : ∀ n ∈ S, qNat n ≤ D := by
    intro n hn
    exact hcolnorm n (Finset.mem_filter.mp hn).1
  have hcount := finite_divisible_count p hp S D hdiv hnorm
  calc
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p ^ 6))‖ ≤
        ∑ n ∈ S, ‖weight n‖ :=
      finiteSquarefreeRow_difference_norm P hgood columns support weight p
    _ ≤ ∑ n ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hweight n (Finset.mem_filter.mp hn).1
    _ = (S.card : ℝ) := by simp
    _ ≤ (64 * (D / qNat p + 1) : ℕ) := by exact_mod_cast hcount

end

theorem prime_sixth_row_approx_maximal
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ) (p : O) (hp : p ≠ 0)
    (hprime : (Ideal.span {p} : Ideal O).IsMaximal)
    (D : ℕ)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hcolnorm : ∀ n ∈ columns, ShortDraftLatticeCount.qNat n ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1) :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p ^ 6))‖ ≤
      (64 * (D / ShortDraftLatticeCount.qNat p + 1) : ℕ) := by
  apply prime_sixth_row_approx P hgood columns support weight p hp D
    ?_ hcolnorm hweight
  intro n hn ⟨i, hi, hpi⟩
  have hle : (Ideal.span {p} : Ideal O) ≤ P i :=
    (Ideal.span_singleton_le_iff_mem (P i)).mpr hpi
  have hne : P i ≠ ⊤ := (inferInstance : (P i).IsMaximal).ne_top
  have heq : (Ideal.span {p} : Ideal O) = P i := hprime.eq_of_le hne hle
  have hnP : n ∈ Ideal.span {p} := by
    rw [heq]
    exact hsupport n hn i hi
  exact Ideal.mem_span_singleton.mp hnP

open AddChar MulChar

theorem canonical_two_prime_gauss_transform
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hc : IsCoprime P Q)
    [Fintype (O ⧸ P * Q)] [Fintype (O ⧸ P)] [Fintype (O ⧸ Q)]
    (hgoodP : lambda ∉ P) (hgoodQ : lambda ∉ Q)
    (hcharP : ringChar (O ⧸ P) ≠ 2)
    (hcharQ : ringChar (O ⧸ Q) ≠ 2)
    (j k : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6)
    (hk0 : k ≠ 0) (hk6 : k < 6)
    (ψ : AddChar (O ⧸ P * Q) ℂ) (h : O ⧸ P * Q) :
    (∑ x : O ⧸ P * Q,
      (canonicalSextic P hgoodP ^ j)
          (Ideal.Quotient.factor (Ideal.mul_le_left : P * Q ≤ P) x) *
      (canonicalSextic Q hgoodQ ^ k)
          (Ideal.Quotient.factor (Ideal.mul_le_right : P * Q ≤ Q) x) *
      ψ (h * x)) =
      (if Ideal.Quotient.factor (Ideal.mul_le_left : P * Q ≤ P) h = 0
        then 0 else
        ((canonicalSextic P hgoodP ^ j)
          (Ideal.Quotient.factor (Ideal.mul_le_left : P * Q ≤ P) h))⁻¹ *
          gaussSum (canonicalSextic P hgoodP ^ j)
            (IdealGaussCRT.leftAddChar
              (Ideal.quotientMulEquivQuotientProd P Q hc) ψ)) *
      (if Ideal.Quotient.factor (Ideal.mul_le_right : P * Q ≤ Q) h = 0
        then 0 else
        ((canonicalSextic Q hgoodQ ^ k)
          (Ideal.Quotient.factor (Ideal.mul_le_right : P * Q ≤ Q) h))⁻¹ *
          gaussSum (canonicalSextic Q hgoodQ ^ k)
            (IdealGaussCRT.rightAddChar
              (Ideal.quotientMulEquivQuotientProd P Q hc) ψ)) := by
  exact IdealGaussCRT.gauss_transform_ideal_crt P Q hc
    (canonicalSextic P hgoodP ^ j)
    (canonicalSextic Q hgoodQ ^ k) ψ
    (canonicalSextic_pow_ne_one P hgoodP hcharP hj0 hj6)
    (canonicalSextic_pow_ne_one Q hgoodQ hcharQ hk0 hk6) h

end ActualEisensteinCubic

end

end OAI

end


