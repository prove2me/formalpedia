-- Prove2me | Definitions.Def_Yukon_db9e62887577419e408bc32c
-- name    : Yukon_db9e62887577419e408bc32c
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:53:13.217744+00:00
-- url     : https://prove2.me/theorems/abf75d88-9171-4d78-b563-707dadc11f95
-- title:
--   YukonModule.CompPoly.Fields.KoalaBear.Basic.part0
-- statement:
--   Source module CompPoly.Fields.KoalaBear.Basic. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Fields/KoalaBear/Basic.lean
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Fields/KoalaBear/Basic.lean
--
--   yukon-proof-operation:e0e880e40c0f71fa3d10a9386ed1f147f6e33bdc0e17dd3a5ae5025d6d8fc6c6
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246ZTBlODgwZTQwYzBmNzFmYTNkMTBhOTM4NmVkMWYxNDdmNmUzM2JkYzBlMTdkZDNhNWFlNTAyNWQ2ZDhmYzZjNiIsImhhc2giOiIwOWZmZGY4NTU5ZGMwMGZhYmJlYjAyNzRmMGVjYWNhMTExZDkzOTljODE5Zjg1MWUzMzRlZDQ3Njk2YmQ0YmM5Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9kYjllNjI4ODc1Nzc0MTllNDA4YmMzMmMiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Valerii Huhnin
-/
module

public import Definitions.Def_Yukon_8c83d2b707eab32a485d82e5

public import Definitions.Def_Yukon_0f67411c7366bd630241c9c8

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.FieldTheory.Finite.Basic


public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.Tactic.ReduceModChar
public import Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Polynomial.FieldDivision
meta import Definitions.Def_Yukon_8c83d2b707eab32a485d82e5
meta import Definitions.Def_Yukon_0f67411c7366bd630241c9c8
set_option backward.isDefEq.respectTransparency.types false
/-!
  # KoalaBear Field `2^{31} - 2^{24} + 1`

  This is the field used for lean Ethereum spec.
-/

@[expose] public section

namespace KoalaBear

/-- The KoalaBear field modulus, `2^31 - 2^24 + 1`. -/
@[reducible]
def fieldSize : Nat := 2 ^ 31 - 2 ^ 24 + 1

-- 2130706433
-- #eval fieldSize

/-- The KoalaBear prime field as a `ZMod`. -/
abbrev Field := ZMod fieldSize

/-- The KoalaBear modulus is prime. -/
theorem is_prime : Nat.Prime fieldSize := by
  unfold fieldSize
  refine PrattCertificate.out ⟨3, by reduce_mod_char, ?_⟩
  refine .split (2 ^ 24) 127 ?_ ?_ (by norm_num)
  · exact .prime 2 24 _ prime_2 (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 127 1 _ (by decide)
      (by reduce_mod_char; decide) (by norm_num)

/-!
  ## Constants

  These are convenience constants to match the Python module:
  - `pBits = 31`
  - `twoAdicity = 24` with `fieldSize - 1 = 2^24 * 127`
-/

/-- Bit width of the KoalaBear modulus. -/
@[reducible]
def pBits : Nat := 31

/-- The largest supported power-of-two root-of-unity exponent for KoalaBear. -/
@[reducible]
def twoAdicity : Nat := 24

/-!
  Provide instances so `KoalaBear.Field = ZMod fieldSize` is available as a `Field`
  and as a `NonBinaryField` (char ≠ 2).
-/

instance  _root_.KoalaBear.instFactPrimeFieldSize : Fact (Nat.Prime fieldSize) := ⟨is_prime⟩

instance  _root_.KoalaBear.instFieldField : _root_.Field Field := ZMod.instField fieldSize

instance  _root_.KoalaBear.instNonBinaryFieldField : NonBinaryField Field where
  char_neq_2 := by
    -- `decide` can discharge this concrete ZMod equality.
    simpa [Field, fieldSize] using
      (by decide : (2 : ZMod (2 ^ 31 - 2 ^ 24 + 1)) ≠ 0)

/-!
  ## Two-adicity and roots of unity table

  We record the factorization of `fieldSize - 1` and provide a precomputed table
  of `2^n`-th roots of unity for `0 ≤ n ≤ twoAdicity`.
-/

/-- The factorization `fieldSize - 1 = 2^twoAdicity * 127`. -/
lemma fieldSize_sub_one_factorization : fieldSize - 1 = 2 ^ twoAdicity * 127 := by
  unfold fieldSize twoAdicity
  decide

/-!
  A table of `2^n`-th roots of unity. The element at index `n` generates the
  multiplicative subgroup of order `2^n`.

  The first entry n = 0 is 1.
-/
/-- Precomputed generators for the KoalaBear two-adic subgroups. -/
def twoAdicGenerators : List Field :=
  [
    (0x1 : Field),
    (0x7F000000 : Field),
    (0x7E010002 : Field),
    (0x6832FE4A : Field),
    (0x8DBD69C : Field),
    (0xA28F031 : Field),
    (0x5C4A5B99 : Field),
    (0x29B75A80 : Field),
    (0x17668B8A : Field),
    (0x27AD539B : Field),
    (0x334D48C7 : Field),
    (0x7744959C : Field),
    (0x768FC6FA : Field),
    (0x303964B2 : Field),
    (0x3E687D4D : Field),
    (0x45A60E61 : Field),
    (0x6E2F4D7A : Field),
    (0x163BD499 : Field),
    (0x6C4A8A45 : Field),
    (0x143EF899 : Field),
    (0x514DDCAD : Field),
    (0x484EF19B : Field),
    (0x205D63C3 : Field),
    (0x68E7DD49 : Field),
    (0x6AC49F88 : Field)
  ]

@[simp] lemma twoAdicGenerators_length : twoAdicGenerators.length = twoAdicity + 1 := by decide

@[simp] lemma twoAdicGenerators_succ_square_eq' (idx : Fin twoAdicity) :
    twoAdicGenerators[idx.val + 1] ^ 2 = twoAdicGenerators[idx] := by
  fin_cases idx
  <;> simp [twoAdicGenerators] <;> decide

@[simp] lemma twoAdicGenerators_succ_square_eq (idx : Nat) (h : idx < twoAdicity) :
    haveI : idx + 1 < twoAdicGenerators.length := by simp [twoAdicGenerators_length, h]
    twoAdicGenerators[idx + 1] ^ 2 = twoAdicGenerators[idx] :=
  twoAdicGenerators_succ_square_eq' ⟨idx, h⟩

/-! Statements requested by the Python spec translation. -/

/-- Fermat-style inversion in `ZMod fieldSize`. -/
lemma inv_eq_pow (a : Field) (ha : a ≠ 0) : a⁻¹ = a ^ (fieldSize - 2) := by
  have hcard : Fintype.card Field = fieldSize := ZMod.card fieldSize
  have h1 : a ^ (fieldSize - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one a ha
    rw [hcard] at h; exact h
  have hmul : a * a ^ (fieldSize - 2) = 1 := by
    rw [← pow_succ']; show a ^ (fieldSize - 2 + 1) = 1
    have : fieldSize - 2 + 1 = fieldSize - 1 := by unfold fieldSize; omega
    rw [this]; exact h1
  exact (eq_inv_of_mul_eq_one_left (by rwa [mul_comm])).symm

/-- Bijectivity of the cube map on the unit group, using `gcd(3, fieldSize-1)=1`. -/
lemma cube_map_bijective :
    Function.Bijective (fun x : Fieldˣ ↦ x ^ 3) := by
  have hcard : Nat.card (Field)ˣ = fieldSize - 1 := by
    rw [Nat.card_units]; simp [Nat.card_eq_fintype_card, ZMod.card]
  have hcop : (Nat.card (Field)ˣ).Coprime 3 := by
    rw [hcard]; decide
  exact (powCoprime hcop).bijective

/-! The cube map x ↦ x^3 is an automorphism on the multiplicative group because
    `Nat.coprime 3 (fieldSize - 1)` holds. We record the coprimality here. -/
lemma coprime_three_fieldSize_sub_one : Nat.Coprime 3 (fieldSize - 1) := by
  -- Using the explicit factorization and concrete numerals
  simpa [fieldSize_sub_one_factorization, twoAdicity] using
    (by decide : Nat.Coprime 3 (2 ^ 24 * 127))

/-!
  Additional statements matching the Python spec API.
-/

/-- `twoAdicity` is maximal: `2^(twoAdicity+1)` does not divide `fieldSize - 1`. -/
lemma twoAdicity_maximal : ¬ (2 ^ (twoAdicity + 1)) ∣ (fieldSize - 1) := by
  decide

/-- Repeated squaring: `sqChain g n = g ^ (2^n)`.
    Uses `n` multiplications and avoids expanding the exponent into `2^n` steps. -/
public def sqChain (g : Field) : Nat → Field
  | 0 => g
  | n + 1 => let h := sqChain g n; h * h

public theorem sqChain_eq_pow_two_pow (g : Field) (n : Nat) :
    sqChain g n = g ^ (2 ^ n) := by
  induction n with
  | zero => simp [sqChain]
  | succ n ih => simp [sqChain, ih, pow_succ, pow_mul]

/-- Repeated squaring walks backward through the precomputed two-adic generator table. -/
public theorem sqChain_twoAdicGenerators_shift (k n : Nat) (hkn : k + n ≤ twoAdicity) :
    sqChain twoAdicGenerators[(⟨k + n, by omega⟩ : Fin (twoAdicity + 1))] n =
      twoAdicGenerators[(⟨k, by omega⟩ : Fin (twoAdicity + 1))] := by
  induction n generalizing k with
  | zero =>
      simp [sqChain]
  | succ n ih =>
      calc
        sqChain twoAdicGenerators[(⟨k + (n + 1), by omega⟩ : Fin (twoAdicity + 1))] (n + 1)
            =
              sqChain twoAdicGenerators[(⟨k + (n + 1), by omega⟩ : Fin (twoAdicity + 1))] n *
                sqChain twoAdicGenerators[(⟨k + (n + 1), by omega⟩ : Fin (twoAdicity + 1))] n := by
                  simp [sqChain]
        _ = twoAdicGenerators[(⟨k + 1, by omega⟩ : Fin (twoAdicity + 1))] *
              twoAdicGenerators[(⟨k + 1, by omega⟩ : Fin (twoAdicity + 1))] := by
              have hshift :
                  sqChain twoAdicGenerators[(⟨k + (n + 1), by omega⟩ : Fin (twoAdicity + 1))] n =
                    twoAdicGenerators[(⟨k + 1, by omega⟩ : Fin (twoAdicity + 1))] := by
                simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                  (ih (k := k + 1) (by omega))
              exact congrArg (fun x => x * x) hshift
        _ = twoAdicGenerators[(⟨k + 1, by omega⟩ : Fin (twoAdicity + 1))] ^ 2 := by
              simp [pow_two]
        _ = twoAdicGenerators[(⟨k, by omega⟩ : Fin (twoAdicity + 1))] := by
              simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                (twoAdicGenerators_succ_square_eq k (by omega))

/-- Every nonzero index in the precomputed table is genuinely nontrivial. -/
public lemma twoAdicGenerators_ne_one_of_pos (n : Fin (twoAdicity + 1)) (hn : 0 < n) :
    twoAdicGenerators[n] ≠ (1 : Field) := by
  fin_cases n <;> simp_all [twoAdicGenerators] <;> decide

/-- The power `(twoAdicGenerators[bits])^(2^bits) = 1`. -/
lemma twoAdicGenerators_pow_twoPow_eq_one (bits : Fin (twoAdicity + 1)) :
    twoAdicGenerators[bits] ^ (2 ^ (bits : Nat)) = 1 := by
  rw [← sqChain_eq_pow_two_pow]
  rcases bits with ⟨n, hn⟩
  have hshift :
      sqChain twoAdicGenerators[(⟨n, hn⟩ : Fin (twoAdicity + 1))] n =
        twoAdicGenerators[(⟨0, by omega⟩ : Fin (twoAdicity + 1))] := by
    have hidx : (⟨0 + n, by omega⟩ : Fin (twoAdicity + 1)) = ⟨n, hn⟩ := by
      ext
      simp
    convert sqChain_twoAdicGenerators_shift 0 n (by omega) using 2
    · exact (congrArg (fun i => twoAdicGenerators[i]) hidx).symm
  simpa [twoAdicGenerators] using hshift

/-- Helper: Fin-indexed version for computational verification of non-triviality. -/
public lemma twoAdicGenerators_pow_ne_one_aux (n : Fin 25) (m : Fin 25)
    (hm : m.val < n.val) :
    twoAdicGenerators[n] ^ (2 ^ m.val) ≠ (1 : Field) := by
  rw [← sqChain_eq_pow_two_pow]
  let nMinus : Fin (twoAdicity + 1) :=
    ⟨n.val - m.val, lt_of_le_of_lt (Nat.sub_le _ _) n.isLt⟩
  have hshift :
      sqChain twoAdicGenerators[n] m.val = twoAdicGenerators[nMinus] := by
    have hn_le : n.val ≤ twoAdicity := by
      simpa [twoAdicity] using Nat.le_of_lt_succ n.isLt
    have hbound : (n.val - m.val) + m.val ≤ twoAdicity := by
      simpa [Nat.sub_add_cancel (Nat.le_of_lt hm)] using hn_le
    simpa [Nat.sub_add_cancel (Nat.le_of_lt hm)] using
      (sqChain_twoAdicGenerators_shift (n.val - m.val) m.val hbound)
  rw [hshift]
  exact twoAdicGenerators_ne_one_of_pos nMinus (by
    change 0 < n.val - m.val
    exact Nat.sub_pos_of_lt hm)

/-- If `m < bits`, then `(twoAdicGenerators[bits])^(2^m) ≠ 1`. -/
lemma twoAdicGenerators_pow_twoPow_ne_one_of_lt
    {bits : Fin (twoAdicity + 1)} {m : Nat} (hm : m < bits) :
    (twoAdicGenerators[bits]) ^ (2 ^ m) ≠ (1 : Field) := by
  have hm_lt : m < 25 := Nat.lt_trans hm bits.isLt
  exact twoAdicGenerators_pow_ne_one_aux bits ⟨m, hm_lt⟩ hm

/-- The precomputed element at index `bits` is a primitive `2^bits`-th root of unity. -/
lemma isPrimitiveRoot_twoAdicGenerator (n : Fin (twoAdicity + 1)) :
    IsPrimitiveRoot (twoAdicGenerators[n]) (2 ^ (n : Nat)) := by
  rw [IsPrimitiveRoot.iff_def]
  rcases n with ⟨_ | k, hb⟩
  · -- bits = 0: 2^0 = 1, and any element satisfies x^1 = x, but twoAdicGenerators[0] = 1
    simp [twoAdicGenerators]
  · -- bits = k + 1
    constructor
    · exact twoAdicGenerators_pow_twoPow_eq_one ⟨k + 1, hb⟩
    · intro m hm
      by_contra h
      have hord := orderOf_eq_prime_pow
        (twoAdicGenerators_pow_twoPow_ne_one_of_lt (bits := ⟨k + 1, hb⟩) (m := k) (by simp))
        (twoAdicGenerators_pow_twoPow_eq_one ⟨k + 1, hb⟩)
      -- hord : orderOf (twoAdicGenerators[⟨k+1, hb⟩]) = 2 ^ (k + 1)
      have hdvd := orderOf_dvd_of_pow_eq_one hm
      rw [hord] at hdvd
      exact h hdvd

/-- As a unit, the precomputed element is a member of `rootsOfUnity (2^bits)`. -/
lemma twoAdicGenerator_unit_mem_rootsOfUnity
    (bits : Fin (twoAdicity + 1)) (h : twoAdicGenerators[bits] ≠ 0) :
    Units.mk0 (twoAdicGenerators[bits]) h ∈ rootsOfUnity (2 ^ (bits : Nat)) Field := by
  rw [mem_rootsOfUnity]
  rw [Units.ext_iff]
  simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
  exact twoAdicGenerators_pow_twoPow_eq_one bits

/-- The order of `twoAdicGenerators[bits]` equals `2^bits`. -/
lemma twoAdicGenerators_order (bits : Fin (twoAdicity + 1)) :
    orderOf (twoAdicGenerators[bits]) = 2 ^ (bits : Nat) := by
  rcases bits with ⟨_ | n, hb⟩
  · -- bits = 0: twoAdicGenerators[0] = 1, orderOf 1 = 1 = 2^0
    simp [twoAdicGenerators, orderOf_one]
  · -- bits = n + 1
    exact orderOf_eq_prime_pow
      (twoAdicGenerators_pow_twoPow_ne_one_of_lt (bits := ⟨n + 1, hb⟩) (m := n) (by simp))
      (twoAdicGenerators_pow_twoPow_eq_one ⟨n + 1, hb⟩)

/-- Primitive generator used by the smooth field-root splitter. -/
def primitiveRoot : Field := (3 : Field)

/-- `primitiveRoot ^ 127` is the maximal two-adic generator. -/
private lemma primitiveRoot_pow_127_eq_twoAdicGenerator :
    primitiveRoot ^ 127 = twoAdicGenerators[twoAdicity] := by
  norm_num [primitiveRoot, twoAdicity, twoAdicGenerators]
  rfl

/-- `primitiveRoot ^ 2^twoAdicity` is nontrivial. -/
private lemma primitiveRoot_pow_twoAdicity_ne_one :
    primitiveRoot ^ (2 ^ twoAdicity) ≠ (1 : Field) := by
  rw [← sqChain_eq_pow_two_pow]
  unfold primitiveRoot twoAdicity
  decide

/-- Prime divisors of `fieldSize - 1` are exactly `2` and `127`. -/
private lemma prime_dvd_fieldSize_sub_one_cases {p : Nat}
    (hp : p.Prime) (hdvd : p ∣ fieldSize - 1) :
    p = 2 ∨ p = 127 := by
  have hpdvd : p ∣ 2 ^ twoAdicity * 127 := by
    rw [← fieldSize_sub_one_factorization]
    exact hdvd
  rcases hp.dvd_mul.mp hpdvd with h2pow | h127
  · left
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow h2pow)
  · right
    exact (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 127)).mp h127

/-- The smooth field-root splitter generator has full multiplicative order. -/
lemma primitiveRoot_order : orderOf primitiveRoot = fieldSize - 1 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (n := fieldSize - 1) ?_ ?_ ?_
  · unfold fieldSize
    omega
  · exact ZMod.pow_card_sub_one_eq_one (a := primitiveRoot) (by
      unfold primitiveRoot
      decide)
  · intro p hp hdvd
    rcases prime_dvd_fieldSize_sub_one_cases hp hdvd with rfl | rfl
    · rw [fieldSize_sub_one_factorization, twoAdicity]
      have hdiv : (2 ^ 24 * 127) / 2 = 127 * 2 ^ 23 := by decide
      rw [hdiv, pow_mul, primitiveRoot_pow_127_eq_twoAdicGenerator]
      exact twoAdicGenerators_pow_twoPow_ne_one_of_lt
        (bits := (⟨twoAdicity, by omega⟩ : Fin (twoAdicity + 1))) (m := 23)
        (by simp [twoAdicity])
    · rw [fieldSize_sub_one_factorization]
      have hdiv : (2 ^ twoAdicity * 127) / 127 = 2 ^ twoAdicity :=
        by decide
      rw [hdiv]
      exact primitiveRoot_pow_twoAdicity_ne_one

/-- Smooth subgroup refinement schedule for `fieldSize - 1 = 2^24 * 127`. -/
def smoothRootSchedule : Array Nat :=
  (Array.replicate twoAdicity 2).push 127

/-- The KoalaBear smooth schedule refines the multiplicative group down to singleton cosets. -/
lemma smoothRootSchedule_fold_eq_one :
    smoothRootSchedule.toList.foldl (fun order ell ↦ order / ell) (fieldSize - 1) = 1 := by
  unfold smoothRootSchedule fieldSize twoAdicity
  decide

end KoalaBear


