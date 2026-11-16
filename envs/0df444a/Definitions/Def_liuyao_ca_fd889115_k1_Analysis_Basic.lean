-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Basic
-- name    : liuyao_ca_fd889115_k1_Analysis_Basic
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:43:10.598352+00:00
-- url     : https://prove2.me/theorems/e3820298-6e3a-4f72-bba0-7a5f71a99a94
-- title:
--   Analysis · Basic
-- statement:
--   Private portability check of the frozen foundation, with concrete rational decision proofs checked by the Lean kernel.

import Init.Grind.Ordered.Rat

set_option autoImplicit true

/-!
# Basic raw computable real and complex foundation

This file is the low-level substrate: rational intervals and boxes, raw real
and complex algorithms, validity and equivalence, rational coercions, raw
function representations, and the basic arithmetic operations on raw
algorithms.
-/

namespace ComputableAnalysis

abbrev QPos := {q : Rat // 0 < q}

namespace QPos

/-- The smaller of two positive rational tolerances, retained as a positive
subtype without passing through completed-real order theory. -/
def minimum (a b : QPos) : QPos :=
  if a.val <= b.val then a else b

theorem minimum_le_left (a b : QPos) :
    (minimum a b).val <= a.val := by
  unfold minimum
  split <;> grind

theorem minimum_le_right (a b : QPos) :
    (minimum a b).val <= b.val := by
  unfold minimum
  split <;> grind

/-- A positive natural denominator determines a positive rational radius. -/
def reciprocalNat (n : Nat) (hn : 0 < n) : QPos :=
  ⟨1 / ((n : Nat) : Rat), by
    rw [Rat.div_def, Rat.one_mul]
    exact (Rat.inv_pos).2 (by exact_mod_cast hn)⟩

@[simp] theorem reciprocalNat_val (n : Nat) (hn : 0 < n) :
    (reciprocalNat n hn).val = 1 / ((n : Nat) : Rat) :=
  rfl

end QPos

/-- A finite numerator/positive-denominator code for a rational number. -/
structure RationalCode where
  num : Int
  den : Nat
  den_nz : den ≠ 0

namespace RationalCode

def encode (q : Rat) : RationalCode where
  num := q.num
  den := q.den
  den_nz := q.den_nz

def decode (c : RationalCode) : Rat :=
  Rat.normalize c.num c.den c.den_nz

theorem den_pos (c : RationalCode) : 0 < c.den :=
  Nat.pos_of_ne_zero c.den_nz

theorem decode_encode (q : Rat) : decode (encode q) = q := by
  simpa [decode, encode] using Rat.normalize_self q

theorem encode_injective {q r : Rat} :
    encode q = encode r -> q = r := by
  intro h
  have hdecode := congrArg decode h
  simpa [decode_encode] using hdecode

theorem encode_eq_iff {q r : Rat} :
    encode q = encode r ↔ q = r := by
  constructor
  · exact encode_injective
  · intro h
    simpa [h]

end RationalCode

theorem rationalCode_decode_surjective (q : Rat) :
    Exists fun c : RationalCode => RationalCode.decode c = q := by
  exact ⟨RationalCode.encode q, RationalCode.decode_encode q⟩

/-! A finite diagonal pairing used by the rational-name enumeration. -/

def triangular : Nat -> Nat
  | 0 => 0
  | n + 1 => triangular n + (n + 1)

theorem triangular_succ (n : Nat) :
    triangular (n + 1) = triangular n + (n + 1) := by
  rfl

theorem triangular_monotone {a b : Nat} (h : a <= b) :
    triangular a <= triangular b := by
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      exact Nat.le_refl _
  | succ b ih =>
      by_cases hab : a <= b
      · rw [triangular_succ]
        exact Nat.le_trans (ih hab) (Nat.le_add_right _ _)
      · have ha : a = b + 1 := by omega
        subst a
        rw [triangular_succ]
        omega

def diagonalPair (a b : Nat) : Nat :=
  triangular (a + b) + a

def diagonalUnpair (n k : Nat) : Nat × Nat :=
  if h : n < k + 1 then (n, k - n)
  else diagonalUnpair (n - (k + 1)) (k + 1)
termination_by n
decreasing_by
  exact Nat.sub_lt (by omega) (by omega)

def diagonalUnpair_spec (n k : Nat) :
    diagonalPair (diagonalUnpair n k).1 (diagonalUnpair n k).2 =
      triangular k + n := by
  rw [diagonalUnpair]
  split
  · simp [diagonalPair]
    have hle : n ≤ k := by omega
    rw [Nat.add_sub_of_le hle]
  · rw [diagonalUnpair_spec]
    rw [triangular_succ]
    have hle : k + 1 ≤ n := by omega
    have hsub := Nat.sub_add_cancel hle
    omega
termination_by n
decreasing_by
  exact Nat.sub_lt (by omega) (by omega)

theorem diagonalUnpair_diagonalPair (a b : Nat) :
    diagonalUnpair (diagonalPair a b) 0 = (a, b) := by
  have aux : ∀ d : Nat, ∀ s a k : Nat,
      s - k = d -> a <= s -> k <= s ->
        diagonalUnpair (triangular s + a - triangular k) k = (a, s - a) := by
    intro d
    induction d with
    | zero =>
        intro s a k hdiff ha hk
        have hks : k = s := by omega
        subst s
        have hrem : triangular k + a - triangular k = a := by omega
        rw [hrem, diagonalUnpair]
        split
        · simp
        · omega
    | succ d ih =>
        intro s a k hdiff ha hk
        by_cases hks : k = s
        · subst s
          have hrem : triangular k + a - triangular k = a := by omega
          rw [hrem, diagonalUnpair]
          split
          · simp
          · omega
        · have hkslt : k < s := by omega
          have htri : triangular (k + 1) <= triangular s :=
            triangular_monotone (by omega)
          have hrem : k + 1 <= triangular s + a - triangular k := by
            rw [triangular_succ] at htri
            omega
          rw [diagonalUnpair]
          split
          · omega
          · have hdecr : s - (k + 1) = d := by omega
            have hnext :
                diagonalUnpair
                    (triangular s + a - triangular (k + 1)) (k + 1) =
                  (a, s - a) := by
              apply ih s a (k + 1) hdecr
              · exact ha
              · omega
            have hrem_eq :
                (triangular s + a - triangular k) - (k + 1) =
                  triangular s + a - triangular (k + 1) := by
              rw [triangular_succ]
              omega
            rw [hrem_eq]
            exact hnext
  have haux := aux (a + b) (a + b) a 0 (by omega) (by omega) (by omega)
  simpa [diagonalPair, triangular] using haux

theorem diagonalPair_injective {a b c d : Nat}
    (h : diagonalPair a b = diagonalPair c d) :
    (a, b) = (c, d) := by
  have hunpair := congrArg (fun n => diagonalUnpair n 0) h
  simpa [diagonalUnpair_diagonalPair] using hunpair

theorem diagonalPair_surjective (n : Nat) :
    Exists fun p : Nat × Nat => diagonalPair p.1 p.2 = n := by
  let p := diagonalUnpair n 0
  refine ⟨p, ?_⟩
  have h := diagonalUnpair_spec n 0
  simpa [p, triangular] using h

def integerCode (n : Nat) : Int :=
  if n % 2 = 0 then Int.ofNat (n / 2) else Int.negSucc (n / 2)

theorem integerCode_injective {m n : Nat} :
    integerCode m = integerCode n -> m = n := by
  intro h
  unfold integerCode at h
  by_cases hm : m % 2 = 0 <;> by_cases hn : n % 2 = 0
  · simp [hm, hn] at h
    omega
  · simp [hm, hn] at h
    cases h
  · simp [hm, hn] at h
    cases h
  · simp [hm, hn] at h
    omega

theorem integerCode_surjective (z : Int) :
    Exists fun n : Nat => integerCode n = z := by
  cases z with
  | ofNat m =>
      refine ⟨2 * m, ?_⟩
      simp [integerCode]
  | negSucc m =>
      refine ⟨2 * m + 1, ?_⟩
      simp [integerCode]
      omega

def integerIndex : Int -> Nat
  | Int.ofNat m => 2 * m
  | Int.negSucc m => 2 * m + 1

theorem integerCode_integerIndex (z : Int) :
    integerCode (integerIndex z) = z := by
  cases z with
  | ofNat m => simp [integerCode, integerIndex]
  | negSucc m =>
      simp [integerCode, integerIndex]
      omega

def rationalNatCode (n : Nat) : RationalCode :=
  let p := diagonalUnpair n 0
  { num := integerCode p.1
    den := p.2 + 1
    den_nz := by omega }

theorem rationalNatCode_injective {m n : Nat} :
    rationalNatCode m = rationalNatCode n -> m = n := by
  intro hcode
  have hnum := congrArg RationalCode.num hcode
  have hden := congrArg RationalCode.den hcode
  have hnum' :
      integerCode (diagonalUnpair m 0).1 =
        integerCode (diagonalUnpair n 0).1 := by
    simpa [rationalNatCode] using hnum
  have hden' :
      (diagonalUnpair m 0).2 + 1 = (diagonalUnpair n 0).2 + 1 := by
    simpa [rationalNatCode] using hden
  have hp1 : (diagonalUnpair m 0).1 = (diagonalUnpair n 0).1 :=
    integerCode_injective hnum'
  have hp2 : (diagonalUnpair m 0).2 = (diagonalUnpair n 0).2 := by
    omega
  have hpair : diagonalUnpair m 0 = diagonalUnpair n 0 :=
    Prod.ext hp1 hp2
  have hdiag : diagonalPair (diagonalUnpair m 0).1 (diagonalUnpair m 0).2 =
      diagonalPair (diagonalUnpair n 0).1 (diagonalUnpair n 0).2 := by
    exact congrArg (fun p : Nat × Nat => diagonalPair p.1 p.2) hpair
  have hm : diagonalPair (diagonalUnpair m 0).1 (diagonalUnpair m 0).2 = m := by
    have hspec := diagonalUnpair_spec m 0
    simpa [triangular] using hspec
  have hn : diagonalPair (diagonalUnpair n 0).1 (diagonalUnpair n 0).2 = n := by
    have hspec := diagonalUnpair_spec n 0
    simpa [triangular] using hspec
  omega

theorem rationalNatCode_encode_surjective (q : Rat) :
    Exists fun n : Nat => rationalNatCode n = RationalCode.encode q := by
  let c := RationalCode.encode q
  obtain ⟨u, hu⟩ := integerCode_surjective c.num
  let n := diagonalPair u (c.den - 1)
  refine ⟨n, ?_⟩
  have hpair := diagonalUnpair_diagonalPair u (c.den - 1)
  have hden : c.den - 1 + 1 = c.den := by
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr c.den_nz)
  have hcode : rationalNatCode n = c := by
    simp [rationalNatCode, n, hpair, hden, hu, c]
  exact hcode

theorem rationalNatCode_existsUnique_canonical_index (q : Rat) :
    ∃ n : Nat, rationalNatCode n = RationalCode.encode q ∧
      ∀ m : Nat, rationalNatCode m = RationalCode.encode q -> m = n := by
  obtain ⟨n, hn⟩ := rationalNatCode_encode_surjective q
  refine ⟨n, hn, ?_⟩
  intro m hm
  exact rationalNatCode_injective (hm.trans hn.symm)

theorem rationalNatCode_existsUnique_canonical_decode_index (q : Rat) :
    ∃ n : Nat,
      (rationalNatCode n = RationalCode.encode q ∧
        RationalCode.decode (rationalNatCode n) = q) ∧
      ∀ m : Nat,
        (rationalNatCode m = RationalCode.encode q ∧
          RationalCode.decode (rationalNatCode m) = q) -> m = n := by
  obtain ⟨n, hn, huniq⟩ := rationalNatCode_existsUnique_canonical_index q
  refine ⟨n, ⟨hn, ?_⟩, ?_⟩
  · rw [hn]
    exact RationalCode.decode_encode q
  · intro m hm
    exact huniq m hm.1

theorem rationalNatCode_decode_surjective (q : Rat) :
    Exists fun n : Nat => RationalCode.decode (rationalNatCode n) = q := by
  obtain ⟨n, hcode⟩ := rationalNatCode_encode_surjective q
  refine ⟨n, ?_⟩
  rw [hcode]
  exact RationalCode.decode_encode q

def rationalNatIndex (q : Rat) : Nat :=
  let c := RationalCode.encode q
  diagonalPair (integerIndex c.num) (c.den - 1)

theorem rationalNatCode_index (q : Rat) :
    rationalNatCode (rationalNatIndex q) = RationalCode.encode q := by
  let c := RationalCode.encode q
  have hpair := diagonalUnpair_diagonalPair (integerIndex c.num) (c.den - 1)
  have hden : c.den - 1 + 1 = c.den := by
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr c.den_nz)
  have hnum : integerCode (integerIndex c.num) = c.num :=
    integerCode_integerIndex c.num
  simp [rationalNatIndex, rationalNatCode, c, hpair, hden, hnum]

theorem rationalNatIndex_injective {p q : Rat}
    (h : rationalNatIndex p = rationalNatIndex q) : p = q := by
  have hcode := congrArg rationalNatCode h
  rw [rationalNatCode_index p, rationalNatCode_index q] at hcode
  exact RationalCode.encode_injective hcode

theorem one_div_nat_pos {n : Nat} (hn : 0 < n) : 0 < 1 / (n : Rat) := by
  rw [Rat.div_def, Rat.one_mul]
  exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 hn)

/-- The induction interface used by finite certificate constructions. -/
theorem nat_induction_schema {P : Nat -> Prop} (hzero : P 0)
    (hsucc : (n : Nat) -> P n -> P (n + 1)) : (n : Nat) -> P n := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
      simpa [Nat.succ_eq_add_one] using hsucc n ih

/-! A small finite-counting layer.  These recurrences are the certificate
cores of the subset-count and binomial-coefficient benchmark entries; no
finite-set or cardinality library is imported here. -/

namespace FiniteCounting

def subsetCount : Nat -> Nat
  | 0 => 1
  | n + 1 => 2 * subsetCount n

theorem subsetCount_succ (n : Nat) :
    subsetCount (n + 1) = 2 * subsetCount n := by
  rfl

theorem subsetCount_eq_pow (n : Nat) : subsetCount n = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [subsetCount_succ, ih, Nat.pow_succ]
      omega

def combination : Nat -> Nat -> Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => combination n k + combination n (k + 1)

theorem combination_zero_right (n : Nat) : combination n 0 = 1 := by
  cases n <;> rfl

theorem combination_zero_left (k : Nat) :
    combination 0 (k + 1) = 0 := by
  rfl

theorem combination_pascal (n k : Nat) :
    combination (n + 1) (k + 1) = combination n k + combination n (k + 1) := by
  rfl

theorem combination_rat_pascal (n k : Nat) :
    (combination (n + 1) (k + 1) : Rat) =
      (combination n k : Rat) + (combination n (k + 1) : Rat) := by
  exact_mod_cast combination_pascal n k

theorem combination_outside (n k : Nat) (h : n < k) :
    combination n k = 0 := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => omega
      | succ k => rfl
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          rw [combination_pascal]
          rw [ih k (by omega), ih (k + 1) (by omega)]

theorem combination_rat_outside (n k : Nat) (h : n < k) :
    (combination n k : Rat) = 0 := by
  rw [combination_outside n k h]
  rfl

theorem combination_self (n : Nat) : combination n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [combination_pascal, ih, combination_outside n (n + 1) (by omega)]

theorem combination_rat_self (n : Nat) :
    (combination n n : Rat) = 1 := by
  rw [combination_self]
  rfl

theorem combination_one (n : Nat) : combination n 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [combination_pascal, combination_zero_right, ih]
      omega

theorem combination_two_rat (n : Nat) :
    (combination n 2 : Rat) = (n : Rat) * ((n : Rat) - 1) / 2 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      have hpascal : combination (n + 1) 2 =
          combination n 1 + combination n 2 := by
        simpa using (combination_pascal n 1)
      rw [hpascal]
      simp only [Rat.natCast_add]
      rw [combination_one, ih]
      grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add,
        Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem combination_three_rat (n : Nat) :
    (combination n 3 : Rat) =
      (n : Rat) * ((n : Rat) - 1) * ((n : Rat) - 2) / 6 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      have hpascal : combination (n + 1) 3 =
          combination n 2 + combination n 3 := by
        simpa using (combination_pascal n 2)
      rw [hpascal]
      simp only [Rat.natCast_add]
      rw [combination_two_rat, ih]
      grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add,
        Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem combination_four_rat (n : Nat) :
    (combination n 4 : Rat) =
      (n : Rat) * ((n : Rat) - 1) * ((n : Rat) - 2) *
        ((n : Rat) - 3) / 24 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      have hpascal : combination (n + 1) 4 =
          combination n 3 + combination n 4 := by
        simpa using (combination_pascal n 3)
      rw [hpascal]
      simp only [Rat.natCast_add]
      rw [combination_three_rat, ih]
      grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add,
        Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem combination_five_rat (n : Nat) :
    (combination n 5 : Rat) =
      (n : Rat) * ((n : Rat) - 1) * ((n : Rat) - 2) *
        ((n : Rat) - 3) * ((n : Rat) - 4) / 120 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      have hpascal : combination (n + 1) 5 =
          combination n 4 + combination n 5 := by
        simpa using (combination_pascal n 4)
      rw [hpascal]
      simp only [Rat.natCast_add]
      rw [combination_four_rat, ih]
      grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add,
        Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem combination_six_rat (n : Nat) :
    (combination n 6 : Rat) =
      (n : Rat) * ((n : Rat) - 1) * ((n : Rat) - 2) *
        ((n : Rat) - 3) * ((n : Rat) - 4) *
        ((n : Rat) - 5) / 720 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      have hpascal : combination (n + 1) 6 =
          combination n 5 + combination n 6 := by
        simpa using (combination_pascal n 5)
      rw [hpascal]
      simp only [Rat.natCast_add]
      rw [combination_five_rat, ih]
      grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add,
        Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem combination_seven_rat (n : Nat) :
    (combination n 7 : Rat) =
      (n : Rat) * ((n : Rat) - 1) * ((n : Rat) - 2) *
        ((n : Rat) - 3) * ((n : Rat) - 4) * ((n : Rat) - 5) *
        ((n : Rat) - 6) / 5040 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      have hpascal : combination (n + 1) 7 =
          combination n 6 + combination n 7 := by
        simpa using (combination_pascal n 6)
      rw [hpascal]
      simp only [Rat.natCast_add]
      rw [combination_six_rat, ih]
      grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add,
        Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem combination_eight_rat (n : Nat) :
    (combination n 8 : Rat) =
      (n : Rat) * ((n : Rat) - 1) * ((n : Rat) - 2) *
        ((n : Rat) - 3) * ((n : Rat) - 4) * ((n : Rat) - 5) *
        ((n : Rat) - 6) * ((n : Rat) - 7) / 40320 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      have hpascal : combination (n + 1) 8 =
          combination n 7 + combination n 8 := by
        simpa using (combination_pascal n 7)
      rw [hpascal]
      simp only [Rat.natCast_add]
      rw [combination_seven_rat, ih]
      grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add,
        Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

end FiniteCounting

/-! A finite multiplicative certificate for later arithmetic factorization.
The factors are only required to be nontrivial here; primality, existence, and
uniqueness are deliberately separate future layers for benchmark item 80. -/

structure MultiplicativeCertificate (n : Nat) where
  factors : List Nat
  factors_ge_two : forall p, p ∈ factors -> 2 <= p
  product_eq : factors.foldl (fun acc p => acc * p) 1 = n

def factorizationCertificate60 : MultiplicativeCertificate 60 where
  factors := [2, 2, 3, 5]
  factors_ge_two := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl <;> omega
  product_eq := by decide +kernel

def BasicPrime (p : Nat) : Prop :=
  2 <= p /\ forall d, d ∣ p -> d = 1 \/ d = p

theorem basicPrime_of_no_proper_divisor {p : Nat} (hp : 2 <= p)
    (hproper : forall d, 2 <= d -> d < p -> ¬ d ∣ p) : BasicPrime p := by
  constructor
  · exact hp
  · intro d hd
    by_cases hd_one : d = 1
    · exact Or.inl hd_one
    by_cases hd_p : d = p
    · exact Or.inr hd_p
    exfalso
    apply hproper d
    · have hp_pos : 0 < p := by omega
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd hp_pos
      omega
    · have hp_pos : 0 < p := by omega
      have hd_le : d <= p := Nat.le_of_dvd hp_pos hd
      omega
    · exact hd

theorem basicPrime_iff_no_proper_divisor {p : Nat} :
    BasicPrime p ↔
      2 <= p ∧ forall d, 2 <= d -> d < p -> ¬ d ∣ p := by
  constructor
  · intro hp
    refine ⟨hp.1, ?_⟩
    intro d hd_two hd_lt hdvd
    rcases hp.2 d hdvd with rfl | rfl
    · omega
    · omega
  · rintro ⟨hp, hproper⟩
    exact basicPrime_of_no_proper_divisor hp hproper

def properDivisorSearch (p fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      let d := fuel + 1
      if 2 <= d ∧ d < p ∧ d ∣ p then some d
      else properDivisorSearch p fuel
termination_by fuel
decreasing_by
  omega

theorem properDivisorSearch_some_is_proper {p fuel d : Nat}
    (h : properDivisorSearch p fuel = some d) :
    2 <= d ∧ d < p ∧ d ∣ p := by
  induction fuel generalizing d with
  | zero => simp [properDivisorSearch] at h
  | succ fuel ih =>
      rw [properDivisorSearch] at h
      split at h
      · injection h with hd
        subst d
        assumption
      · exact ih h

theorem properDivisorSearch_some_of_proper {p fuel d : Nat}
    (hd_two : 2 <= d) (hd_lt : d < p) (hdvd : d ∣ p)
    (hdfuel : d <= fuel) : ∃ e, properDivisorSearch p fuel = some e := by
  induction fuel generalizing d with
  | zero => omega
  | succ fuel ih =>
      rw [properDivisorSearch]
      by_cases hcond : 1 <= fuel ∧ fuel + 1 < p ∧ fuel + 1 ∣ p
      · simp [hcond]
      · simp [hcond]
        by_cases hdfuel' : d <= fuel
        · exact ih hd_two hd_lt hdvd hdfuel'
        · have hd_eq : d = fuel + 1 := by
            omega
          subst d
          exact (hcond ⟨by omega, hd_lt, hdvd⟩).elim

theorem properDivisorSearch_none_of_no_proper {p fuel : Nat}
    (hproper : forall d, 2 <= d -> d < p -> ¬ d ∣ p) :
    properDivisorSearch p fuel = none := by
  induction fuel with
  | zero => simp [properDivisorSearch]
  | succ fuel ih =>
      rw [properDivisorSearch]
      split
      · rename_i hcond
        exact (hproper _ hcond.1 hcond.2.1 hcond.2.2).elim
      · exact ih

theorem properDivisorSearch_none_iff_no_proper {p : Nat} :
    properDivisorSearch p p = none ↔
      forall d, 2 <= d -> d < p -> ¬ d ∣ p := by
  constructor
  · intro h d hd_two hd_lt hdvd
    obtain ⟨e, he⟩ :=
      properDivisorSearch_some_of_proper (fuel := p)
        hd_two hd_lt hdvd (by omega)
    rw [h] at he
    cases he
  · intro hproper
    exact properDivisorSearch_none_of_no_proper hproper

theorem basicPrime_of_properDivisorSearch_none {p : Nat} (hp : 2 <= p)
    (h : properDivisorSearch p p = none) : BasicPrime p :=
  basicPrime_of_no_proper_divisor hp
    ((properDivisorSearch_none_iff_no_proper).1 h)

theorem basicPrime_two : BasicPrime 2 := by
  constructor
  · omega
  · intro d hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
    have hdle : d <= 2 := Nat.le_of_dvd (by omega) hd
    have hcases : d = 1 \/ d = 2 := by omega
    exact hcases

theorem basicPrime_three : BasicPrime 3 := by
  constructor
  · omega
  · intro d hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
    have hdle : d <= 3 := Nat.le_of_dvd (by omega) hd
    have hcases : d = 1 \/ d = 2 \/ d = 3 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact Or.inl rfl
    · simp at hd
    · exact Or.inr rfl

theorem basicPrime_five : BasicPrime 5 := by
  constructor
  · omega
  · intro d hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
    have hdle : d <= 5 := Nat.le_of_dvd (by omega) hd
    have hcases : d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/ d = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · simp at hd
    · simp at hd
    · simp at hd
    · exact Or.inr rfl

theorem basicPrime_eq_of_dvd {p q : Nat}
    (hp : BasicPrime p) (hq : BasicPrime q) (h : p ∣ q) : p = q := by
  rcases hq.2 p h with hp_one | hp_eq
  · have hp_two : 2 <= p := hp.1
    omega
  · exact hp_eq

theorem basicPrime_coprime_of_not_dvd {p a : Nat} (hp : BasicPrime p)
    (hpa : ¬ p ∣ a) : Nat.Coprime p a := by
  show Nat.gcd p a = 1
  have hgp : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
  have hga : Nat.gcd p a ∣ a := Nat.gcd_dvd_right p a
  rcases hp.2 _ hgp with hg | hg
  · exact hg
  · exfalso
    apply hpa
    rw [← hg]
    exact hga

theorem basicPrime_dvd_of_dvd_mul {p a b : Nat} (hp : BasicPrime p)
    (hab : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases hpa : p ∣ a
  · exact Or.inl hpa
  · exact Or.inr ((basicPrime_coprime_of_not_dvd hp hpa).dvd_of_dvd_mul_left hab)

theorem basicPrime_dvd_of_dvd_pow {p a n : Nat} (hp : BasicPrime p)
    (h : p ∣ a ^ n) : p ∣ a := by
  induction n with
  | zero =>
      have hp_one : p = 1 := Nat.dvd_one.mp (by simpa using h)
      have hp_two : 2 <= p := hp.1
      omega
  | succ n ih =>
      have hmul : p ∣ a ^ n * a := by
        simpa [Nat.pow_succ] using h
      rcases basicPrime_dvd_of_dvd_mul hp hmul with hpow | hpa
      · exact ih hpow
      · exact hpa

def natProduct : List Nat -> Nat
  | [] => 1
  | a :: as => a * natProduct as

theorem natProduct_perm {xs ys : List Nat} (h : xs.Perm ys) :
    natProduct xs = natProduct ys := by
  induction h with
  | nil => rfl
  | cons a h ih => simp [natProduct, ih]
  | swap a b l =>
      simp [natProduct, Nat.mul_left_comm]
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem list_mem_dvd_natProduct {a : Nat} {xs : List Nat}
    (ha : a ∈ xs) : a ∣ natProduct xs := by
  induction xs with
  | nil => simp at ha
  | cons b bs ih =>
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact ⟨natProduct bs, by simp [natProduct]⟩
      · rcases ih ha with ⟨k, hk⟩
        refine ⟨b * k, ?_⟩
        simp [natProduct, hk, Nat.mul_left_comm]

theorem foldl_mul_one_eq_natProduct (xs : List Nat) :
    xs.foldl (fun acc a => acc * a) 1 = natProduct xs := by
  have hfold : ∀ (ys : List Nat) (acc : Nat),
      ys.foldl (fun acc a => acc * a) acc =
        acc * ys.foldl (fun acc a => acc * a) 1 := by
    intro ys
    induction ys with
    | nil => intro acc; simp
    | cons b bs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [ih (acc * b)]
        simp only [Nat.one_mul]
        rw [ih b]
        exact Nat.mul_assoc _ _ _
  induction xs with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      calc
        as.foldl (fun acc b => acc * b) (1 * a) =
            as.foldl (fun acc b => acc * b) a := by simp
        _ = a * as.foldl (fun acc b => acc * b) 1 := hfold as a
        _ = a * natProduct as := by rw [ih]
        _ = natProduct (a :: as) := by rfl

theorem foldl_mul_acc_eq_acc_mul_foldl_one (xs : List Nat) (acc : Nat) :
    xs.foldl (fun acc a => acc * a) acc =
      acc * xs.foldl (fun acc a => acc * a) 1 := by
  induction xs generalizing acc with
  | nil => simp
  | cons a as ih =>
      simp only [List.foldl_cons]
      rw [ih (acc * a)]
      simp only [Nat.one_mul]
      rw [ih a]
      exact Nat.mul_assoc _ _ _

def MultiplicativeCertificate.append {m n : Nat}
    (c₁ : MultiplicativeCertificate m) (c₂ : MultiplicativeCertificate n) :
    MultiplicativeCertificate (m * n) where
  factors := c₁.factors ++ c₂.factors
  factors_ge_two := by
    intro p hp
    simp only [List.mem_append] at hp
    rcases hp with hp | hp
    · exact c₁.factors_ge_two p hp
    · exact c₂.factors_ge_two p hp
  product_eq := by
    rw [List.foldl_append, c₁.product_eq,
      foldl_mul_acc_eq_acc_mul_foldl_one, c₂.product_eq]

theorem MultiplicativeCertificate.factors_nonempty {n : Nat}
    (c : MultiplicativeCertificate n) (hn : 1 < n) : c.factors ≠ [] := by
  intro hnil
  have hprod := c.product_eq
  rw [hnil] at hprod
  simp at hprod
  omega

theorem MultiplicativeCertificate.factor_dvd {n : Nat}
    (c : MultiplicativeCertificate n) {p : Nat} (hp : p ∈ c.factors) :
    p ∣ n := by
  have hpProd : p ∣ natProduct c.factors := list_mem_dvd_natProduct hp
  have hpFold : p ∣ c.factors.foldl (fun acc q => acc * q) 1 := by
    rw [foldl_mul_one_eq_natProduct]
    exact hpProd
  simpa [c.product_eq] using hpFold

theorem basicPrime_dvd_of_dvd_natProduct {p : Nat} (hp : BasicPrime p)
    {xs : List Nat} (h : p ∣ natProduct xs) : ∃ a, a ∈ xs ∧ p ∣ a := by
  induction xs with
  | nil =>
      have hp_one : p = 1 := Nat.dvd_one.mp (by simpa [natProduct] using h)
      have hp_two : 2 <= p := hp.1
      omega
  | cons a as ih =>
      have hmul : p ∣ a * natProduct as := by simpa [natProduct] using h
      rcases basicPrime_dvd_of_dvd_mul hp hmul with ha | has
      · exact ⟨a, by simp, ha⟩
      · rcases ih has with ⟨b, hb, hpb⟩
        exact ⟨b, by simp [hb], hpb⟩

theorem natProduct_pos_of_pos {xs : List Nat}
    (hpos : forall a, a ∈ xs -> 0 < a) : 0 < natProduct xs := by
  induction xs with
  | nil => simp [natProduct]
  | cons a as ih =>
      simp only [natProduct]
      apply Nat.mul_pos
      · exact hpos a (by simp)
      · apply ih
        intro b hb
        exact hpos b (by simp [hb])

structure PrimeFactorCertificate (n : Nat) where
  factors : List Nat
  factors_prime : forall p, p ∈ factors -> BasicPrime p
  product_eq : factors.foldl (fun acc p => acc * p) 1 = n

def PrimeFactorCertificate.append {m n : Nat}
    (c₁ : PrimeFactorCertificate m) (c₂ : PrimeFactorCertificate n) :
    PrimeFactorCertificate (m * n) where
  factors := c₁.factors ++ c₂.factors
  factors_prime := by
    intro p hp
    simp only [List.mem_append] at hp
    rcases hp with hp | hp
    · exact c₁.factors_prime p hp
    · exact c₂.factors_prime p hp
  product_eq := by
    rw [List.foldl_append, c₁.product_eq,
      foldl_mul_acc_eq_acc_mul_foldl_one, c₂.product_eq]

def primeFactorCertificate_exists (n : Nat) (hn : 1 < n) :
    Nonempty (PrimeFactorCertificate n) := by
  by_cases hnone : properDivisorSearch n n = none
  · have hp : BasicPrime n :=
      basicPrime_of_properDivisorSearch_none (by omega) hnone
    refine ⟨{ factors := [n]
              factors_prime := by
                intro p hp_mem
                simp at hp_mem
                subst p
                exact hp
              product_eq := by simp }⟩
  · cases hs : properDivisorSearch n n with
    | none => exact (hnone hs).elim
    | some d =>
        have hdprop : 2 <= d ∧ d < n ∧ d ∣ n :=
          properDivisorSearch_some_is_proper hs
        have hprod : d * (n / d) = n := Nat.mul_div_cancel' hdprop.2.2
        have hq_pos : 0 < n / d := by
          by_cases hq_zero : n / d = 0
          · rw [hq_zero] at hprod
            simp at hprod
            omega
          · exact Nat.pos_of_ne_zero hq_zero
        have hq_gt : 1 < n / d := by
          have hq_ge : 1 <= n / d := by omega
          by_cases hq_le : n / d <= 1
          · have hq_one : n / d = 1 := by omega
            rw [hq_one] at hprod
            omega
          · omega
        have hq_lt : n / d < n :=
          Nat.div_lt_self (by omega) (by omega)
        rcases primeFactorCertificate_exists d (by omega) with ⟨cd⟩
        rcases primeFactorCertificate_exists (n / d) hq_gt with ⟨cq⟩
        have hc : PrimeFactorCertificate (d * (n / d)) :=
          PrimeFactorCertificate.append cd cq
        rw [hprod] at hc
        exact ⟨hc⟩
termination_by n
decreasing_by
  · exact hdprop.2.1
  · exact hq_lt

theorem PrimeFactorCertificate.factor_dvd {n : Nat}
    (c : PrimeFactorCertificate n) {p : Nat} (hp : p ∈ c.factors) :
    p ∣ n := by
  have hpProd : p ∣ natProduct c.factors := list_mem_dvd_natProduct hp
  have hpFold : p ∣ c.factors.foldl (fun acc q => acc * q) 1 := by
    rw [foldl_mul_one_eq_natProduct]
    exact hpProd
  simpa [c.product_eq] using hpFold

theorem PrimeFactorCertificate.factor_le {n : Nat}
    (c : PrimeFactorCertificate n) (hn : 1 < n)
    {p : Nat} (hp : p ∈ c.factors) : p ≤ n := by
  exact Nat.le_of_dvd (by omega) (c.factor_dvd hp)

theorem PrimeFactorCertificate.factors_nonempty {n : Nat}
    (c : PrimeFactorCertificate n) (hn : 1 < n) : c.factors ≠ [] := by
  intro hnil
  have hprod := c.product_eq
  rw [hnil] at hprod
  simp at hprod
  omega

theorem PrimeFactorCertificate.exists_prime_dvd {n : Nat}
    (c : PrimeFactorCertificate n) (hn : 1 < n) :
    ∃ p, p ∣ n ∧ BasicPrime p := by
  have hne := c.factors_nonempty hn
  cases hfac : c.factors with
  | nil => exact (hne hfac).elim
  | cons p ps =>
      have hmem : p ∈ c.factors := by simp [hfac]
      have hpProd : p ∣ natProduct c.factors := list_mem_dvd_natProduct hmem
      have hpFold : p ∣ c.factors.foldl (fun acc q => acc * q) 1 := by
        rw [foldl_mul_one_eq_natProduct]
        exact hpProd
      refine ⟨p, ?_, c.factors_prime p hmem⟩
      simpa [c.product_eq] using hpFold

theorem exists_basicPrime_dvd {n : Nat} (hn : 1 < n) :
    ∃ p, p ∣ n ∧ BasicPrime p := by
  rcases primeFactorCertificate_exists n hn with ⟨c⟩
  exact c.exists_prime_dvd hn

theorem exists_basicPrime_not_mem_of_all_basicPrime (xs : List Nat)
    (hprime : ∀ p, p ∈ xs -> BasicPrime p) :
    ∃ p, BasicPrime p ∧ p ∉ xs := by
  have hprod_pos : 0 < natProduct xs :=
    natProduct_pos_of_pos (by
      intro p hp
      have hp_two : 2 <= p := (hprime p hp).1
      omega)
  have htarget : 1 < natProduct xs + 1 := by omega
  rcases exists_basicPrime_dvd htarget with ⟨p, hp_target, hp⟩
  refine ⟨p, hp, ?_⟩
  intro hmem
  have hp_product : p ∣ natProduct xs := list_mem_dvd_natProduct hmem
  have hp_one : p ∣ 1 := by
    apply (Nat.dvd_add_iff_right hp_product).2
    simpa [Nat.add_comm] using hp_target
  have hp_eq_one : p = 1 := Nat.dvd_one.mp hp_one
  have hp_two : 2 <= p := hp.1
  omega

def shiftedRangeProduct (n : Nat) : Nat :=
  natProduct ((List.range n).map (fun k => k + 2))

theorem exists_basicPrime_gt (n : Nat) :
    ∃ p, BasicPrime p ∧ n < p := by
  let xs := (List.range n).map (fun k => k + 2)
  have hprod_pos : 0 < natProduct xs :=
    natProduct_pos_of_pos (by
      intro p hp
      simp only [xs, List.mem_map] at hp
      rcases hp with ⟨k, hk, rfl⟩
      omega)
  have htarget : 1 < natProduct xs + 1 := by omega
  rcases exists_basicPrime_dvd htarget with ⟨p, hp_target, hp⟩
  refine ⟨p, hp, ?_⟩
  by_cases hlt : n < p
  · exact hlt
  · exfalso
    have hp_le : p <= n := by omega
    have hp_two : 2 <= p := hp.1
    have hk_lt : p - 2 < n := by omega
    have hk_mem : p - 2 ∈ List.range n := by
      simpa using hk_lt
    have hp_mem : p ∈ xs := by
      apply List.mem_map.mpr
      exact ⟨p - 2, hk_mem, by omega⟩
    have hp_product : p ∣ natProduct xs := list_mem_dvd_natProduct hp_mem
    have hp_one : p ∣ 1 := by
      apply (Nat.dvd_add_iff_right hp_product).2
      simpa [Nat.add_comm] using hp_target
    have hp_eq_one : p = 1 := Nat.dvd_one.mp hp_one
    omega

theorem PrimeFactorCertificate.exists_factor_dvd {n : Nat}
    (c : PrimeFactorCertificate n) (hn : 1 < n) :
    ∃ p, p ∈ c.factors ∧ BasicPrime p ∧ p ∣ n := by
  have hne := c.factors_nonempty hn
  cases hfac : c.factors with
  | nil => exact (hne hfac).elim
  | cons p ps =>
      have hmem : p ∈ c.factors := by simp [hfac]
      exact ⟨p, by simp, c.factors_prime p hmem, c.factor_dvd hmem⟩

theorem basicPrime_dvd_of_dvd_primeFactorization {p n : Nat}
    (hp : BasicPrime p) (c : PrimeFactorCertificate n) (h : p ∣ n) :
    ∃ a, a ∈ c.factors ∧ p ∣ a := by
  apply basicPrime_dvd_of_dvd_natProduct hp
  rw [← foldl_mul_one_eq_natProduct c.factors]
  simpa [c.product_eq] using h

theorem basicPrime_eq_factor_of_dvd_primeFactorization {p n : Nat}
    (hp : BasicPrime p) (c : PrimeFactorCertificate n) (h : p ∣ n) :
    ∃ a, a ∈ c.factors ∧ p = a := by
  rcases basicPrime_dvd_of_dvd_primeFactorization hp c h with ⟨a, ha, hpa⟩
  exact ⟨a, ha, basicPrime_eq_of_dvd hp (c.factors_prime a ha) hpa⟩

theorem basicPrime_dvd_primeFactorization_iff {p n : Nat}
    (hp : BasicPrime p) (c : PrimeFactorCertificate n) :
    p ∣ n ↔ ∃ a, a ∈ c.factors ∧ p = a := by
  constructor
  · exact basicPrime_eq_factor_of_dvd_primeFactorization hp c
  · rintro ⟨a, ha, hpa⟩
    have haProd : a ∣ natProduct c.factors := list_mem_dvd_natProduct ha
    have haFold : a ∣ c.factors.foldl (fun acc q => acc * q) 1 := by
      rw [foldl_mul_one_eq_natProduct]
      exact haProd
    simpa [c.product_eq, hpa] using haFold

theorem PrimeFactorCertificate.factor_mem_of_factor_mem {n : Nat}
    (c₁ c₂ : PrimeFactorCertificate n) {p : Nat}
    (hp : p ∈ c₁.factors) : ∃ q, q ∈ c₂.factors ∧ p = q := by
  have hpdvd : p ∣ n := c₁.factor_dvd hp
  exact basicPrime_eq_factor_of_dvd_primeFactorization
    (c₁.factors_prime p hp) c₂ hpdvd

theorem PrimeFactorCertificate.factor_mem_iff {n : Nat}
    (c₁ c₂ : PrimeFactorCertificate n) {p : Nat} :
    p ∈ c₁.factors ↔ p ∈ c₂.factors := by
  constructor
  · intro hp
    rcases c₁.factor_mem_of_factor_mem c₂ hp with ⟨q, hq, hpq⟩
    simpa [← hpq] using hq
  · intro hp
    rcases c₂.factor_mem_of_factor_mem c₁ hp with ⟨q, hq, hpq⟩
    simpa [← hpq] using hq

theorem natList_perm_cons_of_mem {a : Nat} {xs : List Nat}
    (ha : a ∈ xs) : ∃ ys, xs.Perm (a :: ys) := by
  induction xs with
  | nil => simp at ha
  | cons b bs ih =>
      by_cases hab : a = b
      · subst a
        exact ⟨bs, List.Perm.refl _⟩
      · have hbs : a ∈ bs := by
          simpa [hab] using ha
        rcases ih hbs with ⟨ys, hperm⟩
        refine ⟨b :: ys, ?_⟩
        exact hperm.cons b |>.trans (List.Perm.swap a b ys)

theorem primeFactorList_perm_of_same_product
    {xs ys : List Nat}
    (hxs : forall p, p ∈ xs -> BasicPrime p)
    (hys : forall p, p ∈ ys -> BasicPrime p)
    (hprod : natProduct xs = natProduct ys) :
    xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => exact List.Perm.nil
      | cons q qs =>
          have hq : BasicPrime q := hys q (by simp)
          have hqge : 2 <= q := hq.1
          have hqspos : 0 < natProduct qs :=
            natProduct_pos_of_pos (fun a ha => by
              have hge := (hys a (by simp [ha])).1
              omega)
          have hqprod : 2 <= q * natProduct qs := by
            calc
              2 <= q := hqge
              _ = q * 1 := by simp
              _ <= q * natProduct qs := Nat.mul_le_mul_left q (by omega)
          have hbad : 1 = q * natProduct qs := by
            simpa [natProduct] using hprod
          omega
  | cons p ps ih =>
      have hp : BasicPrime p := hxs p (by simp)
      have hpdiv : p ∣ natProduct ys := by
        rw [← hprod]
        exact ⟨natProduct ps, by simp [natProduct]
        ⟩
      rcases basicPrime_dvd_of_dvd_natProduct hp hpdiv with ⟨q, hq, hpq⟩
      have hqprime : BasicPrime q := hys q hq
      have hp_eq_q : p = q := basicPrime_eq_of_dvd hp hqprime hpq
      subst q
      rcases natList_perm_cons_of_mem hq with ⟨zs, hperm⟩
      have hprod_tail : natProduct ps = natProduct zs := by
        have hp_ge : 2 <= p := hp.1
        have hp_pos : 0 < p := by omega
        apply Nat.mul_left_cancel hp_pos
        calc
          p * natProduct ps = natProduct (p :: ps) := by rfl
          _ = natProduct ys := hprod
          _ = natProduct (p :: zs) := natProduct_perm hperm
          _ = p * natProduct zs := by rfl
      have hps : forall r, r ∈ ps -> BasicPrime r := by
        intro r hr
        exact hxs r (by simp [hr])
      have hzs : forall r, r ∈ zs -> BasicPrime r := by
        intro r hr
        have hry : r ∈ ys := (List.Perm.mem_iff hperm).2 (by simp [hr])
        exact hys r hry
      have htail : ps.Perm zs := ih hps hzs hprod_tail
      exact (List.Perm.cons p htail).trans hperm.symm

theorem PrimeFactorCertificate.factor_perm {n : Nat}
    (c₁ c₂ : PrimeFactorCertificate n) :
    c₁.factors.Perm c₂.factors := by
  apply primeFactorList_perm_of_same_product c₁.factors_prime c₂.factors_prime
  calc
    natProduct c₁.factors =
        c₁.factors.foldl (fun acc p => acc * p) 1 :=
      (foldl_mul_one_eq_natProduct c₁.factors).symm
    _ = n := c₁.product_eq
    _ = c₂.factors.foldl (fun acc p => acc * p) 1 := c₂.product_eq.symm
    _ = natProduct c₂.factors := foldl_mul_one_eq_natProduct c₂.factors

theorem natList_perm_of_nodup_of_mem_iff {xs ys : List Nat}
    (hxs : xs.Nodup) (hys : ys.Nodup)
    (hmem : forall a, a ∈ xs ↔ a ∈ ys) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
      have hys_nil : ys = [] := by
        cases ys with
        | nil => rfl
        | cons y ys =>
            have hy : y ∈ ([] : List Nat) := (hmem y).2 (by simp)
            simp at hy
      simp [hys_nil]
  | cons a as ih =>
      have ha_ys : a ∈ ys := (hmem a).1 (by simp)
      rcases natList_perm_cons_of_mem ha_ys with ⟨bs, hysperm⟩
      have habs_nodup : (a :: bs).Nodup := hysperm.nodup hys
      have hxs_cons : ¬ a ∈ as ∧ as.Nodup := List.nodup_cons.mp hxs
      have habs_cons : ¬ a ∈ bs ∧ bs.Nodup := List.nodup_cons.mp habs_nodup
      have hmem_rest : forall x, x ∈ as ↔ x ∈ bs := by
        intro x
        have hperm_mem : x ∈ ys ↔ x ∈ a :: bs :=
          List.Perm.mem_iff hysperm
        constructor
        · intro hx
          have hx_ys : x ∈ ys := (hmem x).1 (by simp [hx])
          have hx_cons : x = a ∨ x ∈ bs := by
            simpa using hperm_mem.1 hx_ys
          rcases hx_cons with hxa | hxb
          · subst x
            exact (hxs_cons.1 hx).elim
          · exact hxb
        · intro hx_bs
          have hx_cons : x ∈ a :: bs := by simp [hx_bs]
          have hx_ys : x ∈ ys := hperm_mem.2 hx_cons
          have hx_all : x ∈ a :: as := (hmem x).2 hx_ys
          have hx_cases : x = a ∨ x ∈ as := by simpa using hx_all
          rcases hx_cases with hxa | hxa
          · subst x
            exact (habs_cons.1 hx_bs).elim
          · exact hxa
      have hrest : as.Perm bs := ih hxs_cons.2 habs_cons.2 hmem_rest
      exact hrest.cons a |>.trans hysperm.symm

theorem PrimeFactorCertificate.factor_perm_of_nodup {n : Nat}
    (c₁ c₂ : PrimeFactorCertificate n)
    (h₁ : c₁.factors.Nodup) (h₂ : c₂.factors.Nodup) :
    c₁.factors.Perm c₂.factors := by
  exact natList_perm_of_nodup_of_mem_iff h₁ h₂
    (fun p => PrimeFactorCertificate.factor_mem_iff c₁ c₂)

def primeFactorizationCertificate60 : PrimeFactorCertificate 60 where
  factors := [2, 2, 3, 5]
  factors_prime := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    · exact basicPrime_two
    · exact basicPrime_three
    · exact basicPrime_five
  product_eq := by decide +kernel

/-! An explicit terminating Euclidean loop for the natural-number gcd. -/

def euclideanGcd (a b : Nat) : Nat :=
  if h : b = 0 then a else euclideanGcd b (a % b)
termination_by b
decreasing_by
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

def euclideanGcd_eq_gcd_proof (a b : Nat) :
    euclideanGcd a b = Nat.gcd a b :=
  match b with
  | 0 => by simp [euclideanGcd]
  | b + 1 => by
      calc
        euclideanGcd a (b + 1) = euclideanGcd (b + 1) (a % (b + 1)) := by
          rw [euclideanGcd]
          exact dif_neg (by omega)
        _ = Nat.gcd (b + 1) (a % (b + 1)) :=
          euclideanGcd_eq_gcd_proof (b + 1) (a % (b + 1))
        _ = Nat.gcd (a % (b + 1)) (b + 1) := Nat.gcd_comm _ _
        _ = Nat.gcd (b + 1) a := by
          rw [← Nat.gcd_rec]
        _ = Nat.gcd a (b + 1) := Nat.gcd_comm _ _
termination_by b
decreasing_by
  exact Nat.mod_lt _ (by omega)

theorem euclideanGcd_eq_gcd (a b : Nat) :
    euclideanGcd a b = Nat.gcd a b := by
  exact euclideanGcd_eq_gcd_proof a b

theorem euclideanGcd_step (a b : Nat) (hb : b ≠ 0) :
    euclideanGcd a b = euclideanGcd b (a % b) := by
  rw [euclideanGcd]
  exact dif_neg hb

theorem euclideanGcd_zero_right (a : Nat) : euclideanGcd a 0 = a := by
  rw [euclideanGcd_eq_gcd]
  simp

theorem euclideanGcd_zero_left (a : Nat) : euclideanGcd 0 a = a := by
  rw [euclideanGcd_eq_gcd]
  simp [Nat.gcd_comm]

theorem euclideanGcd_pos_of_pos {a b : Nat}
    (ha : 0 < a) :
    0 < euclideanGcd a b := by
  rw [euclideanGcd_eq_gcd]
  exact Nat.gcd_pos_of_pos_left b ha

theorem euclideanGcd_pos_iff {a b : Nat} :
    0 < euclideanGcd a b ↔ a ≠ 0 ∨ b ≠ 0 := by
  rw [euclideanGcd_eq_gcd, Nat.pos_iff_ne_zero]
  constructor
  · intro h
    by_cases ha : a = 0
    · right
      intro hb
      apply h
      exact Nat.gcd_eq_zero_iff.mpr ⟨ha, hb⟩
    · exact Or.inl ha
  · intro h hg
    rcases h with ha | hb
    · exact ha (Nat.gcd_eq_zero_iff.mp hg).1
    · exact hb (Nat.gcd_eq_zero_iff.mp hg).2

theorem euclideanGcd_eq_one_iff_coprime {a b : Nat} :
    euclideanGcd a b = 1 ↔ Nat.Coprime a b := by
  rw [euclideanGcd_eq_gcd]

theorem euclideanGcd_comm (a b : Nat) :
    euclideanGcd a b = euclideanGcd b a := by
  rw [euclideanGcd_eq_gcd, euclideanGcd_eq_gcd]
  exact Nat.gcd_comm a b

theorem euclideanGcd_dvd_left (a b : Nat) :
    euclideanGcd a b ∣ a := by
  rw [euclideanGcd_eq_gcd]
  exact Nat.gcd_dvd_left a b

theorem euclideanGcd_dvd_right (a b : Nat) :
    euclideanGcd a b ∣ b := by
  rw [euclideanGcd_eq_gcd]
  exact Nat.gcd_dvd_right a b

theorem euclideanGcd_dvd_of_dvd {a b d : Nat}
    (hda : d ∣ a) (hdb : d ∣ b) : d ∣ euclideanGcd a b := by
  rw [euclideanGcd_eq_gcd]
  exact Nat.dvd_gcd hda hdb

theorem euclideanGcd_dvd_iff {a b d : Nat} :
    d ∣ euclideanGcd a b ↔ d ∣ a ∧ d ∣ b := by
  constructor
  · intro hd
    exact ⟨Nat.dvd_trans hd (euclideanGcd_dvd_left a b),
      Nat.dvd_trans hd (euclideanGcd_dvd_right a b)⟩
  · rintro ⟨hda, hdb⟩
    exact euclideanGcd_dvd_of_dvd hda hdb

theorem gcd_remainder_swap (a b : Nat) :
    Nat.gcd b (a % b) = Nat.gcd a b := by
  calc
    Nat.gcd b (a % b) = Nat.gcd (a % b) b := Nat.gcd_comm _ _
    _ = Nat.gcd b a := by rw [← Nat.gcd_rec]
    _ = Nat.gcd a b := Nat.gcd_comm _ _

theorem bezout_step_identity (x y a q r B : Int) (h : a = r + B * q) :
    y * a + (x - q * y) * B = x * B + y * r := by
  grind [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm,
    Int.add_assoc, Int.add_comm, Int.sub_eq_add_neg]

def bezout_exists_proof (a b : Nat) :
    Exists fun x : Int =>
      Exists fun y : Int =>
        x * (a : Int) + y * (b : Int) = (Nat.gcd a b : Int) :=
  match b with
  | 0 => by
      exact ⟨1, 0, by simp⟩
  | b + 1 => by
      rcases bezout_exists_proof (b + 1) (a % (b + 1)) with
        ⟨x, y, hxy⟩
      refine ⟨y, x - ((a / (b + 1) : Nat) : Int) * y, ?_⟩
      have hdiv :
          (a : Int) = ((a % (b + 1) : Nat) : Int) +
            (b + 1 : Int) * ((a / (b + 1) : Nat) : Int) := by
        symm
        exact_mod_cast (Nat.mod_add_div a (b + 1))
      rw [gcd_remainder_swap] at hxy
      calc
        y * (a : Int) +
              (x - ((a / (b + 1) : Nat) : Int) * y) * (b + 1 : Int) =
            x * (b + 1 : Int) +
              y * ((a % (b + 1) : Nat) : Int) := by
          exact bezout_step_identity x y (a : Int)
            ((a / (b + 1) : Nat) : Int)
            ((a % (b + 1) : Nat) : Int) (b + 1 : Int) hdiv
        _ = (Nat.gcd a (b + 1) : Int) := hxy
termination_by b
decreasing_by
  exact Nat.mod_lt _ (by omega)

theorem bezout_exists (a b : Nat) :
    Exists fun x : Int =>
      Exists fun y : Int =>
        x * (a : Int) + y * (b : Int) = (Nat.gcd a b : Int) := by
  exact bezout_exists_proof a b

theorem euclideanGcd_bezout_exists (a b : Nat) :
    Exists fun x : Int =>
      Exists fun y : Int =>
        x * (a : Int) + y * (b : Int) = (euclideanGcd a b : Int) := by
  obtain ⟨x, y, hxy⟩ := bezout_exists a b
  refine ⟨x, y, ?_⟩
  rw [euclideanGcd_eq_gcd]
  exact hxy

structure QInterval where
  lo : Rat
  hi : Rat
deriving Repr, DecidableEq

namespace QInterval

def width (I : QInterval) : Rat := I.hi - I.lo
def midpoint (I : QInterval) : Rat := (I.lo + I.hi) / 2
def Overlaps (I J : QInterval) : Prop := I.lo <= J.hi /\ J.lo <= I.hi
def CloseAt (I J : QInterval) (eps : QPos) : Prop :=
  Overlaps I J /\ I.width <= eps.val /\ J.width <= eps.val
/-- Two interval enclosures are within a requested tolerance.  Unlike
`CloseAt`, this permits distinct nearby values: the gap between either lower
endpoint and the other upper endpoint is at most `eps`, while both evaluation
boxes themselves have width at most `eps`. -/
def NearAt (I J : QInterval) (eps : QPos) : Prop :=
  I.lo <= J.hi + eps.val /\ J.lo <= I.hi + eps.val /\
    I.width <= eps.val /\ J.width <= eps.val
/-- `outer.ContainsInterval inner` says the rational interval `outer` encloses
the whole rational interval `inner`. -/
def ContainsInterval (outer inner : QInterval) : Prop :=
  outer.lo <= inner.lo /\ inner.hi <= outer.hi
def overlaps (I J : QInterval) : Bool := decide (I.lo <= J.hi /\ J.lo <= I.hi)
def closeAt (I J : QInterval) (eps : QPos) : Bool :=
  decide (I.lo <= J.hi /\ J.lo <= I.hi /\ I.width <= eps.val /\ J.width <= eps.val)
def widthOk (I : QInterval) (eps : QPos) : Bool := decide (0 <= I.width /\ I.width <= eps.val)

/-- The smallest rational interval containing both input intervals. -/
def hull (I J : QInterval) : QInterval :=
  { lo := min I.lo J.lo, hi := max I.hi J.hi }

/-- The common part of two rational intervals.  Unlike `hull`, this is only
ordered when the two inputs have a common subinterval; clients prove that
fact explicitly rather than silently replacing an empty intersection. -/
def intersection (I J : QInterval) : QInterval :=
  { lo := max I.lo J.lo, hi := min I.hi J.hi }

theorem hull_contains_left (I J : QInterval) : (hull I J).ContainsInterval I := by
  unfold ContainsInterval hull
  grind

theorem hull_contains_right (I J : QInterval) : (hull I J).ContainsInterval J := by
  unfold ContainsInterval hull
  grind

theorem hull_least {K I J : QInterval}
    (hI : K.ContainsInterval I) (hJ : K.ContainsInterval J) :
    K.ContainsInterval (hull I J) := by
  unfold ContainsInterval hull at *
  grind

theorem intersection_contains
    {I J K : QInterval}
    (hI : I.ContainsInterval K) (hJ : J.ContainsInterval K) :
    (intersection I J).ContainsInterval K := by
  unfold ContainsInterval intersection at *
  grind

theorem intersection_contained_left (I J : QInterval) :
    I.lo <= (intersection I J).lo /\
      (intersection I J).hi <= I.hi := by
  unfold intersection
  grind

theorem intersection_contained_right (I J : QInterval) :
    J.lo <= (intersection I J).lo /\
      (intersection I J).hi <= J.hi := by
  unfold intersection
  grind

/-- Overlapping ordered rational intervals have an ordered explicit
intersection.  The intersection is data, not a choice of a point. -/
theorem intersection_ordered_of_overlaps
    {I J : QInterval}
    (hI : I.lo <= I.hi) (hJ : J.lo <= J.hi)
    (hover : I.Overlaps J) :
    (intersection I J).lo <= (intersection I J).hi := by
  unfold intersection Overlaps at *
  grind

theorem width_le_of_contains {outer inner : QInterval}
    (h : outer.ContainsInterval inner) :
    inner.width <= outer.width := by
  change outer.lo <= inner.lo /\ inner.hi <= outer.hi at h
  change inner.hi - inner.lo <= outer.hi - outer.lo
  grind [Rat.sub_eq_add_neg]

theorem hull_width_le_add_of_overlaps
    {I J : QInterval}
    (hI : 0 <= I.width) (hJ : 0 <= J.width)
    (hover : I.Overlaps J) :
    (hull I J).width <= I.width + J.width := by
  unfold width hull Overlaps at *
  grind [Rat.sub_eq_add_neg]

/-- Widen an interval by a rational radius on both sides. -/
def expand (I : QInterval) (radius : Rat) : QInterval :=
  { lo := I.lo - radius, hi := I.hi + radius }

theorem expand_width (I : QInterval) (radius : Rat) :
    (expand I radius).width = I.width + 2 * radius := by
  unfold expand width
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-- If two intervals overlap, widening the first by at least the width of the
second contains the entire second interval. -/
theorem expand_contains_right_of_overlaps
    {I J : QInterval} {radius : Rat}
    (hover : I.Overlaps J) (hradius : J.width <= radius) :
    (expand I radius).ContainsInterval J := by
  unfold expand ContainsInterval width Overlaps at *
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-- Quantitative nearness gives a concrete enclosure after widening the first
box by twice the tolerance.  One tolerance covers the gap between the two
boxes and the other covers the width of the right box. -/
theorem expand_contains_right_of_near
    {I J : QInterval} {eps : QPos}
    (hnear : I.NearAt J eps) :
    (expand I (2 * eps.val)).ContainsInterval J := by
  unfold NearAt width at hnear
  unfold ContainsInterval expand
  rcases hnear with ⟨hIJ, hJI, _hIwidth, hJwidth⟩
  constructor <;> grind [Rat.sub_eq_add_neg]

def inv (I : QInterval) : QInterval :=
  if 0 < I.lo then
    { lo := 1 / I.hi, hi := 1 / I.lo }
  else if I.hi < 0 then
    { lo := 1 / I.hi, hi := 1 / I.lo }
  else
    { lo := -1, hi := 1 }

def decimalScale (digits : Nat) : Int :=
  Int.ofNat (10 ^ digits)

def zeroPad (digits : Nat) (s : String) : String :=
  String.ofList (List.replicate (digits - s.length) '0') ++ s

/-- Decimal display helper for `#eval!` output.  This is only presentation;
the stored interval remains rational. -/
def ratDecimal (digits : Nat) (q : Rat) : String :=
  let qpos := if q < 0 then -q else q
  let scale := decimalScale digits
  let scaled := Int.ediv (qpos.num * scale) (Int.ofNat qpos.den)
  let whole := Int.ediv scaled scale
  let frac := Int.emod scaled scale
  let sign := if q < 0 then "-" else ""
  sign ++ toString whole ++
    if digits = 0 then "" else "." ++ zeroPad digits (toString frac)

def decimal (digits : Nat) (I : QInterval) : String :=
  "[" ++ ratDecimal digits I.lo ++ ", " ++ ratDecimal digits I.hi ++
    "] width=" ++ ratDecimal digits I.width

def trimDecimalString (s : String) : String :=
  let chars := s.toList
  if chars.contains '.' then
    let trimmed := chars.reverse.dropWhile (fun c => c = '0')
    let trimmed := trimmed.dropWhile (fun c => c = '.')
    let out := String.ofList trimmed.reverse
    if out = "-0" then "0" else out
  else
    s

def ratDecimalCompact (digits : Nat) (q : Rat) : String :=
  trimDecimalString (ratDecimal digits q)

def ensureDecimalPoint (s : String) : String :=
  if s.toList.contains '.' then s else s ++ ".0"

def decimalExactAt (digits : Nat) (q : Rat) : Bool :=
  Int.emod (q.num * decimalScale digits) (Int.ofNat q.den) = 0

def scaledDecimalFixed (digits : Nat) (scaled : Int) : String :=
  let scale := decimalScale digits
  let scaledAbs := if scaled < 0 then -scaled else scaled
  let whole := Int.ediv scaledAbs scale
  let frac := Int.emod scaledAbs scale
  let sign := if scaled < 0 then "-" else ""
  sign ++ toString whole ++
    if digits = 0 then "" else "." ++ zeroPad digits (toString frac)

def floorDecimalFixed (digits : Nat) (q : Rat) : String :=
  scaledDecimalFixed digits
    (Int.ediv (q.num * decimalScale digits) (Int.ofNat q.den))

def ceilDecimalFixed (digits : Nat) (q : Rat) : String :=
  scaledDecimalFixed digits
    (-Int.ediv (-(q.num * decimalScale digits)) (Int.ofNat q.den))

def firstDifferingPrefixLength : List Char -> List Char -> Nat -> Nat
  | [], _, i => i
  | _, [], i => i
  | a :: as, b :: bs, i =>
      if a = b then
        firstDifferingPrefixLength as bs (i + 1)
      else
        i + 1

def digitsForDenAux (den : Nat) : Nat -> Nat -> Nat
  | 0, d => d
  | fuel + 1, d =>
      if den <= 10 ^ d then
        d
      else
        digitsForDenAux den fuel (d + 1)

def digitsForDen (den : Nat) : Nat :=
  digitsForDenAux den den 0

def boundedDigitsForDen (budget den : Nat) : Nat :=
  Nat.min budget (digitsForDen den)

def decimalPlacesInPrefixAux : List Char -> Bool -> Nat -> Nat
  | [], _seenDecimal, d => d
  | c :: cs, seenDecimal, d =>
      if c = '.' then
        decimalPlacesInPrefixAux cs true d
      else if seenDecimal then
        decimalPlacesInPrefixAux cs true (d + 1)
      else
        decimalPlacesInPrefixAux cs false d

def decimalPlacesInPrefix (s : String) (n : Nat) : Nat :=
  decimalPlacesInPrefixAux (s.toList.take n) false 0

def endpointDisplayDigits (lo hi : Rat) : Nat :=
  let width := hi - lo
  let highDigits := digitsForDen width.den
  let lower := ratDecimal highDigits lo
  let upper := ratDecimal highDigits hi
  let n := firstDifferingPrefixLength lower.toList upper.toList 0
  Nat.max 2 (decimalPlacesInPrefix lower n + 1)

def endpointDecimalsToFirstDifference (lo hi : Rat) : String × String :=
  let digits := endpointDisplayDigits lo hi
  let lower := ratDecimal digits lo
  let upper := ratDecimal digits hi
  let lower := trimDecimalString lower
  let upper := trimDecimalString upper
  let lower := if lo < 0 && lower = "0" && !decimalExactAt digits lo then "-0" else lower
  let upper := if hi < 0 && upper = "0" && !decimalExactAt digits hi then "-0" else upper
  let lower :=
    if decimalExactAt digits lo then lower else ensureDecimalPoint lower ++ "..."
  let upper :=
    if decimalExactAt digits hi then upper else ensureDecimalPoint upper ++ "..."
  (lower, upper)

def digitString (d : Nat) : String := toString d

def digitsString : List Nat -> String
  | [] => ""
  | d :: ds => digitString d ++ digitsString ds

def findRemainder (r : Nat) : List Nat -> Nat -> Option Nat
  | [], _ => none
  | s :: seen, i =>
      if r = s then
        some i
      else
        findRemainder r seen (i + 1)

def repeatingFractionAux (den : Nat) : Nat -> Nat -> List Nat -> List Nat -> String
  | 0, _rem, _seen, digits => digitsString digits ++ "..."
  | fuel + 1, rem, seen, digits =>
      if rem = 0 then
        digitsString digits
      else
        match findRemainder rem seen 0 with
        | some i =>
            digitsString (digits.take i) ++ "(" ++ digitsString (digits.drop i) ++ ")"
        | none =>
            let rem10 := rem * 10
            let digit := rem10 / den
            let rem' := rem10 % den
            repeatingFractionAux den fuel rem' (seen ++ [rem]) (digits ++ [digit])

def ratRepeatingDecimal (q : Rat) : String :=
  let den := q.den
  let numAbs := q.num.natAbs
  let whole := numAbs / den
  let rem := numAbs % den
  let sign := if q < 0 then "-" else ""
  let frac := repeatingFractionAux den (den + 1) rem [] []
  if frac = "" then
    sign ++ toString whole
  else
    sign ++ toString whole ++ "." ++ frac

def scientificNormalizeAux : Nat -> Rat -> Int -> Rat × Int
  | 0, q, e => (q, e)
  | fuel + 1, q, e =>
      if 10 <= q then
        scientificNormalizeAux fuel (q / 10) (e + 1)
      else if q < 1 then
        scientificNormalizeAux fuel (q * 10) (e - 1)
      else
        (q, e)

def scientificDecimal (q : Rat) : String :=
  if q = 0 then
    "0"
  else
    let qpos := if q < 0 then -q else q
    let normalized := scientificNormalizeAux 10000 qpos 0
    let sign := if q < 0 then "-" else ""
    sign ++ ratDecimalCompact 3 normalized.1 ++ "e" ++ toString normalized.2

def fixedWidthDecimalDigits (exponent : Int) : Nat :=
  if exponent < 0 then
    Int.toNat (-exponent) + 3
  else
    3

def widthDecimal (q : Rat) : String :=
  if q = 0 then
    "0"
  else
    let qpos := if q < 0 then -q else q
    let normalized := scientificNormalizeAux 10000 qpos 0
    if -6 <= normalized.2 && normalized.2 <= 12 then
      ratDecimalCompact (fixedWidthDecimalDigits normalized.2) q
    else
      scientificDecimal q

def display (I : QInterval) : String :=
  if I.lo = I.hi then
    let q := I.lo
    "[" ++ ratRepeatingDecimal q ++ ", " ++ ratRepeatingDecimal q ++ "] width=0"
  else
    let endpoints := endpointDecimalsToFirstDifference I.lo I.hi
    "[" ++ endpoints.1 ++ ", " ++ endpoints.2 ++ "] width=" ++
      widthDecimal I.width

end QInterval

def qabs (x : Rat) : Rat := if x < 0 then -x else x

theorem qabs_nonneg (x : Rat) : 0 <= qabs x := by
  unfold qabs
  by_cases hneg : x < 0
  · simp [hneg]
    grind
  · simp [hneg]
    grind

theorem qabs_pos_of_ne {x : Rat} (hx : Not (x = 0)) :
    0 < qabs x := by
  unfold qabs
  by_cases hneg : x < 0
  · simp [hneg]
    grind
  · simp [hneg]
    grind

/-- Absolute value preserves a nonnegative rational. -/
theorem qabs_eq_self_of_nonneg {x : Rat} (hx : 0 <= x) :
    qabs x = x := by
  unfold qabs
  by_cases hneg : x < 0
  · simp [hneg]
    grind
  · simp [hneg]

/-- Absolute value negates a nonpositive rational. -/
theorem qabs_eq_neg_of_nonpos {x : Rat} (hx : x <= 0) :
    qabs x = -x := by
  unfold qabs
  by_cases hneg : x < 0
  · simp [hneg]
  · have hzero : x = 0 := by grind
    simp [hzero]

theorem qabs_neg (x : Rat) : qabs (-x) = qabs x := by
  by_cases hx : 0 <= x
  · have hnx : -x <= 0 := by grind
    rw [qabs_eq_neg_of_nonpos hnx, qabs_eq_self_of_nonneg hx]
    grind
  · have hxl : x <= 0 := by grind
    have hnx : 0 <= -x := by grind
    rw [qabs_eq_self_of_nonneg hnx, qabs_eq_neg_of_nonpos hxl]

/- A small product-order helper used by finite interval estimates. -/
theorem rat_mul_le_mul_of_nonneg {a b c d : Rat}
    (ha : 0 <= a) (hab : a <= b) (hc : 0 <= c) (hcd : c <= d) :
    a * c <= b * d := by
  calc
    a * c <= b * c := Rat.mul_le_mul_of_nonneg_right hab hc
    _ <= b * d := Rat.mul_le_mul_of_nonneg_left hcd (by grind)

theorem rat_mul_le_mul_of_nonpos_left {a b c : Rat}
    (hab : a <= b) (hc : c <= 0) : c * b <= c * a := by
  have hnc : 0 <= -c := by grind
  have h := Rat.mul_le_mul_of_nonneg_left hab hnc
  grind [Rat.neg_mul]

theorem qabs_mul (x y : Rat) : qabs (x * y) = qabs x * qabs y := by
  by_cases hx : 0 <= x
  · by_cases hy : 0 <= y
    · rw [qabs_eq_self_of_nonneg (Rat.mul_nonneg hx hy),
        qabs_eq_self_of_nonneg hx, qabs_eq_self_of_nonneg hy]
    · have hyl : y <= 0 := by grind
      have hny : 0 <= -y := by grind
      have hxy : x * y <= 0 := by
        have h : 0 <= x * (-y) := Rat.mul_nonneg hx hny
        grind [Rat.mul_neg]
      rw [qabs_eq_neg_of_nonpos hxy,
        qabs_eq_self_of_nonneg hx, qabs_eq_neg_of_nonpos hyl]
      grind [Rat.mul_neg]
  · have hxl : x <= 0 := by grind
    have hnx : 0 <= -x := by grind
    by_cases hy : 0 <= y
    · have hxy : x * y <= 0 := by
        have h : 0 <= (-x) * y := Rat.mul_nonneg hnx hy
        grind [Rat.neg_mul]
      rw [qabs_eq_neg_of_nonpos hxy,
        qabs_eq_neg_of_nonpos hxl, qabs_eq_self_of_nonneg hy]
      grind [Rat.neg_mul]
    · have hyl : y <= 0 := by grind
      have hny : 0 <= -y := by grind
      have hxy : 0 <= x * y := by
        calc
          0 <= (-x) * (-y) := Rat.mul_nonneg hnx hny
          _ = x * y := by grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
      rw [qabs_eq_self_of_nonneg hxy,
        qabs_eq_neg_of_nonpos hxl, qabs_eq_neg_of_nonpos hyl]
      grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

theorem rat_add_le_add {a b c d : Rat}
    (hab : a <= b) (hcd : c <= d) : a + c <= b + d := by
  calc
    a + c <= b + c := (Rat.add_le_add_right).2 hab
    _ <= b + d := (Rat.add_le_add_left).2 hcd

theorem self_le_qabs (x : Rat) : x <= qabs x := by
  unfold qabs
  by_cases hneg : x < 0
  · simp [hneg]
    grind
  · simp [hneg]

theorem neg_qabs_le_self (x : Rat) : -qabs x <= x := by
  unfold qabs
  by_cases hneg : x < 0
  · simp [hneg]
  · simp [hneg]
    grind

theorem qabs_le_of_neg_le_le {x b : Rat}
    (hlo : -b <= x) (hhi : x <= b) : qabs x <= b := by
  unfold qabs
  by_cases hneg : x < 0
  · simp [hneg]
    grind
  · simp [hneg]
    exact hhi

theorem qabs_add_le (x y : Rat) : qabs (x + y) <= qabs x + qabs y := by
  apply qabs_le_of_neg_le_le
  · calc
      -(qabs x + qabs y) = -qabs x + -qabs y := by grind
      _ <= x + y := rat_add_le_add (neg_qabs_le_self x) (neg_qabs_le_self y)
  · exact rat_add_le_add (self_le_qabs x) (self_le_qabs y)

theorem qabs_add_le_three (x y z : Rat) :
    qabs (x + y + z) <= qabs x + qabs y + qabs z := by
  calc
    qabs (x + y + z) <= qabs (x + y) + qabs z := qabs_add_le (x + y) z
    _ <= (qabs x + qabs y) + qabs z := by
      exact (Rat.add_le_add_right).2 (qabs_add_le x y)
    _ = qabs x + qabs y + qabs z := by rfl

def ratListSum : List Rat -> Rat
  | [] => 0
  | x :: xs => x + ratListSum xs

def ratListAbsSum : List Rat -> Rat
  | [] => 0
  | x :: xs => qabs x + ratListAbsSum xs

theorem ratListSum_append (xs ys : List Rat) :
    ratListSum (xs ++ ys) = ratListSum xs + ratListSum ys := by
  induction xs with
  | nil => simp [ratListSum] <;> grind
  | cons x xs ih =>
      simp only [List.cons_append, ratListSum]
      rw [ih]
      grind

theorem ratListAbsSum_append (xs ys : List Rat) :
    ratListAbsSum (xs ++ ys) = ratListAbsSum xs + ratListAbsSum ys := by
  induction xs with
  | nil => simp [ratListAbsSum] <;> grind
  | cons x xs ih =>
      simp only [List.cons_append, ratListAbsSum]
      rw [ih]
      grind

theorem qabs_ratListSum_le (xs : List Rat) :
    qabs (ratListSum xs) <= ratListAbsSum xs := by
  induction xs with
  | nil => simp [ratListSum, ratListAbsSum, qabs]
  | cons x xs ih =>
      calc
        qabs (ratListSum (x :: xs)) =
            qabs (x + ratListSum xs) := by rfl
        _ <= qabs x + qabs (ratListSum xs) := qabs_add_le x (ratListSum xs)
        _ <= qabs x + ratListAbsSum xs := by
          exact (Rat.add_le_add_left).2 ih
        _ = ratListAbsSum (x :: xs) := by rfl

theorem qabs_sub_le (x y : Rat) : qabs (x - y) <= qabs x + qabs y := by
  rw [show x - y = x + (-y) by grind [Rat.sub_eq_add_neg]]
  calc
    qabs (x + -y) <= qabs x + qabs (-y) := qabs_add_le x (-y)
    _ = qabs x + qabs y := by rw [qabs_neg]

theorem rat_square_nonneg_basic (x : Rat) : 0 <= x * x := by
  by_cases hx : 0 <= x
  · exact Rat.mul_nonneg hx hx
  · have hxneg : x <= 0 := by grind
    have hq : qabs x = -x := qabs_eq_neg_of_nonpos hxneg
    have hx' : x = -qabs x := by grind
    rw [hx']
    grind [Rat.mul_nonneg (qabs_nonneg x) (qabs_nonneg x)]

theorem am_gm_square_bound (a b : Rat) :
    4 * a * b <= (a + b) * (a + b) := by
  have hsq := rat_square_nonneg_basic (a - b)
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem am_gm_rational_half {a b : Rat} :
    a * b <= ((a + b) / 2) ^ 2 := by
  rw [Rat.div_def]
  apply Rat.le_of_mul_le_mul_right (c := (4 : Rat))
  · have h := am_gm_square_bound a b
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
      Rat.pow_succ, Rat.mul_inv_cancel]
  · decide +kernel

theorem am_gm_rational_half_eq_iff {a b : Rat} :
    a * b = ((a + b) / 2) ^ 2 ↔ a = b := by
  constructor
  · intro h
    have hsq : (a - b) * (a - b) = 0 := by
      rw [Rat.div_def] at h
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ, Rat.mul_inv_cancel]
    rcases Rat.mul_eq_zero.mp hsq with hzero | hzero
    · grind
    · grind
  · intro hab
    subst b
    rw [Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
      Rat.pow_succ, Rat.mul_inv_cancel]

/-! A finite four-variable AM--GM certificate, assembled from the checked
two-variable inequality by pairing the inputs. -/

theorem am_gm_four {a b c d : Rat}
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c) (hd : 0 <= d) :
    a * b * c * d <= ((a + b + c + d) / 4) ^ 4 := by
  let x : Rat := (a + b) / 2
  let y : Rat := (c + d) / 2
  have hx : 0 <= x := by
    dsimp [x]
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by grind) (by decide +kernel)
  have hy : 0 <= y := by
    dsimp [y]
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by grind) (by decide +kernel)
  have hab : a * b <= x ^ 2 := by
    simpa [x] using (am_gm_rational_half (a := a) (b := b))
  have hcd : c * d <= y ^ 2 := by
    simpa [y] using (am_gm_rational_half (a := c) (b := d))
  have hcd0 : 0 <= c * d := Rat.mul_nonneg hc hd
  have hxy : x * y <= ((x + y) / 2) ^ 2 :=
    am_gm_rational_half (a := x) (b := y)
  have hxy0 : 0 <= x * y := Rat.mul_nonneg hx hy
  have hxyUpper : 0 <= ((x + y) / 2) ^ 2 := by
    simpa [Rat.pow_succ] using rat_square_nonneg_basic ((x + y) / 2)
  have hx2 : 0 <= x ^ 2 := by
    simpa [Rat.pow_succ] using rat_square_nonneg_basic x
  have hprod : a * b * (c * d) <= x ^ 2 * y ^ 2 := by
    calc
      a * b * (c * d) <= x ^ 2 * (c * d) := by
        exact Rat.mul_le_mul_of_nonneg_right hab hcd0
      _ <= x ^ 2 * y ^ 2 := by
        exact Rat.mul_le_mul_of_nonneg_left hcd hx2
  have hsquare : (x * y) ^ 2 <= (((x + y) / 2) ^ 2) ^ 2 := by
    calc
      (x * y) ^ 2 = (x * y) * (x * y) := by
        grind [Rat.pow_succ]
      _ <= ((x + y) / 2) ^ 2 * (x * y) :=
        Rat.mul_le_mul_of_nonneg_right hxy hxy0
      _ <= ((x + y) / 2) ^ 2 * ((x + y) / 2) ^ 2 :=
        Rat.mul_le_mul_of_nonneg_left hxy hxyUpper
      _ = (((x + y) / 2) ^ 2) ^ 2 := by
        grind [Rat.pow_succ, Rat.mul_assoc]
  have hpair : x ^ 2 * y ^ 2 <= (((x + y) / 2) ^ 2) ^ 2 := by
    calc
      x ^ 2 * y ^ 2 = (x * y) ^ 2 := by
        grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm]
      _ <= (((x + y) / 2) ^ 2) ^ 2 := hsquare
  calc
    a * b * c * d = a * b * (c * d) := by
      grind [Rat.mul_assoc]
    _ <= x ^ 2 * y ^ 2 := hprod
    _ <= (((x + y) / 2) ^ 2) ^ 2 := hpair
    _ = ((a + b + c + d) / 4) ^ 4 := by
      dsimp [x, y]
      rw [Rat.div_def]
      grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
        Rat.add_mul, Rat.mul_inv_cancel]

theorem cauchy_schwarz_2d (a b c d : Rat) :
    (a * b + c * d) ^ 2 <=
      (a * a + c * c) * (b * b + d * d) := by
  have hsq := rat_square_nonneg_basic (a * d - b * c)
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

theorem cauchy_schwarz_2d_eq_iff (a b c d : Rat) :
    (a * b + c * d) ^ 2 =
        (a * a + c * c) * (b * b + d * d) ↔
      a * d = b * c := by
  constructor
  · intro h
    have hsq : (a * d - b * c) * (a * d - b * c) = 0 := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
    rcases Rat.mul_eq_zero.mp hsq with hzero | hzero
    · grind
    · grind
  · intro h
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

theorem cauchy_schwarz_3d (a b c x y z : Rat) :
    (a * x + b * y + c * z) ^ 2 <=
      (a * a + b * b + c * c) * (x * x + y * y + z * z) := by
  have hxy := rat_square_nonneg_basic (a * y - b * x)
  have hxz := rat_square_nonneg_basic (a * z - c * x)
  have hyz := rat_square_nonneg_basic (b * z - c * y)
  have hsum : 0 <=
      (a * y - b * x) * (a * y - b * x) +
        (a * z - c * x) * (a * z - c * x) +
        (b * z - c * y) * (b * z - c * y) := by
    grind
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

theorem cauchy_schwarz_4d (a b c d w x y z : Rat) :
    (a * w + b * x + c * y + d * z) ^ 2 <=
      (a * a + b * b + c * c + d * d) *
        (w * w + x * x + y * y + z * z) := by
  have hab := rat_square_nonneg_basic (a * x - b * w)
  have hac := rat_square_nonneg_basic (a * y - c * w)
  have had := rat_square_nonneg_basic (a * z - d * w)
  have hbc := rat_square_nonneg_basic (b * y - c * x)
  have hbd := rat_square_nonneg_basic (b * z - d * x)
  have hcd := rat_square_nonneg_basic (c * z - d * y)
  have hsum : 0 <=
      (a * x - b * w) * (a * x - b * w) +
        (a * y - c * w) * (a * y - c * w) +
        (a * z - d * w) * (a * z - d * w) +
        (b * y - c * x) * (b * y - c * x) +
        (b * z - d * x) * (b * z - d * x) +
        (c * z - d * y) * (c * z - d * y) := by
    grind
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

theorem cauchy_schwarz_5d
    (a b c d e w x y z u : Rat) :
    (a * w + b * x + c * y + d * z + e * u) ^ 2 <=
      (a * a + b * b + c * c + d * d + e * e) *
        (w * w + x * x + y * y + z * z + u * u) := by
  have hab := rat_square_nonneg_basic (a * x - b * w)
  have hac := rat_square_nonneg_basic (a * y - c * w)
  have had := rat_square_nonneg_basic (a * z - d * w)
  have hae := rat_square_nonneg_basic (a * u - e * w)
  have hbc := rat_square_nonneg_basic (b * y - c * x)
  have hbd := rat_square_nonneg_basic (b * z - d * x)
  have hbe := rat_square_nonneg_basic (b * u - e * x)
  have hcd := rat_square_nonneg_basic (c * z - d * y)
  have hce := rat_square_nonneg_basic (c * u - e * y)
  have hde := rat_square_nonneg_basic (d * u - e * z)
  have hsum : 0 <=
      (a * x - b * w) * (a * x - b * w) +
        (a * y - c * w) * (a * y - c * w) +
        (a * z - d * w) * (a * z - d * w) +
        (a * u - e * w) * (a * u - e * w) +
        (b * y - c * x) * (b * y - c * x) +
        (b * z - d * x) * (b * z - d * x) +
        (b * u - e * x) * (b * u - e * x) +
        (c * z - d * y) * (c * z - d * y) +
        (c * u - e * y) * (c * u - e * y) +
        (d * u - e * z) * (d * u - e * z) := by
    grind
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

theorem cauchy_schwarz_6d
    (a b c d e f w x y z u v : Rat) :
    (a * w + b * x + c * y + d * z + e * u + f * v) ^ 2 <=
      (a * a + b * b + c * c + d * d + e * e + f * f) *
        (w * w + x * x + y * y + z * z + u * u + v * v) := by
  have hab := rat_square_nonneg_basic (a * x - b * w)
  have hac := rat_square_nonneg_basic (a * y - c * w)
  have had := rat_square_nonneg_basic (a * z - d * w)
  have hae := rat_square_nonneg_basic (a * u - e * w)
  have haf := rat_square_nonneg_basic (a * v - f * w)
  have hbc := rat_square_nonneg_basic (b * y - c * x)
  have hbd := rat_square_nonneg_basic (b * z - d * x)
  have hbe := rat_square_nonneg_basic (b * u - e * x)
  have hbf := rat_square_nonneg_basic (b * v - f * x)
  have hcd := rat_square_nonneg_basic (c * z - d * y)
  have hce := rat_square_nonneg_basic (c * u - e * y)
  have hcf := rat_square_nonneg_basic (c * v - f * y)
  have hde := rat_square_nonneg_basic (d * u - e * z)
  have hdf := rat_square_nonneg_basic (d * v - f * z)
  have hef := rat_square_nonneg_basic (e * v - f * u)
  have hsum : 0 <=
      (a * x - b * w) * (a * x - b * w) +
        (a * y - c * w) * (a * y - c * w) +
        (a * z - d * w) * (a * z - d * w) +
        (a * u - e * w) * (a * u - e * w) +
        (a * v - f * w) * (a * v - f * w) +
        (b * y - c * x) * (b * y - c * x) +
        (b * z - d * x) * (b * z - d * x) +
        (b * u - e * x) * (b * u - e * x) +
        (b * v - f * x) * (b * v - f * x) +
        (c * z - d * y) * (c * z - d * y) +
        (c * u - e * y) * (c * u - e * y) +
        (c * v - f * y) * (c * v - f * y) +
        (d * u - e * z) * (d * u - e * z) +
        (d * v - f * z) * (d * v - f * z) +
        (e * v - f * u) * (e * v - f * u) := by
    grind
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

/-- A finite equality witness for the 6D certificate: if all fifteen
pairwise minors vanish, the two rational coordinate lists are collinear and
Cauchy--Schwarz is attained. -/
theorem cauchy_schwarz_6d_eq_of_minors
    (a b c d e f w x y z u v : Rat)
    (hab : a * x = b * w) (hac : a * y = c * w)
    (had : a * z = d * w) (hae : a * u = e * w)
    (haf : a * v = f * w) (hbc : b * y = c * x)
    (hbd : b * z = d * x) (hbe : b * u = e * x)
    (hbf : b * v = f * x) (hcd : c * z = d * y)
    (hce : c * u = e * y) (hcf : c * v = f * y)
    (hde : d * u = e * z) (hdf : d * v = f * z)
    (hef : e * v = f * u) :
    (a * w + b * x + c * y + d * z + e * u + f * v) ^ 2 =
      (a * a + b * b + c * c + d * d + e * e + f * f) *
        (w * w + x * x + y * y + z * z + u * u + v * v) := by
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

theorem cauchy_schwarz_5d_eq_iff
    (a b c d e w x y z u : Rat) :
    (a * w + b * x + c * y + d * z + e * u) ^ 2 =
        (a * a + b * b + c * c + d * d + e * e) *
          (w * w + x * x + y * y + z * z + u * u) ↔
      a * x = b * w ∧ a * y = c * w ∧ a * z = d * w ∧
        a * u = e * w ∧ b * y = c * x ∧ b * z = d * x ∧
        b * u = e * x ∧ c * z = d * y ∧ c * u = e * y ∧
        d * u = e * z := by
  have hab := rat_square_nonneg_basic (a * x - b * w)
  have hac := rat_square_nonneg_basic (a * y - c * w)
  have had := rat_square_nonneg_basic (a * z - d * w)
  have hae := rat_square_nonneg_basic (a * u - e * w)
  have hbc := rat_square_nonneg_basic (b * y - c * x)
  have hbd := rat_square_nonneg_basic (b * z - d * x)
  have hbe := rat_square_nonneg_basic (b * u - e * x)
  have hcd := rat_square_nonneg_basic (c * z - d * y)
  have hce := rat_square_nonneg_basic (c * u - e * y)
  have hde := rat_square_nonneg_basic (d * u - e * z)
  constructor
  · intro h
    have hab0 : (a * x - b * w) * (a * x - b * w) = 0 := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
    have hac0 : (a * y - c * w) * (a * y - c * w) = 0 := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
    have had0 : (a * z - d * w) * (a * z - d * w) = 0 := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
    have hae0 : (a * u - e * w) * (a * u - e * w) = 0 := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
    have hbc0 : (b * y - c * x) * (b * y - c * x) = 0 := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
    have hbd0 : (b * z - d * x) * (b * z - d * x) = 0 := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
    have hbe0 : (b * u - e * x) * (b * u - e * x) = 0 := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
    have hcd0 : (c * z - d * y) * (c * z - d * y) = 0 := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
    have hce0 : (c * u - e * y) * (c * u - e * y) = 0 := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
    have hde0 : (d * u - e * z) * (d * u - e * z) = 0 := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
    have hab' : a * x = b * w := by
      rcases Rat.mul_eq_zero.mp hab0 with hzero | hzero <;> grind
    have hac' : a * y = c * w := by
      rcases Rat.mul_eq_zero.mp hac0 with hzero | hzero <;> grind
    have had' : a * z = d * w := by
      rcases Rat.mul_eq_zero.mp had0 with hzero | hzero <;> grind
    have hae' : a * u = e * w := by
      rcases Rat.mul_eq_zero.mp hae0 with hzero | hzero <;> grind
    have hbc' : b * y = c * x := by
      rcases Rat.mul_eq_zero.mp hbc0 with hzero | hzero <;> grind
    have hbd' : b * z = d * x := by
      rcases Rat.mul_eq_zero.mp hbd0 with hzero | hzero <;> grind
    have hbe' : b * u = e * x := by
      rcases Rat.mul_eq_zero.mp hbe0 with hzero | hzero <;> grind
    have hcd' : c * z = d * y := by
      rcases Rat.mul_eq_zero.mp hcd0 with hzero | hzero <;> grind
    have hce' : c * u = e * y := by
      rcases Rat.mul_eq_zero.mp hce0 with hzero | hzero <;> grind
    have hde' : d * u = e * z := by
      rcases Rat.mul_eq_zero.mp hde0 with hzero | hzero <;> grind
    exact ⟨hab', hac', had', hae', hbc', hbd', hbe', hcd', hce', hde'⟩
  · rintro ⟨hab', hac', had', hae', hbc', hbd', hbe', hcd', hce', hde'⟩
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

theorem cauchy_schwarz_4d_eq_iff (a b c d w x y z : Rat) :
    (a * w + b * x + c * y + d * z) ^ 2 =
        (a * a + b * b + c * c + d * d) *
          (w * w + x * x + y * y + z * z) ↔
      a * x = b * w ∧ a * y = c * w ∧ a * z = d * w ∧
        b * y = c * x ∧ b * z = d * x ∧ c * z = d * y := by
  have hab := rat_square_nonneg_basic (a * x - b * w)
  have hac := rat_square_nonneg_basic (a * y - c * w)
  have had := rat_square_nonneg_basic (a * z - d * w)
  have hbc := rat_square_nonneg_basic (b * y - c * x)
  have hbd := rat_square_nonneg_basic (b * z - d * x)
  have hcd := rat_square_nonneg_basic (c * z - d * y)
  constructor
  · intro h
    have hab0 : (a * x - b * w) * (a * x - b * w) = 0 := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
    have hac0 : (a * y - c * w) * (a * y - c * w) = 0 := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
    have had0 : (a * z - d * w) * (a * z - d * w) = 0 := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
    have hbc0 : (b * y - c * x) * (b * y - c * x) = 0 := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
    have hbd0 : (b * z - d * x) * (b * z - d * x) = 0 := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
    have hcd0 : (c * z - d * y) * (c * z - d * y) = 0 := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
    rcases Rat.mul_eq_zero.mp hab0 with hab0 | hab0
    · rcases Rat.mul_eq_zero.mp hac0 with hac0 | hac0
      · rcases Rat.mul_eq_zero.mp had0 with had0 | had0
        · rcases Rat.mul_eq_zero.mp hbc0 with hbc0 | hbc0
          · rcases Rat.mul_eq_zero.mp hbd0 with hbd0 | hbd0
            · rcases Rat.mul_eq_zero.mp hcd0 with hcd0 | hcd0
              · exact ⟨by grind, by grind, by grind, by grind, by grind, by grind⟩
              · exact ⟨by grind, by grind, by grind, by grind, by grind, by grind⟩
            · exact ⟨by grind, by grind, by grind, by grind, by grind, by grind⟩
          · exact ⟨by grind, by grind, by grind, by grind, by grind, by grind⟩
        · exact ⟨by grind, by grind, by grind, by grind, by grind, by grind⟩
      · exact ⟨by grind, by grind, by grind, by grind, by grind, by grind⟩
    · exact ⟨by grind, by grind, by grind, by grind, by grind, by grind⟩
  · rintro ⟨hab, hac, had, hbc, hbd, hcd⟩
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

theorem cauchy_schwarz_3d_eq_iff (a b c x y z : Rat) :
    (a * x + b * y + c * z) ^ 2 =
        (a * a + b * b + c * c) * (x * x + y * y + z * z) ↔
      a * y = b * x ∧ a * z = c * x ∧ b * z = c * y := by
  have hxy := rat_square_nonneg_basic (a * y - b * x)
  have hxz := rat_square_nonneg_basic (a * z - c * x)
  have hyz := rat_square_nonneg_basic (b * z - c * y)
  constructor
  · intro h
    have hxy0 : (a * y - b * x) * (a * y - b * x) = 0 := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
    have hxz0 : (a * z - c * x) * (a * z - c * x) = 0 := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
    have hyz0 : (b * z - c * y) * (b * z - c * y) = 0 := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]
    rcases Rat.mul_eq_zero.mp hxy0 with hxy0 | hxy0
    · rcases Rat.mul_eq_zero.mp hxz0 with hxz0 | hxz0
      · rcases Rat.mul_eq_zero.mp hyz0 with hyz0 | hyz0
        · grind
        · grind
      · rcases Rat.mul_eq_zero.mp hyz0 with hyz0 | hyz0 <;> grind
    · rcases Rat.mul_eq_zero.mp hxz0 with hxz0 | hxz0 <;> grind
  · rintro ⟨hxy, hxz, hyz⟩
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

theorem cramer_two_by_two (a b c d x y : Rat)
    (hdet : a * d - b * c ≠ 0) :
    let det := a * d - b * c
    let u := (x * d - b * y) / det
    let v := (a * y - x * c) / det
    a * u + b * v = x ∧ c * u + d * v = y := by
  dsimp
  rw [Rat.div_def, Rat.div_def]
  have hdet_inv : (a * d - b * c) * (a * d - b * c)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hdet
  constructor <;> grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem cramer_two_by_two_unique (a b c d x y u v : Rat)
    (hdet : a * d - b * c ≠ 0)
    (hu : a * u + b * v = x) (hv : c * u + d * v = y) :
    u = (x * d - b * y) / (a * d - b * c) ∧
      v = (a * y - x * c) / (a * d - b * c) := by
  rw [Rat.div_def, Rat.div_def]
  have hdet_inv : (a * d - b * c) * (a * d - b * c)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hdet
  constructor <;> grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem three_dvd_three_digit (a b c : Nat) :
    3 ∣ 100 * a + 10 * b + c ↔ 3 ∣ a + b + c := by
  omega

def decimalDigitSum : Nat -> Nat
  | 0 => 0
  | n + 1 =>
      if n + 1 < 10 then n + 1
      else (n + 1) % 10 + decimalDigitSum ((n + 1) / 10)
termination_by n => n
decreasing_by
  omega

theorem decimalDigitSum_succ_of_lt_ten (n : Nat) (hsmall : n + 1 < 10) :
    decimalDigitSum (n + 1) = n + 1 := by
  simp [decimalDigitSum, hsmall]

theorem decimalDigitSum_eq_self_of_lt_ten (n : Nat) (hsmall : n < 10) :
    decimalDigitSum n = n := by
  cases n with
  | zero => simp [decimalDigitSum]
  | succ n => exact decimalDigitSum_succ_of_lt_ten n hsmall

theorem decimalDigitSum_succ_of_not_lt_ten (n : Nat)
    (hlarge : ¬ n + 1 < 10) :
    decimalDigitSum (n + 1) =
      (n + 1) % 10 + decimalDigitSum ((n + 1) / 10) := by
  simp [decimalDigitSum, hlarge]

def decimalDigitSum_mod_three_proof : (n : Nat) ->
    decimalDigitSum n % 3 = n % 3
  | 0 => by simp [decimalDigitSum]
  | n + 1 => by
      by_cases hsmall : n + 1 < 10
      · simp [decimalDigitSum, hsmall]
      · have hlt : (n + 1) / 10 < n + 1 := by
          omega
        rw [decimalDigitSum]
        simp only [hsmall, ↓reduceIte]
        rw [Nat.add_mod, decimalDigitSum_mod_three_proof ((n + 1) / 10)]
        omega
termination_by n => n
decreasing_by
  omega

theorem decimalDigitSum_mod_three (n : Nat) :
    decimalDigitSum n % 3 = n % 3 := by
  exact decimalDigitSum_mod_three_proof n

def decimalDigitSum_mod_nine_proof : (n : Nat) ->
    decimalDigitSum n % 9 = n % 9
  | 0 => by simp [decimalDigitSum]
  | n + 1 => by
      by_cases hsmall : n + 1 < 10
      · simp [decimalDigitSum, hsmall]
      · have hlt : (n + 1) / 10 < n + 1 := by
          omega
        rw [decimalDigitSum]
        simp only [hsmall, ↓reduceIte]
        rw [Nat.add_mod, decimalDigitSum_mod_nine_proof ((n + 1) / 10)]
        omega
termination_by n => n
decreasing_by
  omega

theorem decimalDigitSum_mod_nine (n : Nat) :
    decimalDigitSum n % 9 = n % 9 := by
  exact decimalDigitSum_mod_nine_proof n

theorem three_dvd_iff_decimalDigitSum_dvd (n : Nat) :
    3 ∣ n ↔ 3 ∣ decimalDigitSum n := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero,
    decimalDigitSum_mod_three]

namespace QInterval

/-- The rational midpoint of an ordered interval stays in that interval. -/
theorem midpoint_mem {I : QInterval} (hI : I.lo <= I.hi) :
    I.lo <= I.midpoint /\ I.midpoint <= I.hi := by
  unfold midpoint
  constructor <;> grind [Rat.div_def]

/-- A point in an ordered interval lies within one interval width of its
rational midpoint.  The deliberately loose bound avoids any hidden division
or completed-real argument and is convenient for interval Lipschitz bounds. -/
theorem qabs_sub_midpoint_le_width {I : QInterval} {x : Rat}
    (hI : I.lo <= I.hi) (hxlo : I.lo <= x) (hxhi : x <= I.hi) :
    qabs (x - I.midpoint) <= I.width := by
  apply qabs_le_of_neg_le_le
  · unfold midpoint width
    grind [Rat.div_def]
  · unfold midpoint width
    grind [Rat.div_def]

/-- Midpoints of two overlapping ordered rational intervals differ by no
more than the sum of their widths.  This is the finite representative-change
estimate used when two equivalent raw evaluators expose different centers. -/
theorem qabs_midpoint_sub_midpoint_le_width_add_of_overlaps
    {I J : QInterval}
    (hI : I.lo <= I.hi) (hJ : J.lo <= J.hi) (hover : I.Overlaps J) :
    qabs (I.midpoint - J.midpoint) <= I.width + J.width := by
  apply qabs_le_of_neg_le_le
  · have hImid := midpoint_mem hI
    have hJmid := midpoint_mem hJ
    unfold Overlaps at hover
    unfold width
    grind [Rat.sub_eq_add_neg]
  · have hImid := midpoint_mem hI
    have hJmid := midpoint_mem hJ
    unfold Overlaps at hover
    unfold width
    grind [Rat.sub_eq_add_neg]

/-- The width of the smallest rational interval containing two rational
points is their rational absolute difference. -/
theorem endpointHull_width (x y : Rat) :
    ({ lo := min x y, hi := max x y } : QInterval).width = qabs (y - x) := by
  by_cases hxy : x <= y
  · have hdiff : 0 <= y - x := by grind [Rat.sub_eq_add_neg]
    rw [show min x y = x by grind, show max x y = y by grind,
      qabs_eq_self_of_nonneg hdiff]
    rfl
  · have hyx : y <= x := by grind
    have hdiff : y - x <= 0 := by grind [Rat.sub_eq_add_neg]
    rw [show min x y = y by grind, show max x y = x by grind,
      qabs_eq_neg_of_nonpos hdiff]
    unfold width
    grind [Rat.sub_eq_add_neg]

end QInterval

theorem qabs_sub_le_of_common_bounds {lo hi a b : Rat}
    (ha_lo : lo <= a) (ha_hi : a <= hi)
    (hb_lo : lo <= b) (hb_hi : b <= hi) :
    qabs (a - b) <= hi - lo := by
  unfold qabs
  by_cases hneg : a - b < 0
  · simp [hneg]
    grind
  · simp [hneg]
    grind

private theorem rat_intCast_eq_divInt_one (num : Int) :
    (num : Rat) = Rat.divInt num (1 : Int) := by
  change (num : Rat) = Rat.divInt num (Int.ofNat 1)
  rw [Rat.divInt.eq_1]
  change Rat.ofInt num = mkRat num 1
  rw [←Rat.normalize_self (Rat.ofInt num)]
  rfl

private theorem rat_natCast_eq_divInt_one (den : Nat) :
    (den : Rat) = Rat.divInt (den : Int) (1 : Int) := by
  rw [←Rat.intCast_natCast den]
  exact rat_intCast_eq_divInt_one (den : Int)

theorem rat_den_mul_self (q : Rat) : (q.den : Rat) * q = (q.num : Rat) := by
  cases q with
  | mk' num den den_nz reduced =>
    change (den : Rat) *
      ({ num := num, den := den, den_nz := den_nz, reduced := reduced } : Rat) = (num : Rat)
    rw [Rat.mk_eq_divInt]
    rw [rat_natCast_eq_divInt_one den, rat_intCast_eq_divInt_one num]
    rw [Rat.divInt_mul_divInt]
    have hdenInt : (den : Int) ≠ 0 := by exact_mod_cast den_nz
    rw [Int.mul_comm (den : Int) num]
    change Rat.divInt (num * (den : Int)) (1 * (den : Int)) = Rat.divInt num 1
    rw [Rat.divInt_mul_right (n := num) (d := 1) hdenInt]

theorem rat_eq_of_den_mul_eq_num {q s : Rat}
    (hs : (q.den : Rat) * s = (q.num : Rat)) :
    s = q := by
  have hdenpos : 0 < (q.den : Rat) :=
    (Rat.natCast_pos).2 (Nat.pos_of_ne_zero q.den_nz)
  refine Rat.le_antisymm ?_ ?_
  · apply Rat.le_of_mul_le_mul_right (c := (q.den : Rat))
    · rw [Rat.mul_comm s (q.den : Rat), hs]
      rw [Rat.mul_comm q (q.den : Rat), rat_den_mul_self]
      exact Rat.le_refl
    · exact hdenpos
  · apply Rat.le_of_mul_le_mul_right (c := (q.den : Rat))
    · rw [Rat.mul_comm s (q.den : Rat), hs]
      rw [Rat.mul_comm q (q.den : Rat), rat_den_mul_self]
      exact Rat.le_refl
    · exact hdenpos

theorem rat_num_pos_of_pos {q : Rat} (hq : 0 < q) : 0 < q.num := by
  unfold LT.lt Rat.instLT Rat.blt at hq
  simp at hq
  by_cases hnum : q.num = 0
  · simp [hnum] at hq
  · by_cases hneg : q.num < 0
    · omega
    · omega

/-- A denominator-based natural precision always suffices for a positive
rational tolerance.  This is finite rational arithmetic, not an appeal to
Archimedean completeness. -/
theorem one_div_den_succ_le_of_pos {q : Rat} (hq : 0 < q) :
    1 / (((q.den + 1 : Nat) : Rat)) <= q := by
  let d : Rat := ((q.den + 1 : Nat) : Rat)
  have hdpos : 0 < d := by
    dsimp [d]
    exact (Rat.natCast_pos).2 (Nat.succ_pos q.den)
  have hnumpos : 0 < q.num := rat_num_pos_of_pos hq
  have hnumgeInt : (1 : Int) <= q.num := by omega
  have hnumge : (1 : Rat) <= (q.num : Rat) := by
    exact_mod_cast hnumgeInt
  have hqd :
      q * d = (q.num : Rat) + q := by
    dsimp [d]
    have hden := rat_den_mul_self q
    grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]
  have hqd_ge_one : 1 <= q * d := by
    rw [hqd]
    have hqnonneg : 0 <= q := Rat.le_of_lt hq
    exact Rat.le_trans hnumge (by grind)
  apply Rat.le_of_mul_le_mul_right (c := d)
  · calc
      (1 / d) * d = 1 := by
        rw [Rat.div_def]
        have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= q * d := hqd_ge_one
  · exact hdpos

def ShrinksToZero (width : Nat -> Rat) : Prop :=
  forall eps : QPos, Exists fun N : Nat =>
    forall n, N <= n -> width n <= eps.val

/-- A rational `C / (n + 1)` modulus is enough for epsilon--delta
convergence.  This is the finite denominator argument used throughout the
development; it establishes no completeness property. -/
theorem shrinksToZero_of_natOverSuccBound
    {width : Nat -> Rat} {C : Nat}
    (hbound : forall n, width n <= (C : Rat) / (((n + 1 : Nat) : Rat))) :
    ShrinksToZero width := by
  intro eps
  refine ⟨C * (eps.val.den + 1), ?_⟩
  intro n hn
  have hmain :
      (C : Rat) / (((n + 1 : Nat) : Rat)) <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    let A : Rat := ((n + 1 : Nat) : Rat)
    let B : Rat := ((eps.val.den + 1 : Nat) : Rat)
    let K : Rat := (C : Rat)
    have hApos : 0 < A := by
      dsimp [A]
      exact (Rat.natCast_pos).2 (Nat.succ_pos n)
    have hBpos : 0 < B := by
      dsimp [B]
      exact (Rat.natCast_pos).2 (Nat.succ_pos eps.val.den)
    have hAne : A ≠ 0 := Rat.ne_of_gt hApos
    have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
    have hABpos : 0 < A * B := Rat.mul_pos hApos hBpos
    have hscaledRat : K * B <= A := by
      dsimp [A, B, K]
      exact_mod_cast (by omega :
        C * (eps.val.den + 1) <= n + 1)
    apply Rat.le_of_mul_le_mul_right (c := A * B)
    · calc
        (K / A) * (A * B) = K * B := by
          rw [Rat.div_def]
          have hcancel : A * A⁻¹ = 1 := Rat.mul_inv_cancel A hAne
          grind [Rat.mul_assoc, Rat.mul_comm]
        _ <= A := hscaledRat
        _ = (1 / B) * (A * B) := by
          rw [Rat.div_def]
          have hcancel : B * B⁻¹ = 1 := Rat.mul_inv_cancel B hBne
          grind [Rat.mul_assoc, Rat.mul_comm]
    · exact hABpos
  exact Rat.le_trans (hbound n)
    (Rat.le_trans hmain (one_div_den_succ_le_of_pos eps.property))

/-- Every rational is bounded in absolute value by the successor of the
natural absolute value of its stored numerator.  This deliberately coarse
bound is executable and is useful when a rational convergence coefficient
must be converted to the natural coefficient expected by a stage schedule. -/
theorem qabs_le_numNatAbs_succ (q : Rat) :
    qabs q <= (((q.num.natAbs + 1 : Nat) : Rat)) := by
  have hraw : q <= (((q.num.natAbs + 1 : Nat) : Rat)) := by
    by_cases hqpos : 0 < q
    · have hdenpos : 0 < ((q.den : Nat) : Rat) :=
        (Rat.natCast_pos).2 (Nat.pos_of_ne_zero q.den_nz)
      apply Rat.le_of_mul_le_mul_right (c := ((q.den : Nat) : Rat))
      · rw [Rat.mul_comm q ((q.den : Nat) : Rat), rat_den_mul_self]
        have hnumpos : 0 < q.num := rat_num_pos_of_pos hqpos
        have hnum_nonneg : 0 <= q.num := Int.le_of_lt hnumpos
        have hcast : (((q.num.natAbs : Nat) : Rat)) = (q.num : Rat) := by
          exact_mod_cast (Int.natAbs_of_nonneg hnum_nonneg)
        calc
          (q.num : Rat) = ((q.num.natAbs : Nat) : Rat) := by rw [hcast]
          _ <= (((q.num.natAbs + 1 : Nat) : Rat)) := by
            exact_mod_cast (Nat.le_succ q.num.natAbs)
          _ <= (((q.num.natAbs + 1 : Nat) : Rat)) *
              ((q.den : Nat) : Rat) := by
            exact_mod_cast (Nat.le_mul_of_pos_right (q.num.natAbs + 1)
              (Nat.pos_of_ne_zero q.den_nz))
      · exact hdenpos
    · have hqnonpos : q <= 0 := by grind
      have hzero : (0 : Rat) <= (((q.num.natAbs + 1 : Nat) : Rat)) := by
        exact_mod_cast (Nat.zero_le (q.num.natAbs + 1))
      exact Rat.le_trans hqnonpos hzero
  unfold qabs
  by_cases hneg : q < 0
  · simp [hneg]
    have hnegRaw : -q <= ((((-q).num.natAbs + 1 : Nat) : Rat)) := by
      by_cases hpos : 0 < -q
      · have hdenpos : 0 < (((-q).den : Nat) : Rat) :=
          (Rat.natCast_pos).2 (Nat.pos_of_ne_zero (-q).den_nz)
        apply Rat.le_of_mul_le_mul_right (c := (((-q).den : Nat) : Rat))
        · rw [Rat.mul_comm (-q) (((-q).den : Nat) : Rat),
            rat_den_mul_self]
          have hnumpos : 0 < (-q).num := rat_num_pos_of_pos hpos
          have hnum_nonneg : 0 <= (-q).num := Int.le_of_lt hnumpos
          have hcast : ((((-q).num.natAbs : Nat) : Rat)) =
              ((-q).num : Rat) := by
            exact_mod_cast (Int.natAbs_of_nonneg hnum_nonneg)
          calc
            ((-q).num : Rat) = (((-q).num.natAbs : Nat) : Rat) := by
              rw [hcast]
            _ <= ((((-q).num.natAbs + 1 : Nat) : Rat)) := by
              exact_mod_cast (Nat.le_succ (-q).num.natAbs)
            _ <= ((((-q).num.natAbs + 1 : Nat) : Rat)) *
                (((-q).den : Nat) : Rat) := by
              exact_mod_cast (Nat.le_mul_of_pos_right ((-q).num.natAbs + 1)
                (Nat.pos_of_ne_zero (-q).den_nz))
        · exact hdenpos
      · have hnonpos : -q <= 0 := by grind
        exact Rat.le_trans hnonpos (by exact_mod_cast
          (Nat.zero_le ((-q).num.natAbs + 1)))
    have hnum : (-q).num.natAbs = q.num.natAbs := by
      cases q
      simp
    simpa [hnum] using hnegRaw
  · simp [hneg]
    have hone : (((1 : Nat) : Rat)) = 1 := by decide +kernel
    simpa only [Rat.natCast_add, hone] using hraw

/-- The reciprocal-stage convergence lemma with an arbitrary nonnegative
rational coefficient.  Internally it replaces the coefficient by the finite
natural numerator bound above and reuses `shrinksToZero_of_natOverSuccBound`. -/
theorem shrinksToZero_of_ratOverSuccBound
    {width : Nat -> Rat} {C : Rat}
    (hbound : forall n, width n <= C / (((n + 1 : Nat) : Rat))) :
    ShrinksToZero width := by
  let N : Nat := C.num.natAbs + 1
  apply shrinksToZero_of_natOverSuccBound (C := N)
  intro n
  have hCN : C <= (N : Rat) :=
    Rat.le_trans (self_le_qabs C) (by
      simpa [N] using qabs_le_numNatAbs_succ C)
  have hinv : 0 <= ((((n + 1 : Nat) : Rat))⁻¹) :=
    Rat.le_of_lt ((Rat.inv_pos).2
      ((Rat.natCast_pos).2 (Nat.succ_pos n)))
  exact Rat.le_trans (hbound n) (by
    rw [Rat.div_def, Rat.div_def]
    exact Rat.mul_le_mul_of_nonneg_right hCN hinv)

namespace RealCompute

def WidthsShrinkToZero (compute : Nat -> QInterval) : Prop :=
  forall eps : QPos, Exists fun N : Nat =>
    forall n : Nat, N <= n -> (compute n).width <= eps.val

/-- A raw real algorithm is valid when every stage is an ordered interval,
later stages nest inside earlier stages, and widths tend to zero.  No fixed
speed such as `1/n` is part of this definition. -/
def ValidCompute (compute : Nat -> QInterval) : Prop :=
  (forall n, 0 <= (compute n).width) /\
  (forall n m, n <= m ->
    (compute n).lo <= (compute m).lo /\
    (compute m).lo <= (compute m).hi /\
    (compute m).hi <= (compute n).hi) /\
  WidthsShrinkToZero compute

/-- Optional convergence-rate metadata for a raw interval algorithm.

This is deliberately not another kind of real number. It is just information
attached to a concrete algorithm: eventually the width is bounded either by
`constant / n^power` or by `constant * ratio^n`. `RealCompute` definitions may
leave the rate as `unknown` until a useful bound has been proved. -/
inductive Rate (compute : Nat -> QInterval) where
  | unknown
  | power
      (start : Nat)
      (constant : Rat)
      (power : Nat)
      (power_pos : 0 < power)
      (width_le : forall n : Nat, start <= n ->
        (compute n).width <= constant / (n : Rat) ^ power)
  | geometric
      (start : Nat)
      (constant : Rat)
      (ratio : Rat)
      (ratio_nonneg : 0 <= ratio)
      (ratio_lt_one : ratio < 1)
      (width_le : forall n : Nat, start <= n ->
        (compute n).width <= constant * ratio ^ n)

end RealCompute

/-- Raw interval algorithm for a real number approximation.

At stage `n : Nat`, `compute n` returns two rational endpoints.  A proof of
`RealCompute.ValidCompute compute`, defined just above, says using only rational
inequalities that:

* every interval is ordered;
* later stages are nested inside earlier stages;
* for every positive rational tolerance, all sufficiently late stages have
  width at most that tolerance.

The data here is intentionally tiny: the computation itself plus optional
rate metadata.  Validity is the separate proposition `x.Valid`, so public
algorithms can stay visibly raw while proofs attach the needed certificate. -/
structure RealCompute where
  compute : Nat -> QInterval
  rate : RealCompute.Rate compute := .unknown

namespace RealCompute

def Valid (x : RealCompute) : Prop := ValidCompute x.compute

/-- A cofinal schedule of computation stages.

The schedule may skip stages, but it must move monotonically forward and
eventually pass every requested stage. -/
structure StageSchedule where
  stage : Nat -> Nat
  monotone : forall i j, i <= j -> stage i <= stage j
  cofinal : forall target : Nat, Exists fun k : Nat => target <= (stage k)

namespace StageSchedule

def id : StageSchedule where
  stage := fun n => n + 1
  monotone := by
    intro i j hij
    exact Nat.succ_le_succ hij
  cofinal := by
    intro target
    refine ⟨target, ?_⟩
    omega
end StageSchedule

inductive CompareAt where
  | less
  | greater
  | overlap
deriving Repr, DecidableEq

namespace CompareAt

def display : CompareAt -> String
  | .less => "less"
  | .greater => "greater"
  | .overlap => "overlap"

end CompareAt

def compareIntervals (X Y : QInterval) : CompareAt :=
  if X.hi < Y.lo then
    .less
  else if Y.hi < X.lo then
    .greater
  else
    .overlap

theorem compareIntervals_overlap_iff (X Y : QInterval) :
    Iff (compareIntervals X Y = .overlap) (QInterval.Overlaps X Y) := by
  unfold compareIntervals QInterval.Overlaps
  by_cases hxy : X.hi < Y.lo
  case pos =>
    rw [if_pos hxy]
    constructor
    case mp => intro h; cases h
    case mpr => grind
  case neg =>
    rw [if_neg hxy]
    by_cases hyx : Y.hi < X.lo
    case pos =>
      rw [if_pos hyx]
      constructor
      case mp => intro h; cases h
      case mpr => grind
    case neg =>
      rw [if_neg hyx]
      constructor
      case mp => grind
      case mpr => intro _; rfl

def compareAt (x y : RealCompute) (nx : Nat) (ny : Nat := nx) : CompareAt :=
  compareIntervals (x.compute nx) (y.compute ny)

theorem compareAt_overlap_iff (x y : RealCompute) (nx ny : Nat) :
    Iff (compareAt x y nx ny = .overlap)
      (QInterval.Overlaps (x.compute nx) (y.compute ny)) :=
  compareIntervals_overlap_iff (x.compute nx) (y.compute ny)

def SameStageOverlap (x y : RealCompute) : Prop :=
  forall n, compareAt x y n = .overlap

/-- Equality of raw real algorithms.

Two raw representatives are equivalent when their interval computations
overlap at every common stage. Stage schedules are a proof technique rather
than part of the definition. -/
def Equiv (x y : RealCompute) : Prop :=
  x.SameStageOverlap y

/-- Exact order of raw reals, expressed directly through rational interval
approximations.

This is deliberately not the executable interval comparison `compareAt`.
It says that every rational lower approximation to `x` is at most every
rational upper approximation to `y`.  For valid shrinking representatives,
this is the order relation that survives changes of representative and is the
right primitive for exact convexity. -/
def Le (x y : RealCompute) : Prop :=
  forall n m, (x.compute n).lo <= (y.compute m).hi

theorem sameStageOverlap_equiv {x y : RealCompute} :
    x.SameStageOverlap y -> x.Equiv y := by
  intro h
  exact h

def schedule (sigma : StageSchedule) (x : RealCompute) : RealCompute where
  compute := fun n => x.compute (sigma.stage n)


/-- Stronger than `Equiv`: every interval produced by one raw algorithm
overlaps every interval produced by the other, even at different stages. -/
def AllStagesOverlap (x y : RealCompute) : Prop :=
  forall n m, compareAt x y n m = .overlap

theorem allStagesOverlap_equiv {x y : RealCompute} :
    x.AllStagesOverlap y -> x.Equiv y := by
  intro h
  exact sameStageOverlap_equiv (fun n => h n n)

def StrongEquiv (x y : RealCompute) : Prop :=
  x.AllStagesOverlap y /\ x.Valid /\ y.Valid

def decimalAt (x : RealCompute) (digits : Nat) (n : Nat) : String :=
  QInterval.decimal digits (x.compute n)

def displayAt (x : RealCompute) (n : Nat) : String :=
  QInterval.display (x.compute n)

end RealCompute

end ComputableAnalysis

namespace ComputableAnalysis

private theorem rat_lt_trans {a b c : Rat} (hab : a < b) (hbc : b < c) :
    a < c := by
  apply Rat.lt_of_le_of_ne (Rat.le_trans (Rat.le_of_lt hab) (Rat.le_of_lt hbc))
  intro hac
  rw [hac] at hab
  exact Rat.ne_of_lt hbc (Rat.le_antisymm (Rat.le_of_lt hbc) (Rat.le_of_lt hab))

namespace RealCompute

theorem interval_order_of_valid (x : RealCompute) (hx : x.Valid) (n : Nat) :
    (x.compute n).lo <= (x.compute n).hi := by
  have hwidth := hx.1 n
  grind [QInterval.width, Rat.sub_eq_add_neg]

/-- Rebox a shrinking interval algorithm against a verified nested anchor.

At stage `n` this takes the intersection of the first `n + 1` hulls of the
candidate interval and the corresponding anchor interval.  Every operation is
finite rational `min`/`max` arithmetic.  This is useful when a natural
algorithm has a width modulus and stagewise overlap proof, but its own endpoint
monotonicity has not yet been established. -/
def anchorReboxCompute
    (candidate anchor : Nat -> QInterval) : Nat -> QInterval
  | 0 => QInterval.hull (candidate 0) (anchor 0)
  | n + 1 => QInterval.intersection
      (anchorReboxCompute candidate anchor n)
      (QInterval.hull (candidate (n + 1)) (anchor (n + 1)))

def anchorRebox (candidate anchor : RealCompute) : RealCompute where
  compute := anchorReboxCompute candidate.compute anchor.compute

private theorem anchorReboxCompute_contains_anchor
    {candidate anchor : Nat -> QInterval}
    (hanchor_nested : forall n m, n <= m ->
      (anchor n).lo <= (anchor m).lo /\
        (anchor m).lo <= (anchor m).hi /\
        (anchor m).hi <= (anchor n).hi) :
    forall n, (anchorReboxCompute candidate anchor n).ContainsInterval (anchor n) := by
  intro n
  induction n with
  | zero =>
      exact QInterval.hull_contains_right (candidate 0) (anchor 0)
  | succ n ih =>
      apply QInterval.intersection_contains
      · have hnested := hanchor_nested n (n + 1) (Nat.le_succ n)
        exact ⟨Rat.le_trans ih.1 hnested.1,
          Rat.le_trans hnested.2.2 ih.2⟩
      · exact QInterval.hull_contains_right
          (candidate (n + 1)) (anchor (n + 1))

private theorem anchorReboxCompute_contained_in_current_hull
    (candidate anchor : Nat -> QInterval) :
    forall n, (QInterval.hull (candidate n) (anchor n)).ContainsInterval
      (anchorReboxCompute candidate anchor n) := by
  intro n
  induction n with
  | zero =>
      exact ⟨Rat.le_refl, Rat.le_refl⟩
  | succ n _ih =>
      exact QInterval.intersection_contained_right
        (anchorReboxCompute candidate anchor n)
        (QInterval.hull (candidate (n + 1)) (anchor (n + 1)))

private theorem anchorReboxCompute_step_nested
    (candidate anchor : Nat -> QInterval) (n : Nat) :
    (anchorReboxCompute candidate anchor n).lo <=
        (anchorReboxCompute candidate anchor (n + 1)).lo /\
      (anchorReboxCompute candidate anchor (n + 1)).hi <=
        (anchorReboxCompute candidate anchor n).hi :=
  QInterval.intersection_contained_left
    (anchorReboxCompute candidate anchor n)
    (QInterval.hull (candidate (n + 1)) (anchor (n + 1)))

theorem anchorRebox_contains_anchor
    {candidate anchor : RealCompute}
    (hanchor : anchor.Valid) :
    forall n, (anchorRebox candidate anchor).compute n |>.ContainsInterval
      (anchor.compute n) := by
  exact anchorReboxCompute_contains_anchor hanchor.2.1

theorem anchorRebox_valid
    {candidate anchor : RealCompute}
    (hcandidate_ordered : forall n, 0 <= (candidate.compute n).width)
    (hcandidate_shrinks : WidthsShrinkToZero candidate.compute)
    (hanchor : anchor.Valid)
    (hover : candidate.Equiv anchor) :
    (anchorRebox candidate anchor).Valid := by
  have hcontains := anchorRebox_contains_anchor (candidate := candidate)
    (anchor := anchor) hanchor
  have hcurrent := anchorReboxCompute_contained_in_current_hull
    candidate.compute anchor.compute
  have hstep := anchorReboxCompute_step_nested
    candidate.compute anchor.compute
  constructor
  · intro n
    have hanchor_ordered := interval_order_of_valid anchor hanchor n
    have hcontain := hcontains n
    unfold QInterval.ContainsInterval at hcontain
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      induction hnm with
      | refl =>
          have hordered := interval_order_of_valid anchor hanchor n
          have hcontain := hcontains n
          unfold QInterval.ContainsInterval at hcontain
          exact ⟨Rat.le_refl, by
            have hleft :
                ((anchorRebox candidate anchor).compute n).lo <=
                  ((anchorRebox candidate anchor).compute n).hi := by
              change ((anchorRebox candidate anchor).compute n).lo <=
                (anchor.compute n).lo /\
                (anchor.compute n).hi <=
                  ((anchorRebox candidate anchor).compute n).hi at hcontain
              exact Rat.le_trans hcontain.1
                (Rat.le_trans hordered hcontain.2)
            exact ⟨hleft, Rat.le_refl⟩⟩
      | step hnm ih =>
          rename_i k
          have hnext := hstep k
          have hordered := interval_order_of_valid anchor hanchor (k + 1)
          have hcontain := hcontains (k + 1)
          have hnext_ordered :
                ((anchorRebox candidate anchor).compute (k + 1)).lo <=
                ((anchorRebox candidate anchor).compute (k + 1)).hi := by
            change ((anchorRebox candidate anchor).compute (k + 1)).lo <=
              (anchor.compute (k + 1)).lo /\
              (anchor.compute (k + 1)).hi <=
                ((anchorRebox candidate anchor).compute (k + 1)).hi at hcontain
            exact Rat.le_trans hcontain.1
              (Rat.le_trans hordered hcontain.2)
          exact ⟨Rat.le_trans ih.1 hnext.1,
            ⟨hnext_ordered, Rat.le_trans hnext.2 ih.2.2⟩⟩
    · intro eps
      let half : QPos := ⟨eps.val / 2, by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property
          ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2))⟩
      obtain ⟨Nc, hNc⟩ := hcandidate_shrinks half
      obtain ⟨Na, hNa⟩ := hanchor.2.2 half
      refine ⟨Nat.max Nc Na, ?_⟩
      intro n hn
      have hcn : Nc <= n := Nat.le_trans (Nat.le_max_left _ _) hn
      have han : Na <= n := Nat.le_trans (Nat.le_max_right _ _) hn
      have hcandidate_width := hNc n hcn
      have hanchor_width := hNa n han
      have hcurrent_n := hcurrent n
      have hcurrent_width :
          ((anchorRebox candidate anchor).compute n).width <=
            (QInterval.hull (candidate.compute n) (anchor.compute n)).width := by
        exact QInterval.width_le_of_contains hcurrent_n
      have hhulled_width :
          (QInterval.hull (candidate.compute n) (anchor.compute n)).width <=
            (candidate.compute n).width + (anchor.compute n).width := by
        have hover_n := (compareAt_overlap_iff candidate anchor n n).1 (hover n)
        exact QInterval.hull_width_le_add_of_overlaps
          (hcandidate_ordered n) (hanchor.1 n) hover_n
      change ((anchorRebox candidate anchor).compute n).width <= eps.val
      calc
        ((anchorRebox candidate anchor).compute n).width <=
            (QInterval.hull (candidate.compute n) (anchor.compute n)).width :=
          hcurrent_width
        _ <= (candidate.compute n).width + (anchor.compute n).width :=
          hhulled_width
        _ <= half.val + half.val :=
          by grind
        _ = eps.val := by
          dsimp [half]
          rw [Rat.div_def]
          grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem anchorRebox_equiv_anchor
    {candidate anchor : RealCompute}
    (hanchor : anchor.Valid) :
    (anchorRebox candidate anchor).Equiv anchor := by
  intro n
  apply (compareAt_overlap_iff (anchorRebox candidate anchor) anchor n n).2
  have hcontain := anchorRebox_contains_anchor (candidate := candidate)
    (anchor := anchor) hanchor n
  have hordered := interval_order_of_valid anchor hanchor n
  exact ⟨Rat.le_trans hcontain.1 hordered,
    Rat.le_trans hordered hcontain.2⟩

theorem candidate_equiv_anchorRebox
    {candidate anchor : RealCompute}
    (hanchor : anchor.Valid)
    (hover : candidate.Equiv anchor) :
    candidate.Equiv (anchorRebox candidate anchor) := by
  intro n
  have hcandidate_anchor :=
    (compareAt_overlap_iff candidate anchor n n).1 (hover n)
  have hcontains := anchorRebox_contains_anchor (candidate := candidate)
    (anchor := anchor) hanchor n
  apply (compareAt_overlap_iff candidate (anchorRebox candidate anchor) n n).2
  exact ⟨Rat.le_trans hcandidate_anchor.1 hcontains.2,
    Rat.le_trans hcontains.1 hcandidate_anchor.2⟩

/-- Finite prefix stabilization of an interval algorithm.  Unlike
`anchorReboxCompute`, this computation reads only the candidate intervals and
a rational error-radius schedule: at each stage it intersects all widened
candidate intervals seen so far. -/
def prefixStabilizeCompute
    (candidate : Nat -> QInterval) (radius : Nat -> Rat) : Nat -> QInterval
  | 0 => QInterval.expand (candidate 0) (radius 0)
  | n + 1 => QInterval.intersection
      (prefixStabilizeCompute candidate radius n)
      (QInterval.expand (candidate (n + 1)) (radius (n + 1)))

def prefixStabilize (candidate : RealCompute) (radius : Nat -> Rat) : RealCompute where
  compute := prefixStabilizeCompute candidate.compute radius

private theorem prefixStabilizeCompute_contains_anchor
    {candidate anchor : RealCompute} {radius : Nat -> Rat}
    (hanchor_nested : forall n m, n <= m ->
      (anchor.compute n).lo <= (anchor.compute m).lo /\
        (anchor.compute m).lo <= (anchor.compute m).hi /\
        (anchor.compute m).hi <= (anchor.compute n).hi)
    (hover : candidate.Equiv anchor)
    (hradius : forall n, (anchor.compute n).width <= radius n) :
    forall n,
      (prefixStabilizeCompute candidate.compute radius n).ContainsInterval
        (anchor.compute n) := by
  intro n
  induction n with
  | zero =>
      apply QInterval.expand_contains_right_of_overlaps
      · exact (compareAt_overlap_iff candidate anchor 0 0).1 (hover 0)
      · exact hradius 0
  | succ n ih =>
      apply QInterval.intersection_contains
      · have hnest := hanchor_nested n (n + 1) (Nat.le_succ n)
        exact ⟨Rat.le_trans ih.1 hnest.1,
          Rat.le_trans hnest.2.2 ih.2⟩
      · apply QInterval.expand_contains_right_of_overlaps
        · exact (compareAt_overlap_iff candidate anchor (n + 1) (n + 1)).1
            (hover (n + 1))
        · exact hradius (n + 1)

private theorem prefixStabilizeCompute_contained_in_current_expand
    (candidate : Nat -> QInterval) (radius : Nat -> Rat) :
    forall n,
      (QInterval.expand (candidate n) (radius n)).ContainsInterval
        (prefixStabilizeCompute candidate radius n) := by
  intro n
  cases n with
  | zero => exact ⟨Rat.le_refl, Rat.le_refl⟩
  | succ n =>
      exact QInterval.intersection_contained_right
        (prefixStabilizeCompute candidate radius n)
        (QInterval.expand (candidate (n + 1)) (radius (n + 1)))

/-- At every stage, finite-prefix stabilization is contained in the current
widened candidate interval.  This exposes the direct runtime width bound of a
stabilized algorithm without referring to its proof-side anchor. -/
theorem prefixStabilize_contained_in_current_expand
    (candidate : RealCompute) (radius : Nat -> Rat) (n : Nat) :
    (QInterval.expand (candidate.compute n) (radius n)).ContainsInterval
      ((prefixStabilize candidate radius).compute n) := by
  exact prefixStabilizeCompute_contained_in_current_expand
    candidate.compute radius n

private theorem prefixStabilizeCompute_step_nested
    (candidate : Nat -> QInterval) (radius : Nat -> Rat) (n : Nat) :
    (prefixStabilizeCompute candidate radius n).lo <=
        (prefixStabilizeCompute candidate radius (n + 1)).lo /\
      (prefixStabilizeCompute candidate radius (n + 1)).hi <=
        (prefixStabilizeCompute candidate radius n).hi :=
  QInterval.intersection_contained_left
    (prefixStabilizeCompute candidate radius n)
    (QInterval.expand (candidate (n + 1)) (radius (n + 1)))

/-- The stabilized direct-only computation contains the anchor at every stage
provided that the explicit radius covers the anchor's current interval width. -/
theorem prefixStabilize_contains_anchor
    {candidate anchor : RealCompute} {radius : Nat -> Rat}
    (hanchor : anchor.Valid)
    (hover : candidate.Equiv anchor)
    (hradius : forall n, (anchor.compute n).width <= radius n) :
    forall n,
      (prefixStabilize candidate radius).compute n |>.ContainsInterval
        (anchor.compute n) := by
  exact prefixStabilizeCompute_contains_anchor hanchor.2.1 hover hradius

/-- A direct interval computation can be made nested without reading its
anchor at runtime.  The proof uses the anchor only to certify the public
rational radius schedule; the resulting evaluator uses finite intersections
of widened candidate intervals alone. -/
theorem prefixStabilize_valid
    {candidate anchor : RealCompute} {radius : Nat -> Rat}
    (hcandidate_shrinks : WidthsShrinkToZero candidate.compute)
    (hanchor : anchor.Valid)
    (hover : candidate.Equiv anchor)
    (hradius : forall n, (anchor.compute n).width <= radius n)
    (hradius_shrinks : ShrinksToZero radius) :
    (prefixStabilize candidate radius).Valid := by
  have hcontains := prefixStabilize_contains_anchor
    (candidate := candidate) (anchor := anchor) hanchor hover hradius
  have hcurrent := prefixStabilizeCompute_contained_in_current_expand
    candidate.compute radius
  have hstep := prefixStabilizeCompute_step_nested candidate.compute radius
  constructor
  · intro n
    have hanchor_ordered := interval_order_of_valid anchor hanchor n
    have hcontain := hcontains n
    have hendpoints :
        ((prefixStabilize candidate radius).compute n).lo <=
          ((prefixStabilize candidate radius).compute n).hi :=
      Rat.le_trans hcontain.1
        (Rat.le_trans hanchor_ordered hcontain.2)
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      induction hnm with
      | refl =>
          have hanchor_ordered := interval_order_of_valid anchor hanchor n
          have hcontain := hcontains n
          exact ⟨Rat.le_refl,
            Rat.le_trans hcontain.1
              (Rat.le_trans hanchor_ordered hcontain.2),
            Rat.le_refl⟩
      | step hnm ih =>
          rename_i k
          have hnext := hstep k
          have hanchor_ordered := interval_order_of_valid anchor hanchor (k + 1)
          have hcontain := hcontains (k + 1)
          have hnext_ordered :
              ((prefixStabilize candidate radius).compute (k + 1)).lo <=
                ((prefixStabilize candidate radius).compute (k + 1)).hi :=
            Rat.le_trans hcontain.1
              (Rat.le_trans hanchor_ordered hcontain.2)
          exact ⟨Rat.le_trans ih.1 hnext.1,
            hnext_ordered, Rat.le_trans hnext.2 ih.2.2⟩
    · intro eps
      let half : QPos := ⟨eps.val / 2, by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property
          ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2))⟩
      let quarter : QPos := ⟨eps.val / 4, by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property
          ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 4))⟩
      obtain ⟨Nc, hNc⟩ := hcandidate_shrinks half
      obtain ⟨Nr, hNr⟩ := hradius_shrinks quarter
      refine ⟨Nat.max Nc Nr, ?_⟩
      intro n hn
      have hcn : Nc <= n := Nat.le_trans (Nat.le_max_left _ _) hn
      have hrn : Nr <= n := Nat.le_trans (Nat.le_max_right _ _) hn
      have hcandidate_width := hNc n hcn
      have hradius_width := hNr n hrn
      have hcurrent_width :
          ((prefixStabilize candidate radius).compute n).width <=
            (QInterval.expand (candidate.compute n) (radius n)).width := by
        exact QInterval.width_le_of_contains (hcurrent n)
      rw [QInterval.expand_width] at hcurrent_width
      change ((prefixStabilize candidate radius).compute n).width <= eps.val
      calc
        ((prefixStabilize candidate radius).compute n).width <=
            (candidate.compute n).width + 2 * radius n := hcurrent_width
        _ <= half.val + 2 * quarter.val := by
          exact rat_add_le_add hcandidate_width
            (Rat.mul_le_mul_of_nonneg_left hradius_width
              (by decide +kernel : (0 : Rat) <= 2))
        _ = eps.val := by
          dsimp [half, quarter]
          rw [Rat.div_def, Rat.div_def]
          grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm,
            Rat.mul_inv_cancel]

theorem prefixStabilize_equiv_anchor
    {candidate anchor : RealCompute} {radius : Nat -> Rat}
    (hanchor : anchor.Valid)
    (hover : candidate.Equiv anchor)
    (hradius : forall n, (anchor.compute n).width <= radius n) :
    (prefixStabilize candidate radius).Equiv anchor := by
  intro n
  apply (compareAt_overlap_iff (prefixStabilize candidate radius) anchor n n).2
  have hcontains := prefixStabilize_contains_anchor
    (candidate := candidate) (anchor := anchor) hanchor hover hradius n
  have hanchor_ordered := interval_order_of_valid anchor hanchor n
  exact ⟨Rat.le_trans hcontains.1 hanchor_ordered,
    Rat.le_trans hanchor_ordered hcontains.2⟩

/-- The original candidate and its finite-prefix stabilization overlap at
every common stage.  As with `prefixStabilize_equiv_anchor`, the anchor is a
proof-side certificate only; the stabilized evaluator does not read it. -/
theorem candidate_equiv_prefixStabilize
    {candidate anchor : RealCompute} {radius : Nat -> Rat}
    (hanchor : anchor.Valid)
    (hover : candidate.Equiv anchor)
    (hradius : forall n, (anchor.compute n).width <= radius n) :
    candidate.Equiv (prefixStabilize candidate radius) := by
  intro n
  have hcandidate_anchor :=
    (compareAt_overlap_iff candidate anchor n n).1 (hover n)
  have hcontains := prefixStabilize_contains_anchor
    (candidate := candidate) (anchor := anchor) hanchor hover hradius n
  apply (compareAt_overlap_iff candidate (prefixStabilize candidate radius) n n).2
  exact ⟨Rat.le_trans hcandidate_anchor.1 hcontains.2,
    Rat.le_trans hcontains.1 hcandidate_anchor.2⟩

/-! ### Direct Cauchy gluing without a pre-existing anchor -/

/-- If every later candidate box is contained in every earlier explicitly
widened box, then the finite-prefix intersection at stage `k` contains every
candidate from stage `k` onward.  This is the finite witness used to glue
growing-domain computations before their limiting value has another
representation. -/
theorem prefixStabilize_contains_future_candidate
    {candidate : RealCompute} {radius : Nat -> Rat}
    (hfuture : forall k n, k <= n ->
      (QInterval.expand (candidate.compute k) (radius k)).ContainsInterval
        (candidate.compute n)) :
    forall k n, k <= n ->
      ((prefixStabilize candidate radius).compute k).ContainsInterval
        (candidate.compute n) := by
  intro k
  induction k with
  | zero =>
      intro n _hkn
      simpa [prefixStabilize, prefixStabilizeCompute] using hfuture 0 n (Nat.zero_le n)
  | succ k ih =>
      intro n hkn
      change
        QInterval.ContainsInterval (QInterval.intersection
          (prefixStabilizeCompute candidate.compute radius k)
          (QInterval.expand (candidate.compute (k + 1)) (radius (k + 1))))
            (candidate.compute n)
      apply QInterval.intersection_contains
      · change
          ((prefixStabilize candidate radius).compute k).ContainsInterval
            (candidate.compute n)
        exact ih n (Nat.le_trans (Nat.le_succ k) hkn)
      · exact hfuture (k + 1) n hkn

/-- In particular, the stabilized box contains the current direct candidate.
Unlike `prefixStabilize_contains_anchor`, this theorem needs no independently
valid anchor. -/
theorem prefixStabilize_contains_current_of_future
    {candidate : RealCompute} {radius : Nat -> Rat}
    (hfuture : forall k n, k <= n ->
      (QInterval.expand (candidate.compute k) (radius k)).ContainsInterval
        (candidate.compute n))
    (n : Nat) :
    ((prefixStabilize candidate radius).compute n).ContainsInterval
      (candidate.compute n) :=
  prefixStabilize_contains_future_candidate hfuture n n (Nat.le_refl n)

/-- Direct Cauchy gluing for rational interval candidates.  The runtime uses
only the finite list of candidate boxes and the rational widening schedule.
Ordered candidates, shrinking candidate widths, future containment, and a
shrinking widening schedule suffice to prove the stabilized raw valid; no
completed real or proof-side anchor is used. -/
theorem prefixStabilize_valid_of_future_containment
    {candidate : RealCompute} {radius : Nat -> Rat}
    (hcandidate_ordered : forall n,
      (candidate.compute n).lo <= (candidate.compute n).hi)
    (hcandidate_shrinks : WidthsShrinkToZero candidate.compute)
    (hfuture : forall k n, k <= n ->
      (QInterval.expand (candidate.compute k) (radius k)).ContainsInterval
        (candidate.compute n))
    (hradius_shrinks : ShrinksToZero radius) :
    (prefixStabilize candidate radius).Valid := by
  have hcontains := prefixStabilize_contains_current_of_future hfuture
  have hcurrent := prefixStabilize_contained_in_current_expand candidate radius
  have hordered : forall n,
      ((prefixStabilize candidate radius).compute n).lo <=
        ((prefixStabilize candidate radius).compute n).hi := by
    intro n
    exact Rat.le_trans (hcontains n).1
      (Rat.le_trans (hcandidate_ordered n) (hcontains n).2)
  constructor
  · intro n
    have hn := hordered n
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      induction hnm with
      | refl =>
          exact ⟨Rat.le_refl, hordered n, Rat.le_refl⟩
      | step hnm ih =>
          rename_i k
          have hstep := prefixStabilizeCompute_step_nested
            candidate.compute radius k
          exact ⟨Rat.le_trans ih.1 hstep.1, hordered (k + 1),
            Rat.le_trans hstep.2 ih.2.2⟩
    · intro eps
      let half : QPos := ⟨eps.val / 2, by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property
          ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2))⟩
      let quarter : QPos := ⟨eps.val / 4, by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property
          ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 4))⟩
      obtain ⟨Nc, hNc⟩ := hcandidate_shrinks half
      obtain ⟨Nr, hNr⟩ := hradius_shrinks quarter
      refine ⟨Nat.max Nc Nr, ?_⟩
      intro n hn
      have hcn : Nc <= n := Nat.le_trans (Nat.le_max_left _ _) hn
      have hrn : Nr <= n := Nat.le_trans (Nat.le_max_right _ _) hn
      have hcandidate_width := hNc n hcn
      have hradius_width := hNr n hrn
      have hstabilized_width :
          ((prefixStabilize candidate radius).compute n).width <=
            (QInterval.expand (candidate.compute n) (radius n)).width :=
        QInterval.width_le_of_contains (hcurrent n)
      rw [QInterval.expand_width] at hstabilized_width
      calc
        ((prefixStabilize candidate radius).compute n).width <=
            (candidate.compute n).width + 2 * radius n := hstabilized_width
        _ <= half.val + 2 * quarter.val := by
          exact rat_add_le_add hcandidate_width
            (Rat.mul_le_mul_of_nonneg_left hradius_width
              (by decide +kernel : (0 : Rat) <= 2))
        _ = eps.val := by
          dsimp [half, quarter]
          rw [Rat.div_def, Rat.div_def]
          grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm,
            Rat.mul_inv_cancel]

theorem validCompute_stage_eq_of_zero_width
    {compute : Nat -> QInterval}
    (hvalid : RealCompute.ValidCompute compute)
    (hzero : forall n, (compute n).width = 0)
    (n m : Nat) :
    compute n = compute m := by
  have hpoint : forall k, (compute k).lo = (compute k).hi := by
    intro k
    have hwidth := hzero k
    have hordered : (compute k).lo <= (compute k).hi := by
      have hnonneg := hvalid.1 k
      grind [QInterval.width, Rat.sub_eq_add_neg]
    exact Rat.le_antisymm hordered (by
      grind [QInterval.width, Rat.sub_eq_add_neg])
  rcases Nat.le_total n m with hnm | hmn
  · have hnest := hvalid.2.1 n m hnm
    have hlo : (compute n).lo = (compute m).lo := by
      exact Rat.le_antisymm hnest.1 (by
        have hn := hpoint n
        have hm := hpoint m
        grind)
    have hhi : (compute n).hi = (compute m).hi := by
      have hn := hpoint n
      have hm := hpoint m
      grind
    cases hnI : compute n
    cases hmI : compute m
    simp [hnI, hmI] at hlo hhi ⊢
    exact ⟨hlo, hhi⟩
  · have hnest := hvalid.2.1 m n hmn
    have hlo : (compute n).lo = (compute m).lo := by
      exact Rat.le_antisymm (by
        have hn := hpoint n
        have hm := hpoint m
        grind) hnest.1
    have hhi : (compute n).hi = (compute m).hi := by
      have hn := hpoint n
      have hm := hpoint m
      grind
    cases hnI : compute n
    cases hmI : compute m
    simp [hnI, hmI] at hlo hhi ⊢
    exact ⟨hlo, hhi⟩

theorem stage_eq_of_valid_zero_width
    (x : RealCompute) (hx : x.Valid)
    (hzero : forall n, (x.compute n).width = 0)
    (n m : Nat) :
    x.compute n = x.compute m :=
  validCompute_stage_eq_of_zero_width hx hzero n m

theorem sameStageOverlap_refl (x : RealCompute) (hx : x.Valid) :
    x.SameStageOverlap x := by
  intro n
  have h := interval_order_of_valid x hx n
  exact (compareAt_overlap_iff x x n n).2 ⟨h, h⟩

theorem equiv_refl (x : RealCompute) (hx : x.Valid) : x.Equiv x :=
  sameStageOverlap_equiv (sameStageOverlap_refl x hx)

theorem equiv_symm {x y : RealCompute} : x.Equiv y -> y.Equiv x := by
  intro h n
  have hover := (compareAt_overlap_iff x y n n).1 (h n)
  exact (compareAt_overlap_iff y x n n).2 ⟨hover.2, hover.1⟩

theorem allStagesOverlap_refl (x : RealCompute) (hx : x.Valid) :
    x.AllStagesOverlap x := by
  intro n m
  rcases Nat.le_total n m with hnm | hmn
  · have hnest := hx.2.1 n m hnm
    apply (compareAt_overlap_iff x x n m).2
    constructor
    · exact Rat.le_trans hnest.1 hnest.2.1
    · exact Rat.le_trans hnest.2.1 hnest.2.2
  · have hnest := hx.2.1 m n hmn
    apply (compareAt_overlap_iff x x n m).2
    constructor
    · exact Rat.le_trans hnest.2.1 hnest.2.2
    · exact Rat.le_trans hnest.1 hnest.2.1

theorem schedule_valid (x : RealCompute) (hx : x.Valid)
    (sigma : StageSchedule) :
    (schedule sigma x).Valid := by
  constructor
  · intro n
    exact hx.1 (sigma.stage n)
  · constructor
    · intro n m hnm
      exact hx.2.1 (sigma.stage n) (sigma.stage m)
        (sigma.monotone n m hnm)
    · intro eps
      obtain ⟨N, hN⟩ := hx.2.2 eps
      obtain ⟨k, hk⟩ := sigma.cofinal N
      refine ⟨k, ?_⟩
      intro n hkn
      exact hN (sigma.stage n)
        (Nat.le_trans hk (sigma.monotone k n hkn))

theorem schedule_equiv (x : RealCompute) (hx : x.Valid)
    (sigma : StageSchedule) :
    x.Equiv (schedule sigma x) := by
  intro n
  exact allStagesOverlap_refl x hx n (sigma.stage n)

theorem allStagesOverlap_symm {x y : RealCompute} :
    x.AllStagesOverlap y -> y.AllStagesOverlap x := by
  intro h n m
  have hover := (compareAt_overlap_iff x y m n).1 (h m n)
  exact (compareAt_overlap_iff y x n m).2 ⟨hover.2, hover.1⟩

theorem strongEquiv_refl (x : RealCompute) (hx : x.Valid) : x.StrongEquiv x :=
  ⟨allStagesOverlap_refl x hx, hx, hx⟩

theorem strongEquiv_symm {x y : RealCompute} :
    x.StrongEquiv y -> y.StrongEquiv x := by
  intro h
  exact ⟨allStagesOverlap_symm h.1, h.2.2, h.2.1⟩

/-- Unfold equivalence back to the same-stage overlap predicate. -/
theorem sameStageOverlap_of_equiv {x y : RealCompute}
    (_hx : x.Valid) (_hy : y.Valid) :
    x.Equiv y -> x.SameStageOverlap y := by
  intro hxy
  exact hxy

theorem allStagesOverlap_of_sameStageOverlap {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) :
    x.SameStageOverlap y -> x.AllStagesOverlap y := by
  intro hxy n m
  rcases Nat.le_total n m with hnm | hmn
  · have hxnest := hx.2.1 n m hnm
    have hxy_m := (compareAt_overlap_iff x y m m).1 (hxy m)
    apply (compareAt_overlap_iff x y n m).2
    constructor
    · exact Rat.le_trans hxnest.1 hxy_m.1
    · exact Rat.le_trans hxy_m.2 hxnest.2.2
  · have hynest := hy.2.1 m n hmn
    have hxy_n := (compareAt_overlap_iff x y n n).1 (hxy n)
    apply (compareAt_overlap_iff x y n m).2
    constructor
    · exact Rat.le_trans hxy_n.1 hynest.2.2
    · exact Rat.le_trans hynest.1 hxy_n.2

/-- For certified/nested raw algorithms, same-stage equivalence implies
all-stages overlap. -/
theorem allStagesOverlap_of_equiv {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) :
    x.Equiv y -> x.AllStagesOverlap y :=
  fun hxy => allStagesOverlap_of_sameStageOverlap hx hy
    (sameStageOverlap_of_equiv hx hy hxy)

/-! Cofinal finite overlap is enough for equivalence.  This is the reusable
computable-real form of the witness pattern used by analytic identities such
as Basel: later stages may be selected separately for each requested pair of
earlier stages, and nesting transports their overlap back. -/
theorem equiv_of_cofinal_stage_overlap {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid)
    (hcofinal : ∀ n m, ∃ N M, n ≤ N ∧ m ≤ M ∧
      compareAt x y N M = .overlap) :
    x.Equiv y := by
  apply RealCompute.allStagesOverlap_equiv
  intro n m
  obtain ⟨N, M, hnN, hmM, hover⟩ := hcofinal n m
  have hxnest := hx.2.1 n N hnN
  have hynest := hy.2.1 m M hmM
  have hover' := (compareAt_overlap_iff x y N M).1 hover
  apply (compareAt_overlap_iff x y n m).2
  constructor
  · exact Rat.le_trans hxnest.1
      (Rat.le_trans hover'.1 hynest.2.2)
  · exact Rat.le_trans hynest.1
      (Rat.le_trans hover'.2 hxnest.2.2)

/-! A second useful cofinal criterion proves equality from approximating rational
centers rather than asking directly for overlapping intervals. This is the
form used by finite ODE comparison: later lower endpoints are confined by
nesting to every earlier interval, and their separation can be made
arbitrarily small. -/

theorem equiv_of_cofinal_lower_endpoint_closeness {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid)
    (hclose : forall n m (eps : QPos),
      exists N M, n <= N /\ m <= M /\
        qabs ((x.compute N).lo - (y.compute M).lo) <= eps.val) :
    x.Equiv y := by
  apply RealCompute.allStagesOverlap_equiv
  intro n m
  apply (compareAt_overlap_iff x y n m).2
  unfold QInterval.Overlaps
  by_cases hxy : (x.compute n).hi < (y.compute m).lo
  · let gap := (y.compute m).lo - (x.compute n).hi
    have hgap : 0 < gap := by
      dsimp [gap]
      grind [Rat.sub_eq_add_neg]
    let eps : QPos := ⟨gap / 2, by
      rw [Rat.div_def]
      exact Rat.mul_pos hgap ((Rat.inv_pos).2 (by decide : (0 : Rat) < 2))⟩
    obtain ⟨N, M, hnN, hmM, hcloseNM⟩ := hclose n m eps
    have hnested := hx.2.1 n N hnN
    have hmested := hy.2.1 m M hmM
    let a := (x.compute N).lo
    let b := (y.compute M).lo
    have hab : a < b := by
      dsimp [a, b]
      grind
    have hqabs : qabs (a - b) = b - a := by
      have hneg : a - b < 0 := by grind [Rat.sub_eq_add_neg]
      simp [qabs, hneg]
      grind [Rat.sub_eq_add_neg]
    have hgap_le : gap <= b - a := by
      dsimp [gap, a, b]
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
    have hhalf : gap / 2 < gap := by
      rw [Rat.div_def]
      have hinv : (2 : Rat)⁻¹ < 1 := by decide +kernel
      calc
        gap * (2 : Rat)⁻¹ < gap * 1 := Rat.mul_lt_mul_of_pos_left hinv hgap
        _ = gap := Rat.mul_one _
    have hcontra : gap <= gap / 2 := by
      calc
        gap <= b - a := hgap_le
        _ = qabs (a - b) := hqabs.symm
        _ <= eps.val := hcloseNM
        _ = gap / 2 := rfl
    have hnot : ¬ gap <= gap / 2 := by
      intro h
      exact False.elim (by grind)
    exact False.elim (hnot hcontra)
  · by_cases hyx : (y.compute m).hi < (x.compute n).lo
    · let gap := (x.compute n).lo - (y.compute m).hi
      have hgap : 0 < gap := by
        dsimp [gap]
        grind [Rat.sub_eq_add_neg]
      let eps : QPos := ⟨gap / 2, by
        rw [Rat.div_def]
        exact Rat.mul_pos hgap ((Rat.inv_pos).2 (by decide : (0 : Rat) < 2))⟩
      obtain ⟨N, M, hnN, hmM, hcloseNM⟩ := hclose n m eps
      have hnested := hx.2.1 n N hnN
      have hmested := hy.2.1 m M hmM
      let a := (x.compute N).lo
      let b := (y.compute M).lo
      have hba : b < a := by
        dsimp [a, b]
        grind
      have hqabs : qabs (a - b) = a - b := by
        have hnonneg : ¬ a - b < 0 := by grind [Rat.sub_eq_add_neg]
        simp [qabs, hnonneg]
      have hgap_le : gap <= a - b := by
        dsimp [gap, a, b]
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
      have hhalf : gap / 2 < gap := by
        rw [Rat.div_def]
        have hinv : (2 : Rat)⁻¹ < 1 := by decide +kernel
        calc
          gap * (2 : Rat)⁻¹ < gap * 1 := Rat.mul_lt_mul_of_pos_left hinv hgap
          _ = gap := Rat.mul_one _
      have hcontra : gap <= gap / 2 := by
        calc
          gap <= a - b := hgap_le
          _ = qabs (a - b) := hqabs.symm
          _ <= eps.val := hcloseNM
          _ = gap / 2 := rfl
      have hnot : ¬ gap <= gap / 2 := by
        intro h
        exact False.elim (by grind)
      exact False.elim (hnot hcontra)
    · constructor <;> grind

theorem equiv_iff_allStagesOverlap {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) :
    x.Equiv y ↔ x.AllStagesOverlap y :=
  ⟨allStagesOverlap_of_equiv hx hy, RealCompute.allStagesOverlap_equiv⟩

theorem le_refl (x : RealCompute) (hx : x.Valid) : x.Le x := by
  intro n m
  have hover := (compareAt_overlap_iff x x n m).1
    (allStagesOverlap_refl x hx n m)
  exact hover.1

/-- For valid nested raw reals, a same-stage lower/upper comparison already
implies representation-level order at arbitrary pairs of stages.  Both input
boxes are refined to the finite common stage `max n m`; no completed real
value or limit is selected. -/
theorem le_of_sameStage {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid)
    (hsame : forall stage,
      (x.compute stage).lo <= (y.compute stage).hi) :
    x.Le y := by
  intro n m
  let common := max n m
  have hn : n <= common := Nat.le_max_left n m
  have hm : m <= common := Nat.le_max_right n m
  have hxnest := hx.2.1 n common hn
  have hynest := hy.2.1 m common hm
  exact Rat.le_trans hxnest.1
    (Rat.le_trans (hsame common) hynest.2.2)

theorem le_of_equiv {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) :
    x.Equiv y -> x.Le y := by
  intro hxy n m
  have hall := allStagesOverlap_of_equiv hx hy hxy
  have hover := (compareAt_overlap_iff x y n m).1 (hall n m)
  exact hover.1

theorem equiv_of_le_of_ge {x y : RealCompute}
    (hxy : x.Le y) (hyx : y.Le x) :
    x.Equiv y := by
  intro n
  apply (compareAt_overlap_iff x y n n).2
  exact ⟨hxy n n, hyx n n⟩

theorem le_antisymm {x y : RealCompute}
    (hxy : x.Le y) (hyx : y.Le x) :
    x.Equiv y := by
  exact equiv_of_le_of_ge hxy hyx

theorem equiv_iff_le_and_ge {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) :
    x.Equiv y ↔ x.Le y /\ y.Le x := by
  constructor
  · intro hxy
    exact ⟨le_of_equiv hx hy hxy, le_of_equiv hy hx (equiv_symm hxy)⟩
  · intro h
    exact equiv_of_le_of_ge h.1 h.2

theorem le_trans {x y z : RealCompute}
    (hy : y.Valid) :
    x.Le y -> y.Le z -> x.Le z := by
  intro hxy hyz n m
  by_cases hgood : (x.compute n).lo <= (z.compute m).hi
  · exact hgood
  · exfalso
    have hgap : 0 < (x.compute n).lo - (z.compute m).hi := by
      rw [←Rat.lt_iff_sub_pos]
      simpa [Rat.not_le] using hgood
    have htwo : (0 : Rat) < 2 := by
      exact (Rat.natCast_pos).2 (by omega : 0 < (2 : Nat))
    have hgapHalfPos : 0 < ((x.compute n).lo - (z.compute m).hi) / 2 := by
      rw [Rat.div_def]
      exact Rat.mul_pos hgap ((Rat.inv_pos).2 htwo)
    obtain ⟨k, hk⟩ := hy.2.2
      { val := ((x.compute n).lo - (z.compute m).hi) / 2,
        property := hgapHalfPos }
    have hxyk := hxy n k
    have hyzk := hyz k m
    have hsmall :
        (y.compute k).width <=
          ((x.compute n).lo - (z.compute m).hi) / 2 :=
      hk k (Nat.le_refl k)
    have hgap_le_width :
        (x.compute n).lo - (z.compute m).hi <= (y.compute k).width := by
      grind [QInterval.width, Rat.sub_eq_add_neg]
    have hhalf_lt :
        ((x.compute n).lo - (z.compute m).hi) / 2 <
          (x.compute n).lo - (z.compute m).hi := by
      rw [Rat.div_lt_iff htwo]
      grind
    have hgap_le_half :
        (x.compute n).lo - (z.compute m).hi <=
          ((x.compute n).lo - (z.compute m).hi) / 2 :=
      Rat.le_trans hgap_le_width hsmall
    have hne :
        (x.compute n).lo - (z.compute m).hi ≠
      ((x.compute n).lo - (z.compute m).hi) / 2 := by
      intro heq
      rw [←heq] at hhalf_lt
      exact Rat.lt_irrefl hhalf_lt
    have hgap_lt_half :
        (x.compute n).lo - (z.compute m).hi <
          ((x.compute n).lo - (z.compute m).hi) / 2 :=
      Rat.lt_of_le_of_ne hgap_le_half hne
    exact Rat.lt_irrefl (rat_lt_trans hgap_lt_half hhalf_lt)

private theorem equiv_trans_left {x y z : RealCompute}
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid)
    (hxy : x.SameStageOverlap y) (hyz : y.SameStageOverlap z)
    (n : Nat) : (x.compute n).lo <= (z.compute n).hi := by
  by_cases hgood : (x.compute n).lo <= (z.compute n).hi
  · exact hgood
  · exfalso
    have hgap : 0 < (x.compute n).lo - (z.compute n).hi := by
      rw [←Rat.lt_iff_sub_pos]
      simpa [Rat.not_le] using hgood
    have hthree : (0 : Rat) < 3 := by
      exact (Rat.natCast_pos).2 (by omega : 0 < (3 : Nat))
    have hgapThirdPos : 0 < ((x.compute n).lo - (z.compute n).hi) / 3 := by
      rw [Rat.div_def]
      exact Rat.mul_pos hgap ((Rat.inv_pos).2 hthree)
    obtain ⟨M, hsmall⟩ := hy.2.2
      { val := ((x.compute n).lo - (z.compute n).hi) / 3,
        property := hgapThirdPos }
    let m : Nat := max n M
    have hnm : n <= m := by
      dsimp [m]
      exact Nat.le_max_left n M
    have hMle : M <= m := by
      dsimp [m]
      exact Nat.le_max_right n M
    have hxNest := hx.2.1 n m hnm
    have hzNest := hz.2.1 n m hnm
    have hxyM := (compareAt_overlap_iff x y m m).1 (hxy m)
    have hyzM := (compareAt_overlap_iff y z m m).1 (hyz m)
    have hySmallLe :
        (y.compute m).width <= ((x.compute n).lo - (z.compute n).hi) / 3 :=
      hsmall m hMle
    have hyGapLe :
        (x.compute n).lo - (z.compute n).hi <= (y.compute m).width := by
      grind [QInterval.width, QInterval.Overlaps]
    have hthirdLt : ((x.compute n).lo - (z.compute n).hi) / 3 <
        (x.compute n).lo - (z.compute n).hi := by
      rw [Rat.div_lt_iff hthree]
      grind
    have hgapLeThird : (x.compute n).lo - (z.compute n).hi <=
        ((x.compute n).lo - (z.compute n).hi) / 3 :=
      Rat.le_trans hyGapLe hySmallLe
    have hgapLtThird : (x.compute n).lo - (z.compute n).hi <
        ((x.compute n).lo - (z.compute n).hi) / 3 :=
      Rat.lt_of_le_of_ne hgapLeThird (Rat.ne_of_gt hthirdLt)
    exact Rat.lt_irrefl (rat_lt_trans hgapLtThird hthirdLt)

theorem equiv_trans {x y z : RealCompute}
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid) :
    x.Equiv y -> y.Equiv z -> x.Equiv z := by
  intro hxy hyz
  have hxySame := sameStageOverlap_of_equiv hx hy hxy
  have hyzSame := sameStageOverlap_of_equiv hy hz hyz
  apply sameStageOverlap_equiv
  intro n
  apply (compareAt_overlap_iff x z n n).2
  constructor
  · exact equiv_trans_left hx hy hz hxySame hyzSame n
  · exact equiv_trans_left hz hy hx
      (sameStageOverlap_of_equiv hz hy (equiv_symm hyz))
      (sameStageOverlap_of_equiv hy hx (equiv_symm hxy)) n

theorem equiv_of_schedule_equiv {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid)
    (sigma tau : StageSchedule) :
    (schedule sigma x).Equiv (schedule tau y) -> x.Equiv y := by
  intro hscheduled
  have hsx : (schedule sigma x).Valid := schedule_valid x hx sigma
  have hty : (schedule tau y).Valid := schedule_valid y hy tau
  exact equiv_trans hx hsx hy
    (schedule_equiv x hx sigma)
    (equiv_trans hsx hty hy hscheduled
      (equiv_symm (schedule_equiv y hy tau)))

end RealCompute

end ComputableAnalysis

namespace ComputableAnalysis

private theorem rat_sub_self (q : Rat) : q - q = 0 := by
  cases q
  simp [Rat.sub_def]

namespace RealCompute

theorem ofRat_valid (q : Rat) : ValidCompute (fun _ : Nat => { lo := q, hi := q }) := by
  constructor
  · intro n
    show 0 <= q - q
    rw [rat_sub_self]
    exact Rat.le_refl
  · constructor
    · intro n m h
      simp
    · intro eps
      exact ⟨0, by
        intro n _hn
        show q - q <= eps.val
        rw [rat_sub_self]
        exact Rat.le_of_lt eps.property⟩

def ofRat (q : Rat) : RealCompute where
  compute := fun _ => { lo := q, hi := q }

instance : Coe Rat RealCompute where
  coe := ofRat

instance (n : Nat) : OfNat RealCompute n where
  ofNat := ofRat n

@[simp]
theorem ofRat_compute (q : Rat) (n : Nat) :
    (ofRat q).compute n = { lo := q, hi := q } := rfl

@[simp]
theorem coe_rat_compute (q : Rat) (n : Nat) :
    ((q : RealCompute).compute n) = { lo := q, hi := q } := rfl

theorem ofRat_equiv_self (q : Rat) : (ofRat q).Equiv (ofRat q) :=
  equiv_refl (ofRat q) (ofRat_valid q)

/-- A raw real name is rational when it is equivalent to an exact rational
name. The predicate is intended for valid raw names. -/
def Rational (x : RealCompute) : Prop :=
  Exists fun q : Rat => x.Equiv (ofRat q)

/-- A raw computable real is irrational when it is not equivalent to any
rational coercion.  This is most useful for valid raw algorithms, where
`Equiv` has the expected same-stage and transitive behavior. -/
def Irrational (x : RealCompute) : Prop :=
  forall q : Rat, ¬ x.Equiv (ofRat q)

theorem irrational_iff_not_rational (x : RealCompute) :
    x.Irrational ↔ ¬ x.Rational := by
  unfold Irrational Rational
  constructor
  · intro h ⟨q, hq⟩
    exact h q hq
  · intro h q hq
    exact h ⟨q, hq⟩

def interval (x : RealCompute) (n : Nat) : QInterval := x.compute n
def midpoint (x : RealCompute) (n : Nat) : Rat := (x.compute n).midpoint

end RealCompute

/-- One real computation together with its validity proof. -/
structure RealCompute.Certified where
  raw : RealCompute
  valid : raw.Valid

namespace RealCompute.Certified

def ofRaw (x : RealCompute) (h : x.Valid) : RealCompute.Certified :=
  ⟨x, h⟩

/-- Projection used by earlier calculus proofs. -/
abbrev preferred (x : RealCompute.Certified) : RealCompute := x.raw

def ofRat (q : Rat) : RealCompute.Certified :=
  ofRaw (RealCompute.ofRat q) (RealCompute.ofRat_valid q)

def compute (x : RealCompute.Certified) (n : Nat) : QInterval :=
  x.preferred.compute n

def rate (x : RealCompute.Certified) : RealCompute.Rate x.preferred.compute :=
  x.preferred.rate

def Equiv (x y : RealCompute.Certified) : Prop :=
  x.preferred.Equiv y.preferred

theorem equiv_refl (x : RealCompute.Certified) : x.Equiv x :=
  RealCompute.equiv_refl x.preferred x.valid

theorem equiv_symm {x y : RealCompute.Certified} : x.Equiv y -> y.Equiv x :=
  RealCompute.equiv_symm

theorem equiv_trans {x y z : RealCompute.Certified} : x.Equiv y -> y.Equiv z -> x.Equiv z :=
  RealCompute.equiv_trans x.valid y.valid z.valid

/-- A computable real is rational when it is equivalent to some rational real. -/
def Rational (x : RealCompute.Certified) : Prop :=
  x.preferred.Rational

theorem rational_iff_preferred_rational (x : RealCompute.Certified) :
    x.Rational ↔ x.preferred.Rational :=
  Iff.rfl

/-- Compatibility view for older code using the computation bundle. New
mathematical statements should use `ComputableAnalysis.Real.Irrational`; the raw-name
predicate remains the representation-level helper. -/
def Irrational (x : RealCompute.Certified) : Prop :=
  x.preferred.Irrational

theorem irrational_iff_preferred_irrational (x : RealCompute.Certified) :
    x.Irrational ↔ x.preferred.Irrational :=
  Iff.rfl

structure Representation (x : RealCompute.Certified) where
  raw : RealCompute
  valid : raw.Valid
  agrees : raw.Equiv x.preferred

/-- Any two certified representations of one abstract real compute the same
raw real.  This representation-level interoperability principle is used by
named views such as the various computations of pi and e. -/
theorem Representation.equiv {x : RealCompute.Certified} (source target : Representation x) :
    source.raw.Equiv target.raw :=
  RealCompute.equiv_trans source.valid x.valid target.valid source.agrees
    (RealCompute.equiv_symm target.agrees)

def preferredRepresentation (x : RealCompute.Certified) : Representation x where
  raw := x.preferred
  valid := x.valid
  agrees := RealCompute.equiv_refl x.preferred x.valid

def computeUsing {x : RealCompute.Certified} (rep : Representation x) (n : Nat) : QInterval :=
  rep.raw.compute n

theorem representation_same_real {x : RealCompute.Certified} (rep : Representation x) :
    (RealCompute.Certified.ofRaw rep.raw rep.valid).Equiv x :=
  rep.agrees

end RealCompute.Certified

/-- Raw real-valued function on rational inputs.

A single-variable function representation is a domain together with a stage
algorithm `x, n ↦ [a, b]`.  Validity is pointwise: for each fixed rational
`x` in the domain, the sequence in `n` is a raw real.

The computation field remains total on rationals so existing total-function
machinery can use it directly.  The attached domain records where the
representation is intended to be interpreted, and the optional rate metadata
may depend on a proof that the input lies in that domain.
-/
structure RealFunRaw where
  domain : Rat -> Prop := fun _ => True
  compute : Rat -> Nat -> QInterval
  rate : (x : Rat) -> domain x -> RealCompute.Rate (compute x) := fun _ _ => .unknown

namespace RealFunRaw

def entire : Rat -> Prop := fun _ => True

def applyCompute (f : RealFunRaw) (x : Rat) : Nat -> QInterval :=
  f.compute x

def exact (f : Rat -> Rat) : RealFunRaw where
  domain := entire
  compute := fun x _ => { lo := f x, hi := f x }

def Valid (f : RealFunRaw) : Prop :=
  forall x, f.domain x -> RealCompute.ValidCompute (applyCompute f x)

theorem exact_valid (f : Rat -> Rat) : (exact f).Valid := by
  intro x _hx
  exact RealCompute.ofRat_valid (f x)

/-! A function-level stage schedule.  This is the bridge between a raw
evaluator's native computation stages and a calculus interface that needs a
cofinal, possibly finer, evaluation schedule.  It changes only the exposed
algorithm; at every rational input it remains equivalent to the original
raw evaluator. -/

def stageSchedule (f : RealFunRaw) (sigma : RealCompute.StageSchedule) : RealFunRaw where
  domain := f.domain
  compute := fun x n => f.compute x (sigma.stage n)

theorem stageSchedule_valid {f : RealFunRaw} (hf : f.Valid)
    (sigma : RealCompute.StageSchedule) :
    (f.stageSchedule sigma).Valid := by
  intro x hx
  exact RealCompute.schedule_valid { compute := f.compute x } (hf x hx) sigma

theorem stageSchedule_apply_equiv {f : RealFunRaw} (hf : f.Valid)
    (sigma : RealCompute.StageSchedule) {x : Rat} (hx : f.domain x) :
    (RealCompute.schedule sigma ({ compute := f.compute x } : RealCompute)).Equiv
      ({ compute := f.compute x } : RealCompute) := by
  exact RealCompute.equiv_symm
    (RealCompute.schedule_equiv ({ compute := f.compute x } : RealCompute)
      (hf x hx) sigma)

theorem validAt {f : RealFunRaw} (h : f.Valid)
    {x : Rat} (hx : f.domain x) :
    RealCompute.ValidCompute (f.applyCompute x) :=
  h x hx

def apply (f : RealFunRaw) (_h : f.Valid) (x : Rat) (hx : f.domain x) : RealCompute where
  compute := applyCompute f x
  rate := f.rate x hx

end RealFunRaw

structure RealFunCert where
  raw : RealFunRaw
  valid : raw.Valid

/-- A partial rational-input real-valued function.

This is the proof-relevant version of the same `x, n ↦ [a, b]` notion: the
computation is only available together with a proof that the input is in the
domain, so undefined points cannot be assigned placeholder values.  Validity is
again pointwise in the input.
-/
structure PartialRealFunRaw where
  definedAt : Rat -> Prop
  compute : (x : Rat) -> definedAt x -> Nat -> QInterval
  rate :
    (x : Rat) -> (h : definedAt x) ->
      RealCompute.Rate (compute x h) := fun _ _ => .unknown

/-! A proof-independent evaluator for partial rational-input functions.

`PartialRealFunRaw` deliberately carries a domain proof into `compute`, which
is useful for ruling out undefined inputs but can make elaboration repeatedly
normalize proof arguments.  Many certified algorithms do not inspect that
proof.  This companion structure exposes that stable computation directly and
converts back to the proof-relevant interface without changing its semantics.
-/
structure StablePartialRealFunRaw where
  definedAt : Rat -> Prop
  compute : Rat -> Nat -> QInterval
  rate : (x : Rat) -> RealCompute.Rate (compute x) := fun _ => .unknown

def StablePartialRealFunRaw.toPartial
    (f : StablePartialRealFunRaw) : PartialRealFunRaw where
  definedAt := f.definedAt
  compute := fun x _hx n => f.compute x n
  rate := fun x _hx => f.rate x

@[simp] theorem StablePartialRealFunRaw.toPartial_compute
    (f : StablePartialRealFunRaw) (x : Rat) (hx : f.definedAt x) (n : Nat) :
    f.toPartial.compute x hx n = f.compute x n := rfl

namespace PartialRealFunRaw

def Valid (f : PartialRealFunRaw) : Prop :=
  forall x (hx : f.definedAt x), RealCompute.ValidCompute (f.compute x hx)

def evalRaw (f : PartialRealFunRaw)
    (x : Rat) (h : f.definedAt x) : RealCompute where
  compute := f.compute x h
  rate := f.rate x h

/-- Two partial rational-input real functions agree where both are defined.

This is the function-representation version of raw-real equality: at each
rational input in the common domain, the two output interval algorithms are
equivalent.  We do not make this a global equivalence relation, because
different representations may have different natural domains. -/
def AgreeOnOverlap (f g : PartialRealFunRaw) : Prop :=
  forall x hx hg, (f.evalRaw x hx).Equiv (g.evalRaw x hg)

def AgreeOnOverlapAllStages (f g : PartialRealFunRaw) : Prop :=
  forall x hx hg, (f.evalRaw x hx).AllStagesOverlap (g.evalRaw x hg)

theorem agreeOnOverlap_of_allStages {f g : PartialRealFunRaw} :
    f.AgreeOnOverlapAllStages g -> f.AgreeOnOverlap g := by
  intro h x hx hg
  exact RealCompute.allStagesOverlap_equiv (h x hx hg)

theorem agreeOnOverlap_symm {f g : PartialRealFunRaw} :
    f.AgreeOnOverlap g -> g.AgreeOnOverlap f := by
  intro h x hx hg
  exact RealCompute.equiv_symm (h x hg hx)
def apply (f : PartialRealFunRaw)
    (_validOnDomain : forall x h, RealCompute.ValidCompute (f.compute x h))
    (x : Rat) (h : f.definedAt x) : RealCompute where
  compute := f.compute x h
  rate := f.rate x h

def eval? (f : PartialRealFunRaw) (decideDomain : (x : Rat) -> Decidable (f.definedAt x))
    (x : Rat) (n : Nat) : Option QInterval :=
  haveI := decideDomain x
  if h : f.definedAt x then some (f.compute x h n) else none

end PartialRealFunRaw

/- An abstract partial function is a certified handle for one useful special
   function.  Its concrete representations may have different domains, so each
   registered implementation carries explicit agreement with the preferred
   representation on the intersection of those domains.  This avoids making
   an unjustified global claim about the function space. -/
structure PartialRealFunctionImplementation
    (preferred : PartialRealFunRaw) where
  raw : PartialRealFunRaw
  valid : raw.Valid
  agrees : preferred.AgreeOnOverlap raw

structure PartialRealFunction where
  preferred : PartialRealFunRaw
  valid : preferred.Valid
  implementations : List
    (PartialRealFunctionImplementation preferred) := []

namespace PartialRealFunction

structure Representation (f : PartialRealFunction) where
  raw : PartialRealFunRaw
  valid : raw.Valid
  agrees : raw.AgreeOnOverlap f.preferred

def ofRaw (raw : PartialRealFunRaw) (h : raw.Valid) : PartialRealFunction where
  preferred := raw
  valid := h
  implementations := []

def representations (f : PartialRealFunction) : List PartialRealFunRaw :=
  f.preferred :: f.implementations.map
    PartialRealFunctionImplementation.raw

theorem implementation_agrees_preferred {f : PartialRealFunction}
    (impl : PartialRealFunctionImplementation f.preferred) :
    impl.raw.AgreeOnOverlap f.preferred :=
  PartialRealFunRaw.agreeOnOverlap_symm impl.agrees

def preferredRepresentation (f : PartialRealFunction) : Representation f where
  raw := f.preferred
  valid := f.valid
  agrees := by
    intro x hx hx'
    exact RealCompute.equiv_refl (f.preferred.evalRaw x hx) (f.valid x hx)

def implementationRepresentation {f : PartialRealFunction}
    (impl : PartialRealFunctionImplementation f.preferred) : Representation f where
  raw := impl.raw
  valid := impl.valid
  agrees := implementation_agrees_preferred impl

/-! Two certified views of one abstract partial function can be compared on
their common domain once that domain is known to lie inside the preferred
domain.  This is the function-level analogue of `RealCompute.Certified.Representation.equiv`:
the preferred evaluator is the spanning node in the representation chain. -/
theorem Representation.equiv_on_common_domain
    {f : PartialRealFunction} (source target : Representation f)
    (hsource : forall x, source.raw.definedAt x -> f.preferred.definedAt x)
    {x : Rat} (hxs : source.raw.definedAt x)
    (hxt : target.raw.definedAt x) :
    (source.raw.evalRaw x hxs).Equiv (target.raw.evalRaw x hxt) := by
  have hxp : f.preferred.definedAt x := hsource x hxs
  have hs : (source.raw.evalRaw x hxs).Valid := by
    simpa [PartialRealFunRaw.evalRaw, RealCompute.Valid] using source.valid x hxs
  have hp : (f.preferred.evalRaw x hxp).Valid := by
    simpa [PartialRealFunRaw.evalRaw, RealCompute.Valid] using f.valid x hxp
  have ht : (target.raw.evalRaw x hxt).Valid := by
    simpa [PartialRealFunRaw.evalRaw, RealCompute.Valid] using target.valid x hxt
  exact RealCompute.equiv_trans hs hp ht (source.agrees x hxs hxp)
    (RealCompute.equiv_symm (target.agrees x hxt hxp))

def withAlternative (f : PartialRealFunction) (raw : PartialRealFunRaw)
    (hvalid : raw.Valid)
    (h : f.preferred.AgreeOnOverlap raw) : PartialRealFunction where
  preferred := f.preferred
  valid := f.valid
  implementations :=
    { raw := raw, valid := hvalid, agrees := h } :: f.implementations

/-! Register a partial-function implementation through any already certified
    representation.  The domain-cover hypothesis is explicit: the parent
    computation must be defined wherever the new computation and the preferred
    computation are both defined.  This is the function-level spanning-tree
    operation; it stores only the composed edge back to the preferred node. -/
def withAlternativeFrom (f : PartialRealFunction)
    (parent : Representation f) (raw : PartialRealFunRaw)
    (hvalid : raw.Valid)
    (hcover : forall x, raw.definedAt x -> f.preferred.definedAt x ->
      parent.raw.definedAt x)
    (h : forall x (hr : raw.definedAt x) (hp : f.preferred.definedAt x),
      (raw.evalRaw x hr).Equiv
        (parent.raw.evalRaw x (hcover x hr hp))) : PartialRealFunction where
  preferred := f.preferred
  valid := f.valid
  implementations :=
    { raw := raw
      valid := hvalid
      agrees := by
        intro x hp hr
        have hpValid : (f.preferred.evalRaw x hp).Valid := by
          simpa [PartialRealFunRaw.evalRaw, RealCompute.Valid] using f.valid x hp
        have hparentValid :
            (parent.raw.evalRaw x (hcover x hr hp)).Valid := by
          simpa [PartialRealFunRaw.evalRaw, RealCompute.Valid] using
            parent.valid x (hcover x hr hp)
        have hrawValid : (raw.evalRaw x hr).Valid := by
          simpa [PartialRealFunRaw.evalRaw, RealCompute.Valid] using hvalid x hr
        exact RealCompute.equiv_trans hpValid hparentValid hrawValid
          (RealCompute.equiv_symm (parent.agrees x (hcover x hr hp) hp))
          (RealCompute.equiv_symm (h x hr hp)) } ::
      f.implementations

theorem withAlternativeFrom_equiv_preferred (f : PartialRealFunction)
    (parent : Representation f) (raw : PartialRealFunRaw)
    (hvalid : raw.Valid)
    (hcover : forall x, raw.definedAt x -> f.preferred.definedAt x ->
      parent.raw.definedAt x)
    (h : forall x (hr : raw.definedAt x) (hp : f.preferred.definedAt x),
      (raw.evalRaw x hr).Equiv
        (parent.raw.evalRaw x (hcover x hr hp)))
    {x : Rat} (hr : raw.definedAt x) (hp : f.preferred.definedAt x) :
    (raw.evalRaw x hr).Equiv (f.preferred.evalRaw x hp) := by
  have hrawValid : (raw.evalRaw x hr).Valid := by
    simpa [PartialRealFunRaw.evalRaw, RealCompute.Valid] using hvalid x hr
  have hparentValid :
      (parent.raw.evalRaw x (hcover x hr hp)).Valid := by
    simpa [PartialRealFunRaw.evalRaw, RealCompute.Valid] using
      parent.valid x (hcover x hr hp)
  have hpValid : (f.preferred.evalRaw x hp).Valid := by
    simpa [PartialRealFunRaw.evalRaw, RealCompute.Valid] using f.valid x hp
  exact RealCompute.equiv_trans hrawValid hparentValid hpValid
    (h x hr hp) (parent.agrees x (hcover x hr hp) hp)

theorem withAlternativeFrom_overlaps_preferred (f : PartialRealFunction)
    (parent : Representation f) (raw : PartialRealFunRaw)
    (hvalid : raw.Valid)
    (hcover : forall x, raw.definedAt x -> f.preferred.definedAt x ->
      parent.raw.definedAt x)
    (h : forall x (hr : raw.definedAt x) (hp : f.preferred.definedAt x),
      (raw.evalRaw x hr).Equiv
        (parent.raw.evalRaw x (hcover x hr hp)))
    {x : Rat} (hr : raw.definedAt x) (hp : f.preferred.definedAt x)
    (stage : Nat) :
    QInterval.Overlaps (raw.compute x hr stage)
      (f.preferred.compute x hp stage) := by
  exact (RealCompute.compareAt_overlap_iff
    (raw.evalRaw x hr) (f.preferred.evalRaw x hp) stage stage).1
    (withAlternativeFrom_equiv_preferred f parent raw hvalid hcover h hr hp stage)

end PartialRealFunction

structure EffectiveContinuous (f : RealFunRaw) where
  inputRadius : Nat -> QPos
  good : forall x y n,
    qabs (y - x) <= (inputRadius n).val ->
    qabs ((f.compute y n).midpoint - (f.compute x n).midpoint) <= (1 / (n : Rat))

structure EffectiveDerivativeExact (f g : Rat -> Rat) where
  stepRadius : QPos -> QPos
  good : forall x h eps,
    0 < h -> h <= (stepRadius eps).val ->
    qabs (((f (x + h) - f x) / h) - g x) <= eps.val

end ComputableAnalysis

namespace ComputableAnalysis

structure QComplex where
  re : Rat
  im : Rat
deriving Repr, DecidableEq

namespace QComplex

/-- Coordinatewise order on rational complex points.  This is a bookkeeping
order for rectangular boxes, not the field order of a number system. -/
instance : LE QComplex where
  le z w := z.re <= w.re /\ z.im <= w.im

@[simp] theorem le_def (z w : QComplex) :
    z <= w ↔ z.re <= w.re /\ z.im <= w.im := Iff.rfl

theorem le_refl (z : QComplex) : z <= z :=
  ⟨Rat.le_refl, Rat.le_refl⟩

instance decidableLE (z w : QComplex) : Decidable (z <= w) := by
  change Decidable (z.re <= w.re /\ z.im <= w.im)
  infer_instance

theorem le_trans {z w u : QComplex} (hzw : z <= w) (hwu : w <= u) : z <= u :=
  ⟨Rat.le_trans hzw.1 hwu.1, Rat.le_trans hzw.2 hwu.2⟩

theorem le_antisymm {z w : QComplex} (hzw : z <= w) (hwz : w <= z) : z = w := by
  cases z
  cases w
  simp at hzw hwz ⊢
  exact ⟨Rat.le_antisymm hzw.1 hwz.1, Rat.le_antisymm hzw.2 hwz.2⟩

def ofRat (q : Rat) : QComplex := { re := q, im := 0 }
def zero : QComplex := { re := 0, im := 0 }
def one : QComplex := { re := 1, im := 0 }
def add (z w : QComplex) : QComplex := { re := z.re + w.re, im := z.im + w.im }
def neg (z : QComplex) : QComplex := { re := -z.re, im := -z.im }
def sub (z w : QComplex) : QComplex := add z (neg w)
def scaleRat (r : Rat) (z : QComplex) : QComplex :=
  { re := r * z.re, im := r * z.im }
def mul (z w : QComplex) : QComplex := { re := z.re * w.re - z.im * w.im, im := z.re * w.im + z.im * w.re }
def conj (z : QComplex) : QComplex := { re := z.re, im := -z.im }

/-- The executable natural power of a rational-complex coordinate pair. -/
def natPow (z : QComplex) : Nat -> QComplex
  | 0 => one
  | n + 1 => mul (natPow z n) z

theorem natPow_succ (z : QComplex) (n : Nat) :
    natPow z (n + 1) = mul (natPow z n) z := by
  rfl

theorem conj_mul (z w : QComplex) :
    conj (mul z w) = mul (conj z) (conj w) := by
  cases z
  cases w
  simp [conj, mul]
  constructor <;> grind [Rat.add_assoc, Rat.add_comm, Rat.mul_assoc,
    Rat.mul_comm, Rat.mul_add, Rat.add_mul, Rat.neg_mul, Rat.mul_neg,
    Rat.neg_neg, Rat.sub_eq_add_neg]

theorem conj_one : conj one = one := by
  decide +kernel

theorem conj_add (z w : QComplex) :
    conj (add z w) = add (conj z) (conj w) := by
  cases z
  cases w
  simp [conj, add]
  grind [Rat.neg_add]

theorem conj_neg (z : QComplex) : conj (neg z) = neg (conj z) := by
  cases z
  simp [conj, neg]

theorem conj_scaleRat (r : Rat) (z : QComplex) :
    conj (scaleRat r z) = scaleRat r (conj z) := by
  cases z
  simp [conj, scaleRat]
  grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

theorem conj_natPow (z : QComplex) (n : Nat) :
    conj (natPow z n) = natPow (conj z) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [natPow_succ, conj_mul, ih, natPow_succ]

theorem natPow_mul (z w : QComplex) (n : Nat) :
    natPow (mul z w) n = mul (natPow z n) (natPow w n) := by
  induction n with
  | zero =>
      change QComplex.one = QComplex.mul QComplex.one QComplex.one
      decide +kernel
  | succ n ih =>
      rw [natPow_succ, ih, natPow_succ, natPow_succ]
      cases z
      cases w
      simp [mul]
      constructor <;> grind [Rat.add_assoc, Rat.add_comm, Rat.mul_assoc,
        Rat.mul_comm, Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg]

def coordDist (z w : QComplex) : Rat := max (qabs (z.re - w.re)) (qabs (z.im - w.im))
def normSq (z : QComplex) : Rat := z.re * z.re + z.im * z.im

theorem normSq_conj (z : QComplex) :
    normSq (conj z) = normSq z := by
  cases z
  simp [normSq, conj]
  grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

theorem normSq_mul (z w : QComplex) :
    normSq (mul z w) = normSq z * normSq w := by
  cases z
  cases w
  simp [normSq, mul]
  grind [Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg, Rat.neg_mul,
    Rat.mul_neg, Rat.neg_neg]

theorem normSq_scaleRat (r : Rat) (z : QComplex) :
    normSq (scaleRat r z) = r * r * normSq z := by
  cases z
  simp [normSq, scaleRat]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul]

def inv? (z : QComplex) : Option QComplex :=
  let n := normSq z
  if n = 0 then
    none
  else
    some { re := z.re / n, im := -z.im / n }
def div? (z w : QComplex) : Option QComplex := (inv? w).map (mul z)

theorem normSq_eq_zero_iff {z : QComplex} :
    normSq z = 0 ↔ z = zero := by
  constructor
  · intro h
    cases z with
    | mk re im =>
      have hre_nonneg : 0 <= re * re := rat_square_nonneg_basic re
      have him_nonneg : 0 <= im * im := rat_square_nonneg_basic im
      simp [normSq] at h
      have hre : re * re = 0 := by
        grind
      have him : im * im = 0 := by
        grind
      have hre0 : re = 0 := by
        rcases Rat.mul_eq_zero.mp hre with hzero | hzero <;> exact hzero
      have him0 : im = 0 := by
        rcases Rat.mul_eq_zero.mp him with hzero | hzero <;> exact hzero
      subst re
      subst im
      rfl
  · intro h
    subst z
    simp only [normSq, QComplex.zero, Rat.zero_mul, Rat.mul_zero]
    exact Rat.add_zero 0

theorem mul_inv?_eq_one {z : QComplex} (hnorm : normSq z ≠ 0) :
    (inv? z).map (mul z) = some one := by
  cases z with
  | mk re im =>
    change re * re + im * im ≠ 0 at hnorm
    simp [inv?, normSq, mul, one, hnorm]
    constructor
    · rw [Rat.div_def]
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
        Rat.mul_inv_cancel]
    · rw [Rat.div_def]
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
        Rat.mul_inv_cancel]

theorem exists_mul_inverse_of_normSq_ne_zero {z : QComplex}
    (hnorm : normSq z ≠ 0) :
    Exists fun zi : QComplex => mul z zi = one := by
  have hmap := mul_inv?_eq_one hnorm
  cases h : inv? z with
  | none =>
      rw [h] at hmap
      simp at hmap
  | some zi =>
      refine ⟨zi, ?_⟩
      simpa [h] using hmap

theorem mul_assoc_cert (x y z : QComplex) :
    mul (mul x y) z = mul x (mul y z) := by
  cases x
  cases y
  cases z
  simp [mul]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem mul_add_cert (x y z : QComplex) :
    mul x (add y z) = add (mul x y) (mul x z) := by
  cases x
  cases y
  cases z
  simp [mul, add]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem add_mul_cert (x y z : QComplex) :
    mul (add x y) z = add (mul x z) (mul y z) := by
  cases x
  cases y
  cases z
  simp [mul, add]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem mul_one_cert (x : QComplex) : mul x one = x := by
  cases x
  simp [mul, one]
  exact ⟨by grind [Rat.sub_eq_add_neg], Rat.zero_add _⟩

theorem natPow_add (z : QComplex) (m n : Nat) :
    natPow z (m + n) = mul (natPow z m) (natPow z n) := by
  induction n with
  | zero =>
      simp only [Nat.add_zero, natPow]
      exact (mul_one_cert _).symm
  | succ n ih =>
      rw [show m + (n + 1) = (m + n) + 1 by omega,
        natPow_succ, ih, natPow_succ]
      exact mul_assoc_cert _ _ _

theorem mul_neg_cert (x y : QComplex) : mul x (neg y) = neg (mul x y) := by
  cases x
  cases y
  simp [mul, neg]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem neg_mul_cert (x y : QComplex) : mul (neg x) y = neg (mul x y) := by
  cases x
  cases y
  simp [mul, neg]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

instance : OfNat QComplex n where
  ofNat := ofRat n

instance : HAdd QComplex QComplex QComplex where
  hAdd := add

instance : Neg QComplex where
  neg := neg

instance : HSub QComplex QComplex QComplex where
  hSub := sub

instance : HMul QComplex QComplex QComplex where
  hMul := mul

end QComplex

structure QBox where
  lo : QComplex
  hi : QComplex
deriving Repr, DecidableEq

namespace QBox

def width (B : QBox) : Rat := B.hi.re - B.lo.re
def height (B : QBox) : Rat := B.hi.im - B.lo.im
def center (B : QBox) : QComplex := { re := (B.lo.re + B.hi.re) / 2, im := (B.lo.im + B.hi.im) / 2 }

/-- A rational box is ordered when its lower endpoint is below its upper
endpoint in the coordinatewise order on rational complex points. -/
def Ordered (B : QBox) : Prop := B.lo <= B.hi

/-- `inner` is nested in `outer` when both endpoints are contained
coordinatewise. -/
def NestedIn (inner outer : QBox) : Prop :=
  outer.lo <= inner.lo /\ inner.hi <= outer.hi

def Overlaps (A B : QBox) : Prop := A.lo <= B.hi /\ B.lo <= A.hi

/-- Coordinatewise conjugation of a rational complex box.  The imaginary
    endpoints reverse, while the real endpoints are unchanged. -/
def conj (B : QBox) : QBox :=
  { lo := { re := B.lo.re, im := -B.hi.im }
    hi := { re := B.hi.re, im := -B.lo.im } }

@[simp] theorem conj_conj (B : QBox) : conj (conj B) = B := by
  cases B
  simp [conj, QComplex.conj]

instance overlapsDecidable (A B : QBox) : Decidable (Overlaps A B) := by
  unfold Overlaps
  infer_instance

def overlaps (A B : QBox) : Bool := decide (Overlaps A B)
def widthHeightOk (B : QBox) (eps : QPos) : Bool := decide (0 <= B.width /\ B.width <= eps.val /\ 0 <= B.height /\ B.height <= eps.val)

theorem ordered_iff_width_height_nonneg (B : QBox) :
    B.Ordered ↔ 0 <= B.width /\ 0 <= B.height := by
  unfold Ordered width height
  simp [Rat.sub_eq_add_neg]
  grind

private def displayEndpointStrings (lo hi : Rat) : String × String :=
  if lo = hi then
    let s := QInterval.ratRepeatingDecimal lo
    (s, s)
  else
    QInterval.endpointDecimalsToFirstDifference lo hi

private def displayHasLeadingMinus (s : String) : Bool :=
  match s.toList with
  | '-' :: _ => true
  | _ => false

private def displayStripLeadingMinus (s : String) : String :=
  match s.toList with
  | '-' :: chars => String.ofList chars
  | _ => s

private def displaySignedImag (s : String) : String :=
  if displayHasLeadingMinus s then
    " - i " ++ displayStripLeadingMinus s
  else
    " + i " ++ s

private def displayComplexFromStrings (re im : String) : String :=
  re ++ displaySignedImag im

def display (B : QBox) : String :=
  let re := displayEndpointStrings B.lo.re B.hi.re
  let im := displayEndpointStrings B.lo.im B.hi.im
  let lo := displayComplexFromStrings re.1 im.1
  let hi := displayComplexFromStrings re.2 im.2
  let width := displayComplexFromStrings
    (QInterval.widthDecimal B.width) (QInterval.widthDecimal B.height)
  "[" ++ lo ++ ", " ++ hi ++ "] width = " ++ width

end QBox

namespace ComplexCompute

def WidthsShrinkToZero (compute : Nat -> QBox) : Prop :=
  forall eps : QPos, Exists fun N : Nat =>
    forall n : Nat, N <= n ->
      (compute n).width <= eps.val /\ (compute n).height <= eps.val

/-- A raw complex algorithm is valid when every stage is an ordered rational
box, later boxes nest inside earlier boxes, and both coordinate widths tend to
zero.  No fixed speed such as `1/n` is part of this definition. -/
def ValidCompute (compute : Nat -> QBox) : Prop :=
  (forall n, 0 <= (compute n).width /\ 0 <= (compute n).height) /\
  (forall n m, n <= m ->
    (compute n).lo.re <= (compute m).lo.re /\
    (compute m).hi.re <= (compute n).hi.re /\
    (compute n).lo.im <= (compute m).lo.im /\
    (compute m).hi.im <= (compute n).hi.im) /\
  WidthsShrinkToZero compute

/-- Optional convergence-rate metadata for a raw complex-box algorithm.

The bound applies to both coordinate widths.  As for `RealCompute.Rate`, this is
metadata on the algorithm, not a second kind of complex number. -/
inductive Rate (compute : Nat -> QBox) where
  | unknown
  | power
      (start : Nat)
      (constant : Rat)
      (power : Nat)
      (power_pos : 0 < power)
      (width_height_le : forall n : Nat, start <= n ->
        (compute n).width <= constant / (n : Rat) ^ power /\
        (compute n).height <= constant / (n : Rat) ^ power)
  | geometric
      (start : Nat)
      (constant : Rat)
      (ratio : Rat)
      (ratio_nonneg : 0 <= ratio)
      (ratio_lt_one : ratio < 1)
      (width_height_le : forall n : Nat, start <= n ->
        (compute n).width <= constant * ratio ^ n /\
        (compute n).height <= constant * ratio ^ n)

end ComplexCompute

/-- Raw box-sequence algorithm for a complex number. -/
structure ComplexCompute where
  compute : Nat -> QBox
  rate : ComplexCompute.Rate compute := .unknown

namespace ComplexCompute

def Valid (z : ComplexCompute) : Prop := ValidCompute z.compute

theorem valid_ordered {compute : Nat -> QBox}
    (h : ValidCompute compute) (n : Nat) : (compute n).Ordered :=
  (QBox.ordered_iff_width_height_nonneg (compute n)).2 (h.1 n)

theorem valid_nestedIn {compute : Nat -> QBox}
    (h : ValidCompute compute) {n m : Nat} (hnm : n <= m) :
    QBox.NestedIn (compute m) (compute n) := by
  have hnest := h.2.1 n m hnm
  exact ⟨⟨hnest.1, hnest.2.2.1⟩, ⟨hnest.2.1, hnest.2.2.2⟩⟩

structure CompareAt where
  left : Bool
  right : Bool
  below : Bool
  above : Bool
deriving Repr, DecidableEq

namespace CompareAt

def overlap : CompareAt :=
  { left := false, right := false, below := false, above := false }

private def appendDirection (s direction : String) (present : Bool) : String :=
  if present then
    if s = "" then direction else s ++ ", " ++ direction
  else
    s

def directions (c : CompareAt) : String :=
  appendDirection
    (appendDirection
      (appendDirection
        (appendDirection "" "left" c.left)
        "right" c.right)
      "below" c.below)
    "above" c.above

def display (c : CompareAt) : String :=
  if c = overlap then
    "overlap"
  else
    "separated(" ++ directions c ++ ")"

end CompareAt

def compareBoxes (A B : QBox) : CompareAt :=
  { left := decide (A.hi.re < B.lo.re),
    right := decide (B.hi.re < A.lo.re),
    below := decide (A.hi.im < B.lo.im),
    above := decide (B.hi.im < A.lo.im) }

theorem compareBoxes_overlap_iff (A B : QBox) :
    Iff (compareBoxes A B = .overlap) (QBox.Overlaps A B) := by
  unfold compareBoxes QBox.Overlaps
  simp [CompareAt.overlap]
  grind

def compareAt (z w : ComplexCompute) (nz : Nat) (nw : Nat := nz) : CompareAt :=
  compareBoxes (z.compute nz) (w.compute nw)

theorem compareAt_overlap_iff (z w : ComplexCompute) (nz nw : Nat) :
    Iff (compareAt z w nz nw = .overlap)
      (QBox.Overlaps (z.compute nz) (w.compute nw)) :=
  compareBoxes_overlap_iff (z.compute nz) (w.compute nw)

/-- Same-stage overlap of complex-box computations. -/
def SameStageOverlap (z w : ComplexCompute) : Prop :=
  forall n, compareAt z w n = .overlap

/--
Two raw complex representatives are equivalent when their box computations
overlap at every common stage.
-/
def Equiv (z w : ComplexCompute) : Prop :=
  z.SameStageOverlap w

theorem sameStageOverlap_equiv {z w : ComplexCompute} :
    z.SameStageOverlap w -> z.Equiv w := by
  intro h
  exact h

/-- Stronger than `Equiv`: every box of one raw algorithm overlaps every box
of the other, even at different stages. -/
def AllStagesOverlap (z w : ComplexCompute) : Prop :=
  forall n m, compareAt z w n m = .overlap

theorem allStagesOverlap_equiv {z w : ComplexCompute} :
    z.AllStagesOverlap w -> z.Equiv w := by
  intro h
  exact sameStageOverlap_equiv (fun n => h n n)

theorem equiv_refl (z : ComplexCompute) (hz : z.Valid) : z.Equiv z := by
  apply sameStageOverlap_equiv
  intro eps
  have hwidth : 0 <= (z.compute eps).width := (hz.1 eps).1
  have hheight : 0 <= (z.compute eps).height := (hz.1 eps).2
  have hre : (z.compute eps).lo.re <= (z.compute eps).hi.re := by
    unfold QBox.width at hwidth
    grind [Rat.sub_eq_add_neg]
  have him : (z.compute eps).lo.im <= (z.compute eps).hi.im := by
    unfold QBox.height at hheight
    grind [Rat.sub_eq_add_neg]
  exact (compareAt_overlap_iff z z eps eps).2
    ⟨⟨hre, him⟩, ⟨hre, him⟩⟩

theorem equiv_symm {z w : ComplexCompute} : z.Equiv w -> w.Equiv z := by
  intro h n
  have hover := (compareAt_overlap_iff z w n n).1 (h n)
  exact (compareAt_overlap_iff w z n n).2 ⟨hover.2, hover.1⟩

theorem sameStageOverlap_of_equiv {z w : ComplexCompute}
    (_hz : z.Valid) (_hw : w.Valid) :
    z.Equiv w -> z.SameStageOverlap w := by
  intro hzw
  exact hzw

theorem allStagesOverlap_of_sameStageOverlap {z w : ComplexCompute}
    (hz : z.Valid) (hw : w.Valid) :
    z.SameStageOverlap w -> z.AllStagesOverlap w := by
  intro hzw n m
  rcases Nat.le_total n m with hnm | hmn
  · have hznest := hz.2.1 n m hnm
    have hzw_m := (compareAt_overlap_iff z w m m).1 (hzw m)
    apply (compareAt_overlap_iff z w n m).2
    exact ⟨
      ⟨Rat.le_trans hznest.1 hzw_m.1.1,
        Rat.le_trans hznest.2.2.1 hzw_m.1.2⟩,
      ⟨Rat.le_trans hzw_m.2.1 hznest.2.1,
        Rat.le_trans hzw_m.2.2 hznest.2.2.2⟩⟩
  · have hwnest := hw.2.1 m n hmn
    have hzw_n := (compareAt_overlap_iff z w n n).1 (hzw n)
    apply (compareAt_overlap_iff z w n m).2
    exact ⟨
      ⟨Rat.le_trans hzw_n.1.1 hwnest.2.1,
        Rat.le_trans hzw_n.1.2 hwnest.2.2.2⟩,
      ⟨Rat.le_trans hwnest.1 hzw_n.2.1,
        Rat.le_trans hwnest.2.2.1 hzw_n.2.2⟩⟩

theorem allStagesOverlap_of_equiv {z w : ComplexCompute}
    (hz : z.Valid) (hw : w.Valid) :
    z.Equiv w -> z.AllStagesOverlap w :=
  fun hzw => allStagesOverlap_of_sameStageOverlap hz hw
    (sameStageOverlap_of_equiv hz hw hzw)

theorem equiv_iff_allStagesOverlap {z w : ComplexCompute}
    (hz : z.Valid) (hw : w.Valid) :
    z.Equiv w ↔ z.AllStagesOverlap w :=
  ⟨allStagesOverlap_of_equiv hz hw, ComplexCompute.allStagesOverlap_equiv⟩

private theorem equiv_trans_re_left {x y z : ComplexCompute}
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid)
    (hxy : x.SameStageOverlap y) (hyz : y.SameStageOverlap z)
    (n : Nat) : (x.compute n).lo.re <= (z.compute n).hi.re := by
  by_cases hgood : (x.compute n).lo.re <= (z.compute n).hi.re
  · exact hgood
  · exfalso
    have hgap : 0 < (x.compute n).lo.re - (z.compute n).hi.re := by
      rw [←Rat.lt_iff_sub_pos]
      simpa [Rat.not_le] using hgood
    have hthree : (0 : Rat) < 3 := by
      exact (Rat.natCast_pos).2 (by omega : 0 < (3 : Nat))
    have hgapThirdPos :
        0 < ((x.compute n).lo.re - (z.compute n).hi.re) / 3 := by
      rw [Rat.div_def]
      exact Rat.mul_pos hgap ((Rat.inv_pos).2 hthree)
    obtain ⟨M, hsmall⟩ := hy.2.2
      { val := ((x.compute n).lo.re - (z.compute n).hi.re) / 3,
        property := hgapThirdPos }
    let m : Nat := max n M
    have hnm : n <= m := by
      dsimp [m]
      exact Nat.le_max_left n M
    have hMle : M <= m := by
      dsimp [m]
      exact Nat.le_max_right n M
    have hxNest := hx.2.1 n m hnm
    have hzNest := hz.2.1 n m hnm
    have hxyM := (compareAt_overlap_iff x y m m).1 (hxy m)
    have hyzM := (compareAt_overlap_iff y z m m).1 (hyz m)
    have hySmallLe :
        (y.compute m).width <=
          ((x.compute n).lo.re - (z.compute n).hi.re) / 3 :=
      (hsmall m hMle).1
    have hyGapLe :
        (x.compute n).lo.re - (z.compute n).hi.re <=
          (y.compute m).width := by
      grind [QBox.width, QBox.Overlaps, QComplex.le_def, Rat.sub_eq_add_neg]
    have hthirdLt :
        ((x.compute n).lo.re - (z.compute n).hi.re) / 3 <
          (x.compute n).lo.re - (z.compute n).hi.re := by
      rw [Rat.div_lt_iff hthree]
      grind
    have hgapLeThird :
        (x.compute n).lo.re - (z.compute n).hi.re <=
          ((x.compute n).lo.re - (z.compute n).hi.re) / 3 :=
      Rat.le_trans hyGapLe hySmallLe
    have hgapLtThird :
        (x.compute n).lo.re - (z.compute n).hi.re <
          ((x.compute n).lo.re - (z.compute n).hi.re) / 3 :=
      Rat.lt_of_le_of_ne hgapLeThird (Rat.ne_of_gt hthirdLt)
    exact Rat.lt_irrefl (rat_lt_trans hgapLtThird hthirdLt)

private theorem equiv_trans_im_left {x y z : ComplexCompute}
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid)
    (hxy : x.SameStageOverlap y) (hyz : y.SameStageOverlap z)
    (n : Nat) : (x.compute n).lo.im <= (z.compute n).hi.im := by
  by_cases hgood : (x.compute n).lo.im <= (z.compute n).hi.im
  · exact hgood
  · exfalso
    have hgap : 0 < (x.compute n).lo.im - (z.compute n).hi.im := by
      rw [←Rat.lt_iff_sub_pos]
      simpa [Rat.not_le] using hgood
    have hthree : (0 : Rat) < 3 := by
      exact (Rat.natCast_pos).2 (by omega : 0 < (3 : Nat))
    have hgapThirdPos :
        0 < ((x.compute n).lo.im - (z.compute n).hi.im) / 3 := by
      rw [Rat.div_def]
      exact Rat.mul_pos hgap ((Rat.inv_pos).2 hthree)
    obtain ⟨M, hsmall⟩ := hy.2.2
      { val := ((x.compute n).lo.im - (z.compute n).hi.im) / 3,
        property := hgapThirdPos }
    let m : Nat := max n M
    have hnm : n <= m := by
      dsimp [m]
      exact Nat.le_max_left n M
    have hMle : M <= m := by
      dsimp [m]
      exact Nat.le_max_right n M
    have hxNest := hx.2.1 n m hnm
    have hzNest := hz.2.1 n m hnm
    have hxyM := (compareAt_overlap_iff x y m m).1 (hxy m)
    have hyzM := (compareAt_overlap_iff y z m m).1 (hyz m)
    have hySmallLe :
        (y.compute m).height <=
          ((x.compute n).lo.im - (z.compute n).hi.im) / 3 :=
      (hsmall m hMle).2
    have hyGapLe :
        (x.compute n).lo.im - (z.compute n).hi.im <=
          (y.compute m).height := by
      grind [QBox.height, QBox.Overlaps, QComplex.le_def, Rat.sub_eq_add_neg]
    have hthirdLt :
        ((x.compute n).lo.im - (z.compute n).hi.im) / 3 <
          (x.compute n).lo.im - (z.compute n).hi.im := by
      rw [Rat.div_lt_iff hthree]
      grind
    have hgapLeThird :
        (x.compute n).lo.im - (z.compute n).hi.im <=
          ((x.compute n).lo.im - (z.compute n).hi.im) / 3 :=
      Rat.le_trans hyGapLe hySmallLe
    have hgapLtThird :
        (x.compute n).lo.im - (z.compute n).hi.im <
          ((x.compute n).lo.im - (z.compute n).hi.im) / 3 :=
      Rat.lt_of_le_of_ne hgapLeThird (Rat.ne_of_gt hthirdLt)
    exact Rat.lt_irrefl (rat_lt_trans hgapLtThird hthirdLt)

theorem equiv_trans {x y z : ComplexCompute}
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid) :
    x.Equiv y -> y.Equiv z -> x.Equiv z := by
  intro hxy hyz
  have hxySame := sameStageOverlap_of_equiv hx hy hxy
  have hyzSame := sameStageOverlap_of_equiv hy hz hyz
  have hyxSame := sameStageOverlap_of_equiv hy hx (equiv_symm hxy)
  have hzySame := sameStageOverlap_of_equiv hz hy (equiv_symm hyz)
  apply sameStageOverlap_equiv
  intro n
  apply (compareAt_overlap_iff x z n n).2
  exact ⟨
    ⟨equiv_trans_re_left hx hy hz hxySame hyzSame n,
      equiv_trans_im_left hx hy hz hxySame hyzSame n⟩,
    ⟨equiv_trans_re_left hz hy hx hzySame hyxSame n,
      equiv_trans_im_left hz hy hx hzySame hyxSame n⟩⟩

def ofQComplex (z : QComplex) : ComplexCompute where compute := fun _ => { lo := z, hi := z }

theorem ofQComplex_valid (z : QComplex) :
    (ofQComplex z).Valid := by
  constructor
  · intro n
    constructor
    · show 0 <= z.re - z.re
      grind
    · show 0 <= z.im - z.im
      grind
  · constructor
    · intro n m hnm
      simp [ofQComplex]
    · intro eps
      exact ⟨0, by
        intro n hn
        constructor
        · show ((ofQComplex z).compute n).width <= eps.val
          simp [ofQComplex, QBox.width]
          have hzero : z.re - z.re = 0 := by grind
          rw [hzero]
          exact Rat.le_of_lt eps.property
        · show ((ofQComplex z).compute n).height <= eps.val
          simp [ofQComplex, QBox.height]
          have hzero : z.im - z.im = 0 := by grind
          rw [hzero]
          exact Rat.le_of_lt eps.property⟩

def center (z : ComplexCompute) (n : Nat) : QComplex := (z.compute n).center

/-- The real coordinate of a certified complex-box computation, kept as its
own raw real interval algorithm. -/
def realPart (z : ComplexCompute) : RealCompute where
  compute := fun n =>
    { lo := (z.compute n).lo.re, hi := (z.compute n).hi.re }

/-- The imaginary coordinate of a certified complex-box computation, kept as
its own raw real interval algorithm. -/
def imagPart (z : ComplexCompute) : RealCompute where
  compute := fun n =>
    { lo := (z.compute n).lo.im, hi := (z.compute n).hi.im }

theorem realPart_valid {z : ComplexCompute} (hz : z.Valid) :
    z.realPart.Valid := by
  constructor
  · intro n
    exact (hz.1 n).1
  · constructor
    · intro n m hnm
      have hnest := hz.2.1 n m hnm
      have hordered := (hz.1 m).1
      exact ⟨hnest.1, by
        change (z.compute m).lo.re <= (z.compute m).hi.re
        unfold QBox.width at hordered
        grind [Rat.sub_eq_add_neg], hnest.2.1⟩
    · intro eps
      obtain ⟨N, hN⟩ := hz.2.2 eps
      exact ⟨N, fun n hn => (hN n hn).1⟩

theorem imagPart_valid {z : ComplexCompute} (hz : z.Valid) :
    z.imagPart.Valid := by
  constructor
  · intro n
    exact (hz.1 n).2
  · constructor
    · intro n m hnm
      have hnest := hz.2.1 n m hnm
      have hordered := (hz.1 m).2
      exact ⟨hnest.2.2.1, by
        change (z.compute m).lo.im <= (z.compute m).hi.im
        unfold QBox.height at hordered
        grind [Rat.sub_eq_add_neg], hnest.2.2.2⟩
    · intro eps
      obtain ⟨N, hN⟩ := hz.2.2 eps
      exact ⟨N, fun n hn => (hN n hn).2⟩

theorem realPart_equiv {z w : ComplexCompute} (hzw : z.Equiv w) :
    z.realPart.Equiv w.realPart := by
  intro n
  have hover := (compareAt_overlap_iff z w n n).1 (hzw n)
  apply (RealCompute.compareAt_overlap_iff z.realPart w.realPart n n).2
  exact ⟨hover.1.1, hover.2.1⟩

theorem imagPart_equiv {z w : ComplexCompute} (hzw : z.Equiv w) :
    z.imagPart.Equiv w.imagPart := by
  intro n
  have hover := (compareAt_overlap_iff z w n n).1 (hzw n)
  apply (RealCompute.compareAt_overlap_iff z.imagPart w.imagPart n n).2
  exact ⟨hover.1.2, hover.2.2⟩

/-- Embed a raw real interval algorithm as a raw complex-box algorithm on the
real axis. -/
def ofRealCompute (x : RealCompute) : ComplexCompute where
  compute := fun n =>
    let I := x.compute n
    { lo := { re := I.lo, im := 0 },
      hi := { re := I.hi, im := 0 } }

instance : Coe RealCompute ComplexCompute where
  coe := ofRealCompute

theorem ofRealCompute_valid (x : RealCompute) (hx : x.Valid) :
    (ofRealCompute x).Valid := by
  constructor
  · intro n
    constructor
    · exact hx.1 n
    · simp [ofRealCompute, QBox.height, Rat.sub_eq_add_neg]
      grind
  · constructor
    · intro n m hnm
      have hnest := hx.2.1 n m hnm
      exact ⟨hnest.1, hnest.2.2, by simp [ofRealCompute], by simp [ofRealCompute]⟩
    · intro eps
      obtain ⟨N, hN⟩ := hx.2.2 eps
      exact ⟨N, by
        intro n hn
        constructor
        · exact hN n hn
        · have heps : 0 <= eps.val := Rat.le_of_lt eps.property
          simp [ofRealCompute, QBox.height, Rat.sub_eq_add_neg]
          grind
      ⟩
theorem coe_realCompute_valid (x : RealCompute) (hx : x.Valid) :
    ((x : ComplexCompute).Valid) :=
  ofRealCompute_valid x hx

theorem ofRealCompute_equiv_of_equiv {x y : RealCompute}
    (_hx : x.Valid) (_hy : y.Valid) (h : x.Equiv y) :
    (ofRealCompute x).Equiv (ofRealCompute y) := by
  intro n
  have hstage := (RealCompute.compareAt_overlap_iff x y n n).1 (h n)
  exact (compareAt_overlap_iff (ofRealCompute x) (ofRealCompute y)
    n n).2
    ⟨⟨hstage.1, by simp [ofRealCompute]⟩,
      ⟨hstage.2, by simp [ofRealCompute]⟩⟩
theorem coe_realCompute_equiv_of_equiv {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) (h : x.Equiv y) :
    (x : ComplexCompute).Equiv (y : ComplexCompute) :=
  ofRealCompute_equiv_of_equiv hx hy h

end ComplexCompute

/-- A raw representation of a partial complex-valued function on rational
complex inputs.  The domain belongs to the representation, so branch choices
and local charts can carry their natural domains. -/
structure FunctionRaw where
  domain : QComplex -> Prop
  compute : (z : QComplex) -> domain z -> Nat -> QBox
  rate :
    (z : QComplex) -> (hz : domain z) ->
      ComplexCompute.Rate (compute z hz) := fun _ _ => .unknown

namespace FunctionRaw

/-!
Function representations do not need their own global rate layer.  The function
layer keeps domain and representation data; the numeric output layer is still a
`RealCompute` or `ComplexCompute`, whose optional `rate` field carries any shrinking
rate metadata.
-/

def entire : QComplex -> Prop := fun _ => True

def evalRaw (f : FunctionRaw) (z : QComplex) (hz : f.domain z) : ComplexCompute where
  compute := f.compute z hz
  rate := f.rate z hz

def Valid (f : FunctionRaw) : Prop :=
  forall z (hz : f.domain z), (f.evalRaw z hz).Valid

/-- Restrict a complex-valued raw function to the real axis and keep the real
coordinate. -/
def realPartOnRealAxis (f : FunctionRaw) : PartialRealFunRaw where
  definedAt := fun x => f.domain (QComplex.ofRat x)
  compute := fun x hx n =>
    let B := f.compute (QComplex.ofRat x) hx n
    { lo := B.lo.re, hi := B.hi.re }

/-- Two raw function representations agree on their common domain when their
computed complex numbers are equivalent at every rational complex point where
both representations are defined.

This is intentionally not made into a global equivalence relation: for
arbitrary domains, agreement-on-overlap is not transitive without extra
domain/extension hypotheses. -/
def AgreeOnCommonDomain (f g : FunctionRaw) : Prop :=
  forall z (hf : f.domain z) (hg : g.domain z), (f.evalRaw z hf).Equiv (g.evalRaw z hg)

theorem agreeOnCommonDomain_symm {f g : FunctionRaw} :
    f.AgreeOnCommonDomain g -> g.AgreeOnCommonDomain f := by
  intro h z hg hf
  exact ComplexCompute.equiv_symm (h z hf hg)

/-- Short alias for `AgreeOnCommonDomain`. -/
def Compatible (f g : FunctionRaw) : Prop := AgreeOnCommonDomain f g

end FunctionRaw

/- The abstract complex-function layer.  A named special function is a
   certified handle whose representations may have different complex domains.
   Agreement is required only on the intersection of those domains. -/
structure ComplexFunctionImplementation (preferred : FunctionRaw) where
  raw : FunctionRaw
  valid : raw.Valid
  agrees : preferred.AgreeOnCommonDomain raw

structure ComplexFunction where
  preferred : FunctionRaw
  valid : preferred.Valid
  implementations : List
    (ComplexFunctionImplementation preferred) := []

namespace ComplexFunction

structure Representation (f : ComplexFunction) where
  raw : FunctionRaw
  valid : raw.Valid
  agrees : raw.AgreeOnCommonDomain f.preferred

def ofRaw (raw : FunctionRaw) (h : raw.Valid) : ComplexFunction where
  preferred := raw
  valid := h
  implementations := []

def representations (f : ComplexFunction) : List FunctionRaw :=
  f.preferred :: f.implementations.map ComplexFunctionImplementation.raw

theorem implementation_agrees_preferred {f : ComplexFunction}
    (impl : ComplexFunctionImplementation f.preferred) :
    impl.raw.AgreeOnCommonDomain f.preferred :=
  FunctionRaw.agreeOnCommonDomain_symm impl.agrees

def preferredRepresentation (f : ComplexFunction) : Representation f where
  raw := f.preferred
  valid := f.valid
  agrees := by
    intro z hz hz'
    exact ComplexCompute.equiv_refl (f.preferred.evalRaw z hz) (f.valid z hz)

def implementationRepresentation {f : ComplexFunction}
    (impl : ComplexFunctionImplementation f.preferred) : Representation f where
  raw := impl.raw
  valid := impl.valid
  agrees := implementation_agrees_preferred impl

def withAlternative (f : ComplexFunction) (raw : FunctionRaw)
    (hvalid : raw.Valid)
    (h : f.preferred.AgreeOnCommonDomain raw) : ComplexFunction where
  preferred := f.preferred
  valid := f.valid
  implementations :=
    { raw := raw, valid := hvalid, agrees := h } :: f.implementations

/- Add a function implementation through an existing representation.  The
   explicit coverage hypothesis is essential: agreement on varying partial
   domains cannot be composed unless the intermediate representation is
   defined at the new/preferred common inputs. -/
def withAlternativeFrom (f : ComplexFunction) (parent : Representation f)
    (raw : FunctionRaw) (hvalid : raw.Valid)
    (hcover : forall z, raw.domain z -> f.preferred.domain z -> parent.raw.domain z)
    (h : forall z (hr : raw.domain z) (hf : f.preferred.domain z)
      (hp : parent.raw.domain z),
      (raw.evalRaw z hr).Equiv (parent.raw.evalRaw z hp)) : ComplexFunction where
  preferred := f.preferred
  valid := f.valid
  implementations :=
    { raw := raw
      valid := hvalid
      agrees := by
        intro z hf hr
        let hp := hcover z hr hf
        exact ComplexCompute.equiv_trans (f.valid z hf) (parent.valid z hp)
          (hvalid z hr)
          (ComplexCompute.equiv_symm (parent.agrees z hp hf))
          (ComplexCompute.equiv_symm (h z hr hf hp)) } :: f.implementations

def withAlternativeFromImplementation (f : ComplexFunction)
    (parent : ComplexFunctionImplementation f.preferred)
    (raw : FunctionRaw) (hvalid : raw.Valid)
    (hcover : forall z, raw.domain z -> f.preferred.domain z -> parent.raw.domain z)
    (h : forall z (hr : raw.domain z) (hf : f.preferred.domain z)
      (hp : parent.raw.domain z),
      (raw.evalRaw z hr).Equiv (parent.raw.evalRaw z hp)) : ComplexFunction where
  preferred := f.preferred
  valid := f.valid
  implementations :=
    { raw := raw
      valid := hvalid
      agrees := by
        intro z hf hr
        let hp := hcover z hr hf
        exact ComplexCompute.equiv_trans (f.valid z hf) (parent.valid z hp)
          (hvalid z hr)
          (parent.agrees z hf hp) (ComplexCompute.equiv_symm (h z hr hf hp)) } ::
      f.implementations

end ComplexFunction

structure ComplexCert where
  raw : ComplexCompute
  valid : raw.Valid

end ComputableAnalysis

namespace ComputableAnalysis

def minRat (a b : Rat) : Rat := if a <= b then a else b
def maxRat2 (a b : Rat) : Rat := if a <= b then b else a

def min4 (a b c d : Rat) : Rat := minRat (minRat a b) (minRat c d)
def max4 (a b c d : Rat) : Rat := maxRat2 (maxRat2 a b) (maxRat2 c d)

namespace QBox

def point (z : QComplex) : QBox := { lo := z, hi := z }

def zero : QBox := point QComplex.zero

def ofRealInterval (I : QInterval) : QBox :=
  { lo := { re := I.lo, im := 0 }, hi := { re := I.hi, im := 0 } }

def add (A B : QBox) : QBox :=
  { lo := QComplex.add A.lo B.lo, hi := QComplex.add A.hi B.hi }

def neg (A : QBox) : QBox :=
  { lo := { re := -A.hi.re, im := -A.hi.im },
    hi := { re := -A.lo.re, im := -A.lo.im } }

def sub (A B : QBox) : QBox := add A (neg B)

def mulRealInterval (a b c d : Rat) : QInterval :=
  let p1 := a * c
  let p2 := a * d
  let p3 := b * c
  let p4 := b * d
  { lo := min4 p1 p2 p3 p4, hi := max4 p1 p2 p3 p4 }

theorem mulRealInterval_self_of_nonneg {a b : Rat}
    (ha0 : 0 <= a) (hab : a <= b) :
    mulRealInterval a b a b = { lo := a * a, hi := b * b } := by
  have hb0 : 0 <= b := by grind
  have h12 : a * a <= a * b := Rat.mul_le_mul_of_nonneg_left hab ha0
  have h13 : a * a <= b * a := by
    simpa [Rat.mul_comm] using Rat.mul_le_mul_of_nonneg_left hab ha0
  have h34 : b * a <= b * b := by
    simpa [Rat.mul_comm] using Rat.mul_le_mul_of_nonneg_left hab hb0
  have h24 : a * b <= b * b := Rat.mul_le_mul_of_nonneg_right hab hb0
  unfold mulRealInterval min4 max4 minRat maxRat2
  simp [h12, h13, h34, h24]

/-- On two nonnegative rational intervals, interval multiplication has the
expected endpoint form.  This is the finite order fact behind the first
certified product construction for nonnegative bounded raw reals. -/
theorem mulRealInterval_of_nonneg {a b c d : Rat}
    (ha0 : 0 <= a) (hab : a <= b)
    (hc0 : 0 <= c) (hcd : c <= d) :
    mulRealInterval a b c d = { lo := a * c, hi := b * d } := by
  have hb0 : 0 <= b := by grind
  have hd0 : 0 <= d := by grind
  have h12 : a * c <= a * d :=
    Rat.mul_le_mul_of_nonneg_left hcd ha0
  have h13 : a * c <= b * c :=
    Rat.mul_le_mul_of_nonneg_right hab hc0
  have h24 : a * d <= b * d :=
    Rat.mul_le_mul_of_nonneg_right hab hd0
  have h34 : b * c <= b * d :=
    Rat.mul_le_mul_of_nonneg_left hcd hb0
  unfold mulRealInterval min4 max4 minRat maxRat2
  simp [h12, h13, h24, h34]

def mul (A B : QBox) : QBox :=
  let rr := mulRealInterval A.lo.re A.hi.re B.lo.re B.hi.re
  let ii := mulRealInterval A.lo.im A.hi.im B.lo.im B.hi.im
  let ri := mulRealInterval A.lo.re A.hi.re B.lo.im B.hi.im
  let ir := mulRealInterval A.lo.im A.hi.im B.lo.re B.hi.re
  { lo := { re := rr.lo - ii.hi, im := ri.lo + ir.lo },
    hi := { re := rr.hi - ii.lo, im := ri.hi + ir.hi } }

def scaleRat (r : Rat) (A : QBox) : QBox :=
  if 0 <= r then
    { lo := { re := r * A.lo.re, im := r * A.lo.im },
      hi := { re := r * A.hi.re, im := r * A.hi.im } }
  else
    { lo := { re := r * A.hi.re, im := r * A.hi.im },
      hi := { re := r * A.lo.re, im := r * A.lo.im } }

/-- The coordinatewise common part of two rational complex boxes.  As with
real intervals, callers establish a common enclosed box before treating this
as ordered. -/
def intersection (A B : QBox) : QBox :=
  { lo := { re := maxRat2 A.lo.re B.lo.re, im := maxRat2 A.lo.im B.lo.im },
    hi := { re := minRat A.hi.re B.hi.re, im := minRat A.hi.im B.hi.im } }

/-- Widen both real and imaginary coordinates of a complex box by the same
rational radius.  This is the finite operation used to stabilize a Cauchy
family of direct complex computations. -/
def expand (A : QBox) (radius : Rat) : QBox :=
  { lo := { re := A.lo.re - radius, im := A.lo.im - radius },
    hi := { re := A.hi.re + radius, im := A.hi.im + radius } }

/-- Enlarging a box by a larger rational radius can only enlarge it. -/
theorem expand_mono_radius (A : QBox) {r s : Rat} (hrs : r <= s) :
    (expand A r).NestedIn (expand A s) := by
  unfold NestedIn expand
  simp only [QComplex.le_def]
  grind [Rat.sub_eq_add_neg]

theorem intersection_contains {A B C : QBox}
    (hA : C.NestedIn A) (hB : C.NestedIn B) :
    C.NestedIn (intersection A B) := by
  unfold NestedIn intersection at *
  simp only [QComplex.le_def] at *
  grind [minRat, maxRat2]

theorem intersection_contained_left (A B : QBox) :
    (intersection A B).NestedIn A := by
  unfold NestedIn intersection
  simp only [QComplex.le_def]
  grind [minRat, maxRat2]

theorem intersection_contained_right (A B : QBox) :
    (intersection A B).NestedIn B := by
  unfold NestedIn intersection
  simp only [QComplex.le_def]
  grind [minRat, maxRat2]

theorem nested_trans {A B C : QBox}
    (hAB : A.NestedIn B) (hBC : B.NestedIn C) :
    A.NestedIn C := by
  exact ⟨QComplex.le_trans hBC.1 hAB.1, QComplex.le_trans hAB.2 hBC.2⟩

theorem ordered_of_nested {inner outer : QBox}
    (hinner : inner.Ordered) (h : inner.NestedIn outer) : outer.Ordered := by
  exact QComplex.le_trans h.1 (QComplex.le_trans hinner h.2)

theorem width_height_le_of_nested {outer inner : QBox}
    (h : inner.NestedIn outer) :
    inner.width <= outer.width /\ inner.height <= outer.height := by
  unfold NestedIn at h
  simp only [QComplex.le_def] at h
  unfold width height
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem expand_width (A : QBox) (radius : Rat) :
    (expand A radius).width = A.width + 2 * radius := by
  unfold expand width
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem expand_height (A : QBox) (radius : Rat) :
    (expand A radius).height = A.height + 2 * radius := by
  unfold expand height
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

end QBox

end ComputableAnalysis

namespace ComputableAnalysis

namespace RealCompute

def zero : RealCompute := ofRat 0
def one : RealCompute := ofRat 1

def addCompute (x y : RealCompute) : Nat -> QInterval :=
  fun n =>
    let X := x.compute n
    let Y := y.compute n
    { lo := X.lo + Y.lo, hi := X.hi + Y.hi }

def negCompute (x : RealCompute) : Nat -> QInterval :=
  fun n =>
    let X := x.compute n
    { lo := -X.hi, hi := -X.lo }

def subCompute (x y : RealCompute) : Nat -> QInterval :=
  fun n =>
    let X := x.compute n
    let Y := y.compute n
    { lo := X.lo - Y.hi, hi := X.hi - Y.lo }

def scaleRatCompute (r : Rat) (x : RealCompute) : Nat -> QInterval :=
  fun n =>
    let X := x.compute n
    if 0 <= r then
      { lo := r * X.lo, hi := r * X.hi }
    else
      { lo := r * X.hi, hi := r * X.lo }

def mulCompute (x y : RealCompute) : Nat -> QInterval :=
  fun n =>
    let X := x.compute n
    let Y := y.compute n
    QBox.mulRealInterval X.lo X.hi Y.lo Y.hi

def add (x y : RealCompute) : RealCompute where
  compute := addCompute x y

def neg (x : RealCompute) : RealCompute where
  compute := negCompute x

def sub (x y : RealCompute) : RealCompute where
  compute := subCompute x y

def scaleRat (r : Rat) (x : RealCompute) : RealCompute where
  compute := scaleRatCompute r x

def mul (x y : RealCompute) : RealCompute where
  compute := mulCompute x y

theorem le_neg_le_neg {x y : RealCompute} (hxy : x.Le y) :
    (RealCompute.neg y).Le (RealCompute.neg x) := by
  intro n m
  change -(y.compute n).hi <= -(x.compute m).lo
  exact Rat.neg_le_neg (hxy m n)

theorem le_sub_le_sub {x y z w : RealCompute}
    (hxy : x.Le y) (hzw : z.Le w) :
    (RealCompute.sub x w).Le (RealCompute.sub y z) := by
  intro n m
  change (x.compute n).lo - (w.compute n).hi <=
    (y.compute m).hi - (z.compute m).lo
  calc
    (x.compute n).lo - (w.compute n).hi <=
        (y.compute m).hi - (w.compute n).hi := by
      simpa [Rat.sub_eq_add_neg] using
        (Rat.add_le_add_right).2 (hxy n m)
    _ <= (y.compute m).hi - (z.compute m).lo := by
      simpa [Rat.sub_eq_add_neg] using
        (Rat.add_le_add_left).2 (Rat.neg_le_neg (hzw m n))

theorem le_add_le_add {x y z w : RealCompute}
    (hxy : x.Le y) (hzw : z.Le w) :
    (RealCompute.add x z).Le (RealCompute.add y w) := by
  intro n m
  change (x.compute n).lo + (z.compute n).lo <=
    (y.compute m).hi + (w.compute m).hi
  calc
    (x.compute n).lo + (z.compute n).lo <=
        (y.compute m).hi + (z.compute n).lo :=
      (Rat.add_le_add_right).2 (hxy n m)
    _ <= (y.compute m).hi + (w.compute m).hi :=
      (Rat.add_le_add_left).2 (hzw n m)

theorem le_scaleRat_le_scaleRat {x y : RealCompute} {r : Rat}
    (hr : 0 <= r) (hxy : x.Le y) :
    (RealCompute.scaleRat r x).Le (RealCompute.scaleRat r y) := by
  intro n m
  dsimp [RealCompute.scaleRat, scaleRatCompute]
  rw [if_pos hr]
  rw [if_pos hr]
  exact Rat.mul_le_mul_of_nonneg_left (hxy n m) hr

theorem le_scaleRat_le_scaleRat_of_nonpos {x y : RealCompute} {r : Rat}
    (hr : r <= 0) (hxy : x.Le y) :
    (RealCompute.scaleRat r y).Le (RealCompute.scaleRat r x) := by
  intro n m
  by_cases hr0 : 0 <= r
  · have hrzero : r = 0 := Rat.le_antisymm hr hr0
    simp [RealCompute.scaleRat, scaleRatCompute, hr0, hrzero]
  · dsimp [RealCompute.scaleRat, scaleRatCompute]
    rw [if_neg hr0]
    rw [if_neg hr0]
    have hrneg : 0 <= -r := by grind [Rat.sub_eq_add_neg]
    have hmul := Rat.mul_le_mul_of_nonneg_left (hxy m n) hrneg
    grind [Rat.neg_mul, Rat.mul_neg]

def scaleRatNonneg (r : Rat) (_hr : 0 <= r) (x : RealCompute) : RealCompute where
  compute := fun n =>
    let X := x.compute n
    { lo := r * X.lo, hi := r * X.hi }

instance : HAdd RealCompute RealCompute RealCompute where
  hAdd := add

instance : Neg RealCompute where
  neg := neg

instance : HSub RealCompute RealCompute RealCompute where
  hSub := sub

instance : HMul RealCompute RealCompute RealCompute where
  hMul := mul

instance : HMul Rat RealCompute RealCompute where
  hMul := scaleRat

instance : HMul Nat RealCompute RealCompute where
  hMul n x := scaleRat (n : Rat) x

instance : HMul Int RealCompute RealCompute where
  hMul n x := scaleRat (n : Rat) x

def AddCertifies (x y : RealCompute) : Prop :=
  RealCompute.ValidCompute (addCompute x y)

def NegCertifies (x : RealCompute) : Prop :=
  RealCompute.ValidCompute (negCompute x)

def ScaleRatCertifies (r : Rat) (x : RealCompute) : Prop :=
  RealCompute.ValidCompute (scaleRatCompute r x)

private theorem half_pos {q : Rat} (hq : 0 < q) : 0 < q / 2 := by
  rw [Rat.div_def]
  exact Rat.mul_pos hq ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2))

private theorem add_halves (q : Rat) : q / 2 + q / 2 = q := by
  rw [Rat.div_def]
  have hne : (2 : Rat) != 0 := by decide +kernel
  grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm, Rat.mul_assoc,
    Rat.mul_comm, Rat.mul_inv_cancel]

private theorem valid_width_order
    {compute : Nat -> QInterval}
    (h : RealCompute.ValidCompute compute) (n : Nat) :
    (compute n).lo <= (compute n).hi := by
  have hn := h.2.1 n n (Nat.le_refl n)
  exact hn.2.1

theorem addCompute_valid {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) :
    RealCompute.ValidCompute (addCompute x y) := by
  constructor
  · intro n
    have hxord := valid_width_order hx n
    have hyord := valid_width_order hy n
    unfold addCompute QInterval.width
    grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      have hxnm := hx.2.1 n m hnm
      have hynm := hy.2.1 n m hnm
      unfold addCompute
      constructor
      · grind
      · constructor
        · grind
        · grind
    · intro eps
      let eps2 : QPos := ⟨eps.val / 2, half_pos eps.property⟩
      obtain ⟨Nx, hNx⟩ := hx.2.2 eps2
      obtain ⟨Ny, hNy⟩ := hy.2.2 eps2
      refine ⟨Nat.max Nx Ny, ?_⟩
      intro n hn
      have hnx : Nx <= n := Nat.le_trans (Nat.le_max_left Nx Ny) hn
      have hny : Ny <= n := Nat.le_trans (Nat.le_max_right Nx Ny) hn
      have hxeps := hNx n hnx
      have hyeps := hNy n hny
      unfold addCompute QInterval.width
      change
        (x.compute n).hi + (y.compute n).hi -
          ((x.compute n).lo + (y.compute n).lo) <= eps.val
      calc
        (x.compute n).hi + (y.compute n).hi -
            ((x.compute n).lo + (y.compute n).lo)
            <= eps2.val + eps2.val := by
          have hxeps' :
              (x.compute n).hi - (x.compute n).lo <= eps2.val := by
            simpa [QInterval.width] using hxeps
          have hyeps' :
              (y.compute n).hi - (y.compute n).lo <= eps2.val := by
            simpa [QInterval.width] using hyeps
          grind [Rat.sub_eq_add_neg]
        _ = eps.val := add_halves eps.val

theorem negCompute_valid {x : RealCompute}
    (hx : x.Valid) : RealCompute.ValidCompute (negCompute x) := by
  constructor
  · intro n
    have hxord := valid_width_order hx n
    unfold negCompute QInterval.width
    change 0 <= -(x.compute n).lo - -(x.compute n).hi
    grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      have hxnm := hx.2.1 n m hnm
      unfold negCompute
      constructor
      · exact Rat.neg_le_neg hxnm.2.2
      · constructor
        · exact Rat.neg_le_neg hxnm.2.1
        · exact Rat.neg_le_neg hxnm.1
    · intro eps
      obtain ⟨N, hN⟩ := hx.2.2 eps
      refine ⟨N, ?_⟩
      intro n hn
      have hxeps := hN n hn
      unfold negCompute QInterval.width
      change -(x.compute n).lo - -(x.compute n).hi <= eps.val
      have hxeps' :
          (x.compute n).hi - (x.compute n).lo <= eps.val := by
        simpa [QInterval.width] using hxeps
      grind [Rat.sub_eq_add_neg]

theorem subCompute_valid {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) :
    RealCompute.ValidCompute (subCompute x y) := by
  constructor
  · intro n
    have hxord := valid_width_order hx n
    have hyord := valid_width_order hy n
    unfold subCompute QInterval.width
    change 0 <=
      ((x.compute n).hi - (y.compute n).lo) -
        ((x.compute n).lo - (y.compute n).hi)
    grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      have hxnm := hx.2.1 n m hnm
      have hynm := hy.2.1 n m hnm
      unfold subCompute
      constructor
      · grind [Rat.sub_eq_add_neg]
      · constructor
        · grind [Rat.sub_eq_add_neg]
        · grind [Rat.sub_eq_add_neg]
    · intro eps
      let eps2 : QPos := ⟨eps.val / 2, half_pos eps.property⟩
      obtain ⟨Nx, hNx⟩ := hx.2.2 eps2
      obtain ⟨Ny, hNy⟩ := hy.2.2 eps2
      refine ⟨Nat.max Nx Ny, ?_⟩
      intro n hn
      have hnx : Nx <= n := Nat.le_trans (Nat.le_max_left Nx Ny) hn
      have hny : Ny <= n := Nat.le_trans (Nat.le_max_right Nx Ny) hn
      have hxeps := hNx n hnx
      have hyeps := hNy n hny
      unfold subCompute QInterval.width
      change
        ((x.compute n).hi - (y.compute n).lo) -
          ((x.compute n).lo - (y.compute n).hi) <= eps.val
      calc
        ((x.compute n).hi - (y.compute n).lo) -
            ((x.compute n).lo - (y.compute n).hi)
            <= eps2.val + eps2.val := by
          have hxeps' :
              (x.compute n).hi - (x.compute n).lo <= eps2.val := by
            simpa [QInterval.width] using hxeps
          have hyeps' :
              (y.compute n).hi - (y.compute n).lo <= eps2.val := by
            simpa [QInterval.width] using hyeps
          grind [Rat.sub_eq_add_neg]
        _ = eps.val := add_halves eps.val

private theorem mul_width_shrink
    {compute : Nat -> QInterval} (h : RealCompute.ValidCompute compute)
    {r : Rat} (hr : 0 <= r) :
    RealCompute.WidthsShrinkToZero
      (fun n => { lo := r * (compute n).lo,
                  hi := r * (compute n).hi }) := by
  by_cases hr0 : r = 0
  · intro eps
    refine ⟨0, ?_⟩
    intro n _hn
    unfold QInterval.width
    simp [hr0]
    grind [Rat.sub_eq_add_neg, Rat.le_of_lt eps.property]
  · have hrpos : 0 < r := by grind
    intro eps
    let scaled : QPos :=
      ⟨eps.val / r, by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property ((Rat.inv_pos).2 hrpos)⟩
    obtain ⟨N, hN⟩ := h.2.2 scaled
    refine ⟨N, ?_⟩
    intro n hn
    have hw := hN n hn
    unfold QInterval.width
    have hw' : (compute n).hi - (compute n).lo <= scaled.val := by
      simpa [QInterval.width] using hw
    calc
      r * (compute n).hi - r * (compute n).lo =
          r * (compute n).width := by
            unfold QInterval.width
            grind [Rat.sub_eq_add_neg, Rat.mul_add]
      _ <= r * scaled.val := by
            exact Rat.mul_le_mul_of_nonneg_left hw' hr
      _ = eps.val := by
            dsimp [scaled]
            rw [Rat.div_def]
            have hrne : r ≠ 0 := Rat.ne_of_gt hrpos
            grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem scaleRatCompute_valid_of_nonneg {r : Rat} {x : RealCompute}
    (hr : 0 <= r) (hx : x.Valid) :
    RealCompute.ValidCompute (scaleRatCompute r x) := by
  constructor
  · intro n
    have hxord := valid_width_order hx n
    unfold scaleRatCompute QInterval.width
    simp [hr]
    change 0 <= r * (x.compute n).hi - r * (x.compute n).lo
    have hmul :
        r * (x.compute n).lo <= r * (x.compute n).hi :=
      Rat.mul_le_mul_of_nonneg_left hxord hr
    grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      have hxnm := hx.2.1 n m hnm
      unfold scaleRatCompute
      simp [hr]
      constructor
      · exact Rat.mul_le_mul_of_nonneg_left hxnm.1 hr
      · constructor
        · exact Rat.mul_le_mul_of_nonneg_left hxnm.2.1 hr
        · exact Rat.mul_le_mul_of_nonneg_left hxnm.2.2 hr
    · intro eps
      obtain ⟨N, hN⟩ := mul_width_shrink hx hr eps
      refine ⟨N, ?_⟩
      intro n hn
      have hwidth := hN n hn
      unfold scaleRatCompute QInterval.width
      simp [hr]
      simpa [QInterval.width] using hwidth

theorem add_valid {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) : (x + y).Valid :=
  addCompute_valid hx hy

theorem neg_valid {x : RealCompute} (hx : x.Valid) : (-x).Valid :=
  negCompute_valid hx

theorem sub_valid {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) : (x - y).Valid :=
  subCompute_valid hx hy

theorem scaleRat_valid_of_nonneg {r : Rat} {x : RealCompute}
    (hr : 0 <= r) (hx : x.Valid) : (scaleRat r x).Valid :=
  scaleRatCompute_valid_of_nonneg hr hx

private theorem scaleRatCompute_neg_eq_scaleRatCompute_neg
    {r : Rat} (hr : ¬ 0 <= r) (x : RealCompute) :
    scaleRatCompute r x = scaleRatCompute (-r) (RealCompute.neg x) := by
  funext n
  have hneg : 0 <= -r := by grind
  simp [scaleRatCompute, RealCompute.neg, negCompute, hr, hneg]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem scaleRatCompute_valid {r : Rat} {x : RealCompute}
    (hx : x.Valid) :
    RealCompute.ValidCompute (scaleRatCompute r x) := by
  by_cases hr : 0 <= r
  · exact scaleRatCompute_valid_of_nonneg hr hx
  · have hneg : 0 <= -r := by grind
    have hvalid :=
      scaleRatCompute_valid_of_nonneg (r := -r) (x := RealCompute.neg x) hneg
        (neg_valid hx)
    rwa [scaleRatCompute_neg_eq_scaleRatCompute_neg hr x]

theorem scaleRat_valid {r : Rat} {x : RealCompute}
    (hx : x.Valid) : (scaleRat r x).Valid :=
  scaleRatCompute_valid hx

private theorem square_mono_nonneg {a b : Rat}
    (ha0 : 0 <= a) (hab : a <= b) : a * a <= b * b := by
  have hb0 : 0 <= b := by grind
  have h1 : a * a <= a * b := Rat.mul_le_mul_of_nonneg_left hab ha0
  have h2 : a * b <= b * b := Rat.mul_le_mul_of_nonneg_right hab hb0
  exact Rat.le_trans h1 h2

theorem mulSelf_valid_of_nonneg_bounded {x : RealCompute}
    (hx : x.Valid) {B : Rat} (hB : 0 < B)
    (hbounds : forall n, 0 <= (x.compute n).lo ∧ (x.compute n).hi <= B) :
    (x * x).Valid := by
  constructor
  · intro n
    have horder := RealCompute.interval_order_of_valid x hx n
    have hnonneg := (hbounds n).1
    have hcompute : ((x * x).compute n) =
        { lo := (x.compute n).lo * (x.compute n).lo,
          hi := (x.compute n).hi * (x.compute n).hi } := by
      change QBox.mulRealInterval
          (x.compute n).lo (x.compute n).hi
          (x.compute n).lo (x.compute n).hi = _
      exact QBox.mulRealInterval_self_of_nonneg hnonneg horder
    rw [hcompute]
    unfold QInterval.width
    have hsquare :
        (x.compute n).lo * (x.compute n).lo <=
          (x.compute n).hi * (x.compute n).hi :=
      square_mono_nonneg hnonneg horder
    grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      have horderN := RealCompute.interval_order_of_valid x hx n
      have horderM := RealCompute.interval_order_of_valid x hx m
      have hnonnegN := (hbounds n).1
      have hnonnegM := (hbounds m).1
      have hnested := hx.2.1 n m hnm
      have hcomputeN : ((x * x).compute n) =
          { lo := (x.compute n).lo * (x.compute n).lo,
            hi := (x.compute n).hi * (x.compute n).hi } := by
        change QBox.mulRealInterval
            (x.compute n).lo (x.compute n).hi
            (x.compute n).lo (x.compute n).hi = _
        exact QBox.mulRealInterval_self_of_nonneg hnonnegN horderN
      have hcomputeM : ((x * x).compute m) =
          { lo := (x.compute m).lo * (x.compute m).lo,
            hi := (x.compute m).hi * (x.compute m).hi } := by
        change QBox.mulRealInterval
            (x.compute m).lo (x.compute m).hi
            (x.compute m).lo (x.compute m).hi = _
        exact QBox.mulRealInterval_self_of_nonneg hnonnegM horderM
      rw [hcomputeN, hcomputeM]
      constructor
      · exact square_mono_nonneg hnonnegN hnested.1
      · constructor
        · exact square_mono_nonneg hnonnegM horderM
        · exact square_mono_nonneg (by grind) hnested.2.2
    · intro eps
      have hdenPos : 0 < (2 : Rat) * B := by
        exact Rat.mul_pos (by decide +kernel : (0 : Rat) < 2) hB
      let scaled : QPos :=
        ⟨eps.val / ((2 : Rat) * B), by
          rw [Rat.div_def]
          exact Rat.mul_pos eps.property ((Rat.inv_pos).2 hdenPos)⟩
      obtain ⟨N, hN⟩ := hx.2.2 scaled
      refine ⟨N, ?_⟩
      intro n hn
      have horder := RealCompute.interval_order_of_valid x hx n
      have hnonneg := (hbounds n).1
      have hcompute : ((x * x).compute n) =
          { lo := (x.compute n).lo * (x.compute n).lo,
            hi := (x.compute n).hi * (x.compute n).hi } := by
        change QBox.mulRealInterval
            (x.compute n).lo (x.compute n).hi
            (x.compute n).lo (x.compute n).hi = _
        exact QBox.mulRealInterval_self_of_nonneg hnonneg horder
      have hw := hN n hn
      rw [hcompute]
      unfold QInterval.width
      have hw' : (x.compute n).hi - (x.compute n).lo <= scaled.val := by
        simpa [QInterval.width] using hw
      have hsumBound :
          (x.compute n).hi + (x.compute n).lo <= (2 : Rat) * B := by
        have hhiB := (hbounds n).2
        grind
      have hgapNonneg : 0 <= (x.compute n).hi - (x.compute n).lo := by
        grind [Rat.sub_eq_add_neg]
      calc
        (x.compute n).hi * (x.compute n).hi -
            (x.compute n).lo * (x.compute n).lo
            = ((x.compute n).hi - (x.compute n).lo) *
                ((x.compute n).hi + (x.compute n).lo) := by
              grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
                Rat.mul_assoc, Rat.mul_comm]
        _ <= ((x.compute n).hi - (x.compute n).lo) * ((2 : Rat) * B) := by
              exact Rat.mul_le_mul_of_nonneg_left hsumBound hgapNonneg
        _ <= scaled.val * ((2 : Rat) * B) := by
              exact Rat.mul_le_mul_of_nonneg_right hw' (Rat.le_of_lt hdenPos)
        _ = eps.val := by
              dsimp [scaled]
              rw [Rat.div_def]
              have hne : (2 : Rat) * B ≠ 0 := Rat.ne_of_gt hdenPos
              grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- The interval computation for a product of nonnegative raw reals has the
ordinary lower--lower and upper--upper endpoint form. -/
private theorem mul_compute_of_nonneg
    {x y : RealCompute} (hx : x.Valid) (hy : y.Valid)
    (hxnonneg : forall n, 0 <= (x.compute n).lo)
    (hynonneg : forall n, 0 <= (y.compute n).lo)
    (n : Nat) :
    ((x * y).compute n) =
      { lo := (x.compute n).lo * (y.compute n).lo,
        hi := (x.compute n).hi * (y.compute n).hi } := by
  change QBox.mulRealInterval
      (x.compute n).lo (x.compute n).hi
      (y.compute n).lo (y.compute n).hi = _
  exact QBox.mulRealInterval_of_nonneg
    (hxnonneg n) (RealCompute.interval_order_of_valid x hx n)
    (hynonneg n) (RealCompute.interval_order_of_valid y hy n)

/-- Products of nonnegative, rationally bounded computable reals are valid.

The proof is entirely interval based.  Its width estimate is
`B_x * width(y) + B_y * width(x)`, so it supplies the product operation needed
for local positive-domain calculus without a completed-real multiplication
principle. -/
theorem mul_valid_of_nonneg_bounded {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid)
    {Bx By : Rat} (hBx : 0 < Bx) (hBy : 0 < By)
    (hxbounds : forall n,
      0 <= (x.compute n).lo /\ (x.compute n).hi <= Bx)
    (hybounds : forall n,
      0 <= (y.compute n).lo /\ (y.compute n).hi <= By) :
    (x * y).Valid := by
  have hxnonneg : forall n, 0 <= (x.compute n).lo := fun n =>
    (hxbounds n).1
  have hynonneg : forall n, 0 <= (y.compute n).lo := fun n =>
    (hybounds n).1
  constructor
  · intro n
    have horderx := RealCompute.interval_order_of_valid x hx n
    have hordery := RealCompute.interval_order_of_valid y hy n
    have hcompute := mul_compute_of_nonneg hx hy hxnonneg hynonneg n
    rw [hcompute]
    unfold QInterval.width
    have hxhi0 : 0 <= (x.compute n).hi := by grind
    have hleft :
        (x.compute n).lo * (y.compute n).lo <=
          (x.compute n).hi * (y.compute n).lo :=
      Rat.mul_le_mul_of_nonneg_right horderx (hynonneg n)
    have hright :
        (x.compute n).hi * (y.compute n).lo <=
          (x.compute n).hi * (y.compute n).hi :=
      Rat.mul_le_mul_of_nonneg_left hordery hxhi0
    grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      have hxnm := hx.2.1 n m hnm
      have hynm := hy.2.1 n m hnm
      have hcomputeN := mul_compute_of_nonneg hx hy hxnonneg hynonneg n
      have hcomputeM := mul_compute_of_nonneg hx hy hxnonneg hynonneg m
      rw [hcomputeN, hcomputeM]
      have hxloM0 : 0 <= (x.compute m).lo := hxnonneg m
      have hyloN0 : 0 <= (y.compute n).lo := hynonneg n
      have hyhiM0 : 0 <= (y.compute m).hi := by
        have hordery := RealCompute.interval_order_of_valid y hy m
        grind
      have hlow :
          (x.compute n).lo * (y.compute n).lo <=
            (x.compute m).lo * (y.compute m).lo := by
        calc
          (x.compute n).lo * (y.compute n).lo <=
              (x.compute m).lo * (y.compute n).lo :=
            Rat.mul_le_mul_of_nonneg_right hxnm.1 hyloN0
          _ <= (x.compute m).lo * (y.compute m).lo :=
            Rat.mul_le_mul_of_nonneg_left hynm.1 hxloM0
      have hhigh :
          (x.compute m).hi * (y.compute m).hi <=
            (x.compute n).hi * (y.compute n).hi := by
        calc
          (x.compute m).hi * (y.compute m).hi <=
              (x.compute n).hi * (y.compute m).hi :=
            Rat.mul_le_mul_of_nonneg_right hxnm.2.2 hyhiM0
          _ <= (x.compute n).hi * (y.compute n).hi := by
            have hxhiN0 : 0 <= (x.compute n).hi := by
              have horderx := RealCompute.interval_order_of_valid x hx n
              grind
            exact Rat.mul_le_mul_of_nonneg_left hynm.2.2 hxhiN0
      have horderxM := RealCompute.interval_order_of_valid x hx m
      have horderyM := RealCompute.interval_order_of_valid y hy m
      have hxhiM0 : 0 <= (x.compute m).hi := by grind
      have hmid :
          (x.compute m).lo * (y.compute m).lo <=
            (x.compute m).hi * (y.compute m).hi := by
        calc
          (x.compute m).lo * (y.compute m).lo <=
              (x.compute m).hi * (y.compute m).lo :=
            Rat.mul_le_mul_of_nonneg_right horderxM (hynonneg m)
          _ <= (x.compute m).hi * (y.compute m).hi :=
            Rat.mul_le_mul_of_nonneg_left horderyM hxhiM0
      exact ⟨hlow, hmid, hhigh⟩
    · intro eps
      let B : Rat := Bx + By
      have hB : 0 < B := by
        dsimp [B]
        grind
      have htwoB : 0 < (2 : Rat) * B :=
        Rat.mul_pos (by decide) hB
      let delta : QPos :=
        ⟨eps.val / ((2 : Rat) * B), by
          rw [Rat.div_def]
          exact Rat.mul_pos eps.property ((Rat.inv_pos).2 htwoB)⟩
      obtain ⟨Nx, hNx⟩ := hx.2.2 delta
      obtain ⟨Ny, hNy⟩ := hy.2.2 delta
      refine ⟨Nat.max Nx Ny, ?_⟩
      intro n hn
      have hnx : Nx <= n := Nat.le_trans (Nat.le_max_left Nx Ny) hn
      have hny : Ny <= n := Nat.le_trans (Nat.le_max_right Nx Ny) hn
      have hxwidth := hNx n hnx
      have hywidth := hNy n hny
      have hxgap :
          (x.compute n).hi - (x.compute n).lo <= delta.val := by
        simpa [QInterval.width] using hxwidth
      have hygap :
          (y.compute n).hi - (y.compute n).lo <= delta.val := by
        simpa [QInterval.width] using hywidth
      have horderx := RealCompute.interval_order_of_valid x hx n
      have hordery := RealCompute.interval_order_of_valid y hy n
      have hxgap0 : 0 <= (x.compute n).hi - (x.compute n).lo := by
        grind [Rat.sub_eq_add_neg]
      have hygap0 : 0 <= (y.compute n).hi - (y.compute n).lo := by
        grind [Rat.sub_eq_add_neg]
      have hBxleB : Bx <= B := by
        dsimp [B]
        grind
      have hByleB : By <= B := by
        dsimp [B]
        grind
      have hxhiB : (x.compute n).hi <= B :=
        Rat.le_trans (hxbounds n).2 hBxleB
      have hyloB : (y.compute n).lo <= B := by
        have hylohi : (y.compute n).lo <= (y.compute n).hi := hordery
        exact Rat.le_trans hylohi (Rat.le_trans (hybounds n).2 hByleB)
      have hB0 : 0 <= B := Rat.le_of_lt hB
      have hfirst :
          (x.compute n).hi * ((y.compute n).hi - (y.compute n).lo) <=
            B * delta.val := by
        calc
          (x.compute n).hi * ((y.compute n).hi - (y.compute n).lo) <=
              B * ((y.compute n).hi - (y.compute n).lo) :=
            Rat.mul_le_mul_of_nonneg_right hxhiB hygap0
          _ <= B * delta.val :=
            Rat.mul_le_mul_of_nonneg_left hygap hB0
      have hsecond :
          (y.compute n).lo * ((x.compute n).hi - (x.compute n).lo) <=
            B * delta.val := by
        calc
          (y.compute n).lo * ((x.compute n).hi - (x.compute n).lo) <=
              B * ((x.compute n).hi - (x.compute n).lo) :=
            Rat.mul_le_mul_of_nonneg_right hyloB hxgap0
          _ <= B * delta.val :=
            Rat.mul_le_mul_of_nonneg_left hxgap hB0
      have hcompute := mul_compute_of_nonneg hx hy hxnonneg hynonneg n
      rw [hcompute]
      unfold QInterval.width
      calc
        (x.compute n).hi * (y.compute n).hi -
            (x.compute n).lo * (y.compute n).lo =
          (x.compute n).hi * ((y.compute n).hi - (y.compute n).lo) +
            (y.compute n).lo * ((x.compute n).hi - (x.compute n).lo) := by
              grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
                Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
        _ <= B * delta.val + B * delta.val :=
          rat_add_le_add hfirst hsecond
        _ = eps.val := by
          dsimp [delta]
          rw [Rat.div_def]
          have hne : (2 : Rat) * B ≠ 0 := Rat.ne_of_gt htwoB
          grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem le_mul_le_mul_of_nonneg
    {x y z w : RealCompute}
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid) (hw : w.Valid)
    (hxnonneg : forall n, 0 <= (x.compute n).lo)
    (hynonneg : forall n, 0 <= (y.compute n).lo)
    (hznonneg : forall n, 0 <= (z.compute n).lo)
    (hwnonneg : forall n, 0 <= (w.compute n).lo)
    (hxy : x.Le y) (hzw : z.Le w) :
    (x * z).Le (y * w) := by
  intro n m
  have hprodN := mul_compute_of_nonneg hx hz hxnonneg hznonneg n
  have hprodM := mul_compute_of_nonneg hy hw hynonneg hwnonneg m
  rw [hprodN, hprodM]
  have hyhi : 0 <= (y.compute m).hi := by
    have horder := RealCompute.interval_order_of_valid y hy m
    grind
  calc
    (x.compute n).lo * (z.compute n).lo <=
        (y.compute m).hi * (z.compute n).lo := by
      exact Rat.mul_le_mul_of_nonneg_right (hxy n m) (hznonneg n)
    _ <= (y.compute m).hi * (w.compute m).hi := by
      have hzw' := hzw n m
      have hzw_mul := Rat.mul_le_mul_of_nonneg_left hzw' hyhi
      simpa [Rat.mul_comm] using hzw_mul

/-- Nonnegative interval multiplication respects changes of certified raw
representation.  Bounds are needed for validity, but not for this same-stage
overlap argument. -/
theorem mul_equiv_of_nonneg {x x' y y' : RealCompute}
    (hx : x.Valid) (hx' : x'.Valid) (hy : y.Valid) (hy' : y'.Valid)
    (hxnonneg : forall n, 0 <= (x.compute n).lo)
    (hx'nonneg : forall n, 0 <= (x'.compute n).lo)
    (hynonneg : forall n, 0 <= (y.compute n).lo)
    (hy'nonneg : forall n, 0 <= (y'.compute n).lo)
    (hxx' : x.Equiv x') (hyy' : y.Equiv y') :
    (x * y).Equiv (x' * y') := by
  intro n
  have hxx := (RealCompute.compareAt_overlap_iff x x' n n).1
    (RealCompute.sameStageOverlap_of_equiv hx hx' hxx' n)
  have hyy := (RealCompute.compareAt_overlap_iff y y' n n).1
    (RealCompute.sameStageOverlap_of_equiv hy hy' hyy' n)
  have hcompute := mul_compute_of_nonneg hx hy hxnonneg hynonneg n
  have hcompute' := mul_compute_of_nonneg hx' hy' hx'nonneg hy'nonneg n
  apply (RealCompute.compareAt_overlap_iff (x * y) (x' * y') n n).2
  rw [hcompute, hcompute']
  change QInterval.Overlaps
    { lo := (x.compute n).lo * (y.compute n).lo,
      hi := (x.compute n).hi * (y.compute n).hi }
    { lo := (x'.compute n).lo * (y'.compute n).lo,
      hi := (x'.compute n).hi * (y'.compute n).hi }
  have hx'hi0 : 0 <= (x'.compute n).hi := by
    have horder := RealCompute.interval_order_of_valid x' hx' n
    grind
  have hxhi0 : 0 <= (x.compute n).hi := by
    have horder := RealCompute.interval_order_of_valid x hx n
    grind
  unfold QInterval.Overlaps at hxx hyy ⊢
  constructor
  · calc
      (x.compute n).lo * (y.compute n).lo <=
          (x'.compute n).hi * (y.compute n).lo :=
        Rat.mul_le_mul_of_nonneg_right hxx.1 (hynonneg n)
      _ <= (x'.compute n).hi * (y'.compute n).hi :=
        Rat.mul_le_mul_of_nonneg_left hyy.1 hx'hi0
  · calc
      (x'.compute n).lo * (y'.compute n).lo <=
          (x.compute n).hi * (y'.compute n).lo :=
        Rat.mul_le_mul_of_nonneg_right hxx.2 (hy'nonneg n)
      _ <= (x.compute n).hi * (y.compute n).hi :=
        Rat.mul_le_mul_of_nonneg_left hyy.2 hxhi0

private theorem le_of_mul_le_mul_pos_left {r a b : Rat}
    (hr : 0 < r) (h : r * a <= r * b) : a <= b := by
  apply Rat.le_of_mul_le_mul_right (c := r)
  · simpa [Rat.mul_comm] using h
  · exact hr

theorem scaleRat_width_of_nonneg {r : Rat} (hr : 0 <= r)
    (x : RealCompute) (n : Nat) :
    ((scaleRat r x).compute n).width = r * (x.compute n).width := by
  unfold scaleRat scaleRatCompute QInterval.width
  simp [hr]
  grind [Rat.sub_eq_add_neg, Rat.mul_add]

/-- Adding rational intervals adds their widths exactly. -/
theorem add_width (x y : RealCompute) (n : Nat) :
    ((x + y).compute n).width =
      (x.compute n).width + (y.compute n).width := by
  change (addCompute x y n).width =
    (x.compute n).width + (y.compute n).width
  unfold addCompute QInterval.width
  grind [Rat.sub_eq_add_neg]

/-- Subtracting rational intervals adds their widths exactly. -/
theorem sub_width (x y : RealCompute) (n : Nat) :
    ((x - y).compute n).width =
      (x.compute n).width + (y.compute n).width := by
  change (subCompute x y n).width =
    (x.compute n).width + (y.compute n).width
  unfold subCompute QInterval.width
  grind [Rat.sub_eq_add_neg]

/-- Natural scaling multiplies an interval width by that natural number. -/
theorem natScale_width (k n : Nat) (x : RealCompute) :
    ((k * x : RealCompute).compute n).width =
      (k : Rat) * (x.compute n).width := by
  change ((scaleRat (k : Rat) x).compute n).width =
    (k : Rat) * (x.compute n).width
  exact scaleRat_width_of_nonneg Rat.natCast_nonneg x n

theorem valid_of_scaleRat_valid_of_pos {r : Rat} {x : RealCompute}
    (hr : 0 < r) (hscale : (scaleRat r x).Valid) : x.Valid := by
  have hr_nonneg : 0 <= r := Rat.le_of_lt hr
  constructor
  · intro n
    have hs := hscale.1 n
    rw [scaleRat_width_of_nonneg hr_nonneg x n] at hs
    have hmul : r * 0 <= r * (x.compute n).width := by
      simpa using hs
    exact le_of_mul_le_mul_pos_left hr hmul
  · constructor
    · intro n m hnm
      have hs := hscale.2.1 n m hnm
      unfold scaleRat scaleRatCompute at hs
      simp [hr_nonneg] at hs
      constructor
      · exact le_of_mul_le_mul_pos_left hr hs.1
      · constructor
        · exact le_of_mul_le_mul_pos_left hr hs.2.1
        · exact le_of_mul_le_mul_pos_left hr hs.2.2
    · intro eps
      let scaled : QPos := ⟨r * eps.val, Rat.mul_pos hr eps.property⟩
      obtain ⟨N, hN⟩ := hscale.2.2 scaled
      refine ⟨N, ?_⟩
      intro n hn
      have hw := hN n hn
      rw [scaleRat_width_of_nonneg hr_nonneg x n] at hw
      have hmul : r * (x.compute n).width <= r * eps.val := by
        simpa [scaled] using hw
      exact le_of_mul_le_mul_pos_left hr hmul

theorem natScale_valid (n : Nat) {x : RealCompute}
    (hx : x.Valid) : (n * x).Valid :=
  scaleRat_valid_of_nonneg (Rat.natCast_nonneg : 0 <= (n : Rat)) hx

theorem valid_of_natScale_valid {n : Nat} {x : RealCompute}
    (hn : 0 < n) (hscale : ((n : Nat) * x : RealCompute).Valid) : x.Valid := by
  change (scaleRat (n : Rat) x).Valid at hscale
  exact valid_of_scaleRat_valid_of_pos
    ((Rat.natCast_pos).2 hn) hscale

theorem scaleRat_equiv_of_nonneg {r : Rat} {x y : RealCompute}
    (hr : 0 <= r) (hxy : x.Equiv y) :
    (scaleRat r x).Equiv (scaleRat r y) := by
  intro n
  have h := (compareAt_overlap_iff x y n n).1 (hxy n)
  apply (compareAt_overlap_iff (scaleRat r x) (scaleRat r y) n n).2
  unfold scaleRat scaleRatCompute
  simp [hr, QInterval.Overlaps]
  exact ⟨Rat.mul_le_mul_of_nonneg_left h.1 hr,
    Rat.mul_le_mul_of_nonneg_left h.2 hr⟩

theorem equiv_of_scaleRat_equiv_of_pos {r : Rat} {x y : RealCompute}
    (hr : 0 < r) (hxy : (scaleRat r x).Equiv (scaleRat r y)) :
    x.Equiv y := by
  have hr_nonneg : 0 <= r := Rat.le_of_lt hr
  intro n
  have h := (compareAt_overlap_iff (scaleRat r x) (scaleRat r y) n n).1
    (hxy n)
  apply (compareAt_overlap_iff x y n n).2
  unfold scaleRat scaleRatCompute at h
  simp [hr_nonneg, QInterval.Overlaps] at h
  exact ⟨le_of_mul_le_mul_pos_left hr h.1,
    le_of_mul_le_mul_pos_left hr h.2⟩

theorem natScale_equiv (n : Nat) {x y : RealCompute}
    (hxy : x.Equiv y) : (n * x).Equiv (n * y) :=
  scaleRat_equiv_of_nonneg (Rat.natCast_nonneg : 0 <= (n : Rat)) hxy

theorem equiv_of_natScale_equiv {n : Nat} {x y : RealCompute}
    (hn : 0 < n) (hxy : ((n : Nat) * x : RealCompute).Equiv (n * y)) :
    x.Equiv y := by
  change (scaleRat (n : Rat) x).Equiv (scaleRat (n : Rat) y) at hxy
  exact equiv_of_scaleRat_equiv_of_pos ((Rat.natCast_pos).2 hn) hxy

theorem neg_equiv {x y : RealCompute}
    (hxy : x.Equiv y) : (-x).Equiv (-y) := by
  intro n
  have h := (compareAt_overlap_iff x y n n).1 (hxy n)
  apply (compareAt_overlap_iff (-x) (-y) n n).2
  change QInterval.Overlaps
    (negCompute x n) (negCompute y n)
  unfold negCompute QInterval.Overlaps
  exact ⟨Rat.neg_le_neg h.2, Rat.neg_le_neg h.1⟩

theorem scaleRat_equiv {r : Rat} {x y : RealCompute}
    (hxy : x.Equiv y) :
    (scaleRat r x).Equiv (scaleRat r y) := by
  by_cases hr : 0 <= r
  · exact scaleRat_equiv_of_nonneg hr hxy
  · have hneg : 0 <= -r := by grind
    have h :=
      scaleRat_equiv_of_nonneg
        (r := -r) (x := RealCompute.neg x) (y := RealCompute.neg y)
        hneg (neg_equiv hxy)
    intro n
    change compareAt (scaleRat r x) (scaleRat r y) n = .overlap
    change compareAt
      { compute := scaleRatCompute r x }
      { compute := scaleRatCompute r y } n = .overlap
    rw [scaleRatCompute_neg_eq_scaleRatCompute_neg hr x,
      scaleRatCompute_neg_eq_scaleRatCompute_neg hr y]
    exact h n

/-- Nonnegative scalar multiplication distributes over raw interval addition,
up to the project's overlap equivalence.  This is finite endpoint algebra;
it does not pass to a quotient or appeal to a completed ordered field. -/
theorem scaleRat_add_equiv_of_nonneg (r : Rat) (hr : 0 <= r)
    (x y : RealCompute) (hx : x.Valid) (hy : y.Valid) :
    (scaleRat r (add x y)).Equiv (add (scaleRat r x) (scaleRat r y)) := by
  intro n
  apply (compareAt_overlap_iff
    (scaleRat r (add x y)) (add (scaleRat r x) (scaleRat r y)) n n).2
  simp only [scaleRat, scaleRatCompute, add, addCompute, if_pos hr]
  change QInterval.Overlaps
    { lo := r * ((x.compute n).lo + (y.compute n).lo),
      hi := r * ((x.compute n).hi + (y.compute n).hi) }
    { lo := r * (x.compute n).lo + r * (y.compute n).lo,
      hi := r * (x.compute n).hi + r * (y.compute n).hi }
  have hxorder := interval_order_of_valid x hx n
  have hyorder := interval_order_of_valid y hy n
  have hsum : (x.compute n).lo + (y.compute n).lo <=
      (x.compute n).hi + (y.compute n).hi := by
    grind [Rat.sub_eq_add_neg]
  have hscaled := Rat.mul_le_mul_of_nonneg_left hsum hr
  unfold QInterval.Overlaps
  constructor <;> grind [Rat.mul_add]

/-- Two nonnegative raw scalings compose to their product scaling.  The
statement is deliberately an interval-overlap equivalence so it is reusable
before any identification of raw representatives. -/
theorem scaleRat_scaleRat_equiv_of_nonneg (r s : Rat)
    (hr : 0 <= r) (hs : 0 <= s) (x : RealCompute) (hx : x.Valid) :
    (scaleRat r (scaleRat s x)).Equiv (scaleRat (r * s) x) := by
  intro n
  apply (compareAt_overlap_iff
    (scaleRat r (scaleRat s x)) (scaleRat (r * s) x) n n).2
  have hrs : 0 <= r * s := Rat.mul_nonneg hr hs
  simp only [scaleRat, scaleRatCompute, if_pos hr, if_pos hs, if_pos hrs]
  change QInterval.Overlaps
    { lo := r * (s * (x.compute n).lo),
      hi := r * (s * (x.compute n).hi) }
    { lo := (r * s) * (x.compute n).lo,
      hi := (r * s) * (x.compute n).hi }
  have horder := interval_order_of_valid x hx n
  have hscaled := Rat.mul_le_mul_of_nonneg_left horder hrs
  unfold QInterval.Overlaps
  constructor <;> grind [Rat.mul_assoc]

theorem add_equiv {x x' y y' : RealCompute}
    (hx : x.Valid) (hx' : x'.Valid)
    (hy : y.Valid) (hy' : y'.Valid)
    (hxx' : x.Equiv x') (hyy' : y.Equiv y') :
    (x + y).Equiv (x' + y') := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  have hxSame := (RealCompute.compareAt_overlap_iff x x' n n).1
    (RealCompute.sameStageOverlap_of_equiv hx hx' hxx' n)
  have hySame := (RealCompute.compareAt_overlap_iff y y' n n).1
    (RealCompute.sameStageOverlap_of_equiv hy hy' hyy' n)
  apply (RealCompute.compareAt_overlap_iff (x + y) (x' + y') n n).2
  unfold QInterval.Overlaps at hxSame hySame
  change QInterval.Overlaps (addCompute x y n) (addCompute x' y' n)
  unfold addCompute QInterval.Overlaps
  constructor <;> grind

/-- Addition of valid raw interval representatives is commutative up to
equivalence. -/
theorem add_comm_equiv (x y : RealCompute) (hx : x.Valid) (hy : y.Valid) :
    (x + y).Equiv (y + x) := by
  intro n
  apply (compareAt_overlap_iff (x + y) (y + x) n n).2
  have hxorder := interval_order_of_valid x hx n
  have hyorder := interval_order_of_valid y hy n
  change QInterval.Overlaps
    { lo := (x.compute n).lo + (y.compute n).lo,
      hi := (x.compute n).hi + (y.compute n).hi }
    { lo := (y.compute n).lo + (x.compute n).lo,
      hi := (y.compute n).hi + (x.compute n).hi }
  unfold QInterval.Overlaps
  constructor <;> grind [Rat.add_comm]

/-- Addition of raw interval representatives is associative up to equivalence.

This permits later analytic identities to regroup certified interval
expressions without selecting a completed-real quotient. -/
theorem add_assoc_equiv (x y z : RealCompute)
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid) :
    ((x + y) + z).Equiv (x + (y + z)) := by
  intro n
  apply (compareAt_overlap_iff ((x + y) + z) (x + (y + z)) n n).2
  have hxorder := interval_order_of_valid x hx n
  have hyorder := interval_order_of_valid y hy n
  have hzorder := interval_order_of_valid z hz n
  change QInterval.Overlaps
    { lo := ((x.compute n).lo + (y.compute n).lo) + (z.compute n).lo,
      hi := ((x.compute n).hi + (y.compute n).hi) + (z.compute n).hi }
    { lo := (x.compute n).lo + ((y.compute n).lo + (z.compute n).lo),
      hi := (x.compute n).hi + ((y.compute n).hi + (z.compute n).hi) }
  unfold QInterval.Overlaps
  constructor <;> grind [Rat.add_assoc]

/-- Scaling a raw real by two agrees with adding it to itself. -/
theorem two_natscale_equiv_add_self (x : RealCompute) (hx : x.Valid) :
    ((2 : Nat) * x).Equiv (x + x) := by
  intro n
  apply (compareAt_overlap_iff ((2 : Nat) * x) (x + x) n n).2
  have hxorder := interval_order_of_valid x hx n
  change QInterval.Overlaps
    (scaleRatCompute (2 : Rat) x n) (addCompute x x n)
  simp [scaleRatCompute, addCompute,
    (by decide +kernel : (0 : Rat) <= 2), QInterval.Overlaps]
  constructor <;> grind [Rat.add_comm]

/-- Scaling a raw real by four agrees with adding two doubled copies. -/
theorem four_natscale_equiv_add_two_natscale (x : RealCompute) (hx : x.Valid) :
    ((4 : Nat) * x).Equiv (((2 : Nat) * x) + ((2 : Nat) * x)) := by
  intro n
  apply (compareAt_overlap_iff
    ((4 : Nat) * x) (((2 : Nat) * x) + ((2 : Nat) * x)) n n).2
  have hxorder := interval_order_of_valid x hx n
  change QInterval.Overlaps
    (scaleRatCompute (4 : Rat) x n)
    (addCompute (scaleRat (2 : Rat) x) (scaleRat (2 : Rat) x) n)
  simp [scaleRat, scaleRatCompute, addCompute,
    (by decide +kernel : (0 : Rat) <= 4),
    (by decide +kernel : (0 : Rat) <= 2), QInterval.Overlaps]
  constructor <;> grind [Rat.add_comm]

theorem zero_add_equiv {x : RealCompute}
    (hx : x.Valid) : (zero + x).Equiv x := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  have horder := RealCompute.interval_order_of_valid x hx n
  apply (RealCompute.compareAt_overlap_iff (zero + x) x n n).2
  change QInterval.Overlaps (addCompute zero x n) (x.compute n)
  unfold addCompute zero ofRat QInterval.Overlaps
  constructor <;> grind

theorem add_zero_equiv {x : RealCompute}
    (hx : x.Valid) : (x + zero).Equiv x := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  have horder := RealCompute.interval_order_of_valid x hx n
  apply (RealCompute.compareAt_overlap_iff (x + zero) x n n).2
  change QInterval.Overlaps (addCompute x zero n) (x.compute n)
  unfold addCompute zero ofRat QInterval.Overlaps
  constructor <;> grind

/-- Subtracting a valid raw representative from itself gives the exact zero
value up to interval overlap.  The runtime box need not be degenerate: its
radius is precisely the numerical uncertainty of the input stage. -/
theorem sub_self_equiv_zero {x : RealCompute}
    (hx : x.Valid) : (x - x).Equiv zero := by
  intro n
  have horder := RealCompute.interval_order_of_valid x hx n
  apply (RealCompute.compareAt_overlap_iff (x - x) zero n n).2
  change QInterval.Overlaps
    { lo := (x.compute n).lo - (x.compute n).hi,
      hi := (x.compute n).hi - (x.compute n).lo }
    { lo := 0, hi := 0 }
  unfold QInterval.Overlaps
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem sub_equiv {x x' y y' : RealCompute}
    (hx : x.Valid) (hx' : x'.Valid)
    (hy : y.Valid) (hy' : y'.Valid)
    (hxx' : x.Equiv x') (hyy' : y.Equiv y') :
    (x - y).Equiv (x' - y') := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  have hxSame := (RealCompute.compareAt_overlap_iff x x' n n).1
    (RealCompute.sameStageOverlap_of_equiv hx hx' hxx' n)
  have hySame := (RealCompute.compareAt_overlap_iff y y' n n).1
    (RealCompute.sameStageOverlap_of_equiv hy hy' hyy' n)
  apply (RealCompute.compareAt_overlap_iff (x - y) (x' - y') n n).2
  unfold QInterval.Overlaps at hxSame hySame
  change QInterval.Overlaps (subCompute x y n) (subCompute x' y' n)
  unfold subCompute QInterval.Overlaps
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem add_sub_cancel_left_equiv {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) :
    ((x + y) - x).Equiv y := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  have hxord := RealCompute.interval_order_of_valid x hx n
  have hyord := RealCompute.interval_order_of_valid y hy n
  apply (RealCompute.compareAt_overlap_iff ((x + y) - x) y n n).2
  change QInterval.Overlaps
    { lo := ((x.compute n).lo + (y.compute n).lo) - (x.compute n).hi,
      hi := ((x.compute n).hi + (y.compute n).hi) - (x.compute n).lo }
    (y.compute n)
  unfold QInterval.Overlaps
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem add_sub_cancel_right_equiv {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) :
    ((x + y) - y).Equiv x := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  have hxord := RealCompute.interval_order_of_valid x hx n
  have hyord := RealCompute.interval_order_of_valid y hy n
  apply (RealCompute.compareAt_overlap_iff ((x + y) - y) x n n).2
  change QInterval.Overlaps
    { lo := ((x.compute n).lo + (y.compute n).lo) - (y.compute n).hi,
      hi := ((x.compute n).hi + (y.compute n).hi) - (y.compute n).lo }
    (x.compute n)
  unfold QInterval.Overlaps
  constructor <;> grind [Rat.sub_eq_add_neg]

/-- Adding back a subtracted valid representative recovers the original raw
real up to interval overlap. -/
theorem sub_add_cancel_equiv {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) :
    ((x - y) + y).Equiv x := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  have hxord := RealCompute.interval_order_of_valid x hx n
  have hyord := RealCompute.interval_order_of_valid y hy n
  apply (RealCompute.compareAt_overlap_iff ((x - y) + y) x n n).2
  change QInterval.Overlaps
    { lo := ((x.compute n).lo - (y.compute n).hi) + (y.compute n).lo,
      hi := ((x.compute n).hi - (y.compute n).lo) + (y.compute n).hi }
    (x.compute n)
  unfold QInterval.Overlaps
  constructor <;> grind [Rat.sub_eq_add_neg]

/-- Telescoping for raw interval representatives:
`(y - x) + (z - y)` is equivalent to `z - x`. -/
theorem sub_add_sub_cancel_middle_equiv {x y z : RealCompute}
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid) :
    ((y - x) + (z - y)).Equiv (z - x) := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  have hxord := RealCompute.interval_order_of_valid x hx n
  have hyord := RealCompute.interval_order_of_valid y hy n
  have hzord := RealCompute.interval_order_of_valid z hz n
  apply (RealCompute.compareAt_overlap_iff ((y - x) + (z - y)) (z - x) n n).2
  change QInterval.Overlaps
    { lo := ((y.compute n).lo - (x.compute n).hi) +
        ((z.compute n).lo - (y.compute n).hi),
      hi := ((y.compute n).hi - (x.compute n).lo) +
        ((z.compute n).hi - (y.compute n).lo) }
    { lo := (z.compute n).lo - (x.compute n).hi,
      hi := (z.compute n).hi - (x.compute n).lo }
  unfold QInterval.Overlaps
  constructor <;> grind [Rat.sub_eq_add_neg]

def Pos (x : RealCompute) : Prop :=
  Exists fun n : Nat => 0 < (x.compute n).lo

def Neg (x : RealCompute) : Prop :=
  Exists fun n : Nat => (x.compute n).hi < 0

def ApartZero (x : RealCompute) : Prop :=
  x.Pos \/ x.Neg

def HasComputableInv (x : RealCompute) : Prop :=
  x.Valid -> ApartZero x -> Exists fun y : RealCompute => y.Valid

end RealCompute

namespace ComplexCompute

def zero : ComplexCompute := ofQComplex QComplex.zero
def one : ComplexCompute := ofQComplex QComplex.one

instance (n : Nat) : OfNat ComplexCompute n where
  ofNat := ofQComplex (QComplex.ofRat n)

def add (z w : ComplexCompute) : ComplexCompute where
  compute := fun eps => QBox.add (z.compute eps) (w.compute eps)

def neg (z : ComplexCompute) : ComplexCompute where
  compute := fun eps => QBox.neg (z.compute eps)

/-- Conjugation of a complex raw computation, with the imaginary interval
    endpoints reversed at each finite stage. -/
def conj (z : ComplexCompute) : ComplexCompute where
  compute := fun eps => QBox.conj (z.compute eps)

/-! Conjugation is also a representation-preserving operation on arbitrary
    valid complex raws, not only on series certificates. -/
theorem conj_valid (z : ComplexCompute) (hz : z.Valid) :
    (ComplexCompute.conj z).Valid := by
  unfold ComplexCompute.Valid ComplexCompute.ValidCompute ComplexCompute.conj
  constructor
  · intro n
    have h := hz.1 n
    simp [QBox.conj, QComplex.conj, QBox.width, QBox.height] at h ⊢
    exact ⟨h.1, by grind⟩

  constructor
  · intro n m hnm
    have h := hz.2.1 n m hnm
    simp [QBox.conj, QComplex.conj, QComplex.le_def] at h ⊢
    exact ⟨h.1, h.2.1, by grind, by grind⟩
  · intro eps
    obtain ⟨N, hN⟩ := hz.2.2 eps
    refine ⟨N, ?_⟩
    intro n hn
    have h := hN n hn
    simp [QBox.conj, QComplex.conj, QBox.width, QBox.height] at h ⊢
    exact ⟨h.1, by grind⟩

theorem conj_conj_equiv (z : ComplexCompute) (hz : z.Valid) :
    (ComplexCompute.conj (ComplexCompute.conj z)).Equiv z := by
  intro n
  apply (ComplexCompute.compareAt_overlap_iff
    (ComplexCompute.conj (ComplexCompute.conj z)) z n n).2
  have ho := ComplexCompute.valid_ordered hz n
  unfold QBox.Ordered at ho
  simpa [ComplexCompute.conj, QBox.conj, QBox.Overlaps] using ho

/-! Conjugation transports an overlap certificate between any two complex
    raw representations. -/
theorem conj_equiv {z w : ComplexCompute} (hzw : z.Equiv w) :
    (ComplexCompute.conj z).Equiv (ComplexCompute.conj w) := by
  intro n
  have h := (ComplexCompute.compareAt_overlap_iff z w n n).1 (hzw n)
  apply (ComplexCompute.compareAt_overlap_iff
    (ComplexCompute.conj z) (ComplexCompute.conj w) n n).2
  simp [ComplexCompute.conj, QBox.conj, QBox.Overlaps] at h ⊢
  exact ⟨⟨h.1.1, h.2.2⟩, ⟨h.2.1, h.1.2⟩⟩

def sub (z w : ComplexCompute) : ComplexCompute :=
  add z (neg w)

def scaleRat (r : Rat) (z : ComplexCompute) : ComplexCompute where
  compute := fun eps => QBox.scaleRat r (z.compute eps)

instance : HAdd ComplexCompute ComplexCompute ComplexCompute where
  hAdd := add

instance : Neg ComplexCompute where
  neg := neg

instance : HSub ComplexCompute ComplexCompute ComplexCompute where
  hSub := sub

instance : HMul Rat ComplexCompute ComplexCompute where
  hMul := scaleRat

instance : HMul Nat ComplexCompute ComplexCompute where
  hMul n z := scaleRat (n : Rat) z

instance : HMul Int ComplexCompute ComplexCompute where
  hMul n z := scaleRat (n : Rat) z

/-- Stabilize a Cauchy family of direct complex-box computations by
intersecting the finite prefix of their explicitly widened boxes.  The runtime
uses only rational box arithmetic; a future-containment proof supplies the
finite witness that keeps every prefix intersection ordered. -/
def cauchyStabilizeCompute
    (candidate : Nat -> QBox) (radius : Nat -> Rat) : Nat -> QBox
  | 0 => QBox.expand (candidate 0) (radius 0)
  | n + 1 => QBox.intersection
      (cauchyStabilizeCompute candidate radius n)
      (QBox.expand (candidate (n + 1)) (radius (n + 1)))

/-- A direct complex Cauchy stabilization.  Its validity theorem below needs
neither a pre-existing complex number nor a completeness principle: later
candidate boxes themselves witness each finite intersection. -/
def cauchyStabilize (candidate : ComplexCompute) (radius : Nat -> Rat) : ComplexCompute where
  compute := cauchyStabilizeCompute candidate.compute radius

private theorem cauchyStabilizeCompute_contains_future
    {candidate : Nat -> QBox} {radius : Nat -> Rat}
    (hfuture : forall k n, k <= n ->
      (candidate n).NestedIn (QBox.expand (candidate k) (radius k))) :
    forall k n, k <= n ->
      (candidate n).NestedIn (cauchyStabilizeCompute candidate radius k) := by
  intro k
  induction k with
  | zero =>
      intro n _
      simpa [cauchyStabilizeCompute] using hfuture 0 n (Nat.zero_le n)
  | succ k ih =>
      intro n hkn
      rw [cauchyStabilizeCompute]
      apply QBox.intersection_contains
      · exact ih n (Nat.le_trans (Nat.le_succ k) hkn)
      · exact hfuture (k + 1) n hkn

/-- An external sequence is contained in a finite-prefix stabilization
whenever each of its future boxes is contained in every widened candidate box.
This is the finite common-witness principle used to compare two separately
stabilized computations. -/
theorem cauchyStabilize_contains_external
    {candidate : ComplexCompute} {radius : Nat -> Rat} {external : Nat -> QBox}
    (hexternal : forall k n, k <= n ->
      (external n).NestedIn
        (QBox.expand (candidate.compute k) (radius k))) :
    forall k n, k <= n ->
      (external n).NestedIn ((cauchyStabilize candidate radius).compute k) := by
  intro k
  change forall n, k <= n ->
    (external n).NestedIn
      (cauchyStabilizeCompute candidate.compute radius k)
  induction k with
  | zero =>
      intro n _
      simpa [cauchyStabilizeCompute] using hexternal 0 n (Nat.zero_le n)
  | succ k ih =>
      intro n hkn
      rw [cauchyStabilizeCompute]
      apply QBox.intersection_contains
      · exact ih n (Nat.le_trans (Nat.le_succ k) hkn)
      · exact hexternal (k + 1) n hkn

private theorem cauchyStabilizeCompute_contained_in_current_expand
    (candidate : Nat -> QBox) (radius : Nat -> Rat) :
    forall n,
      (cauchyStabilizeCompute candidate radius n).NestedIn
        (QBox.expand (candidate n) (radius n))
  | 0 => ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  | n + 1 => by
      rw [cauchyStabilizeCompute]
      exact QBox.intersection_contained_right
        (cauchyStabilizeCompute candidate radius n)
        (QBox.expand (candidate (n + 1)) (radius (n + 1)))

private theorem cauchyStabilizeCompute_nested
    (candidate : Nat -> QBox) (radius : Nat -> Rat) :
    forall n m, n <= m ->
      (cauchyStabilizeCompute candidate radius m).NestedIn
        (cauchyStabilizeCompute candidate radius n)
  | n, 0, hnm => by
      have hn : n = 0 := by omega
      subst n
      exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  | n, m + 1, hnm => by
      by_cases hlast : n = m + 1
      · subst n
        exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
      · have hnm' : n <= m := by omega
        apply QBox.nested_trans
        · rw [cauchyStabilizeCompute]
          exact QBox.intersection_contained_left
            (cauchyStabilizeCompute candidate radius m)
            (QBox.expand (candidate (m + 1)) (radius (m + 1)))
        · exact cauchyStabilizeCompute_nested candidate radius n m hnm'

/-- At stage `n`, the stabilized box still contains the current direct
candidate box.  This is the public finite-witness fact used by extensions of
rational-input algorithms. -/
theorem cauchyStabilize_contains_current
    {candidate : ComplexCompute} {radius : Nat -> Rat}
    (hfuture : forall k n, k <= n ->
      (candidate.compute n).NestedIn
        (QBox.expand (candidate.compute k) (radius k))) (n : Nat) :
    (candidate.compute n).NestedIn ((cauchyStabilize candidate radius).compute n) := by
  exact cauchyStabilizeCompute_contains_future hfuture n n (Nat.le_refl n)

/-- The finite-prefix stabilization does not depend on a particular valid
widening-radius schedule once the direct candidate is fixed.  At every stage
both intersections contain that same ordered rational candidate box, hence
their boxes overlap directly. -/
theorem cauchyStabilize_equiv_of_common_candidate
    {candidate : ComplexCompute} {radius sigma : Nat -> Rat}
    (hordered : forall n, (candidate.compute n).Ordered)
    (hfutureRadius : forall k n, k <= n ->
      (candidate.compute n).NestedIn
        (QBox.expand (candidate.compute k) (radius k)))
    (hfutureSigma : forall k n, k <= n ->
      (candidate.compute n).NestedIn
        (QBox.expand (candidate.compute k) (sigma k))) :
    (cauchyStabilize candidate radius).Equiv
      (cauchyStabilize candidate sigma) := by
  intro n
  apply (compareAt_overlap_iff
    (cauchyStabilize candidate radius)
    (cauchyStabilize candidate sigma) n n).2
  have hRadius := cauchyStabilize_contains_current hfutureRadius n
  have hSigma := cauchyStabilize_contains_current hfutureSigma n
  exact ⟨
    QComplex.le_trans hRadius.1 (QComplex.le_trans (hordered n) hSigma.2),
    QComplex.le_trans hSigma.1 (QComplex.le_trans (hordered n) hRadius.2)⟩

/-- A Cauchy family of finite complex computations produces a valid raw
complex number once its own widths and widening radii shrink.  The proof is
the finite-prefix intersection argument: candidate `n` lies in every widened
box through stage `n`, so that candidate is a rational-box witness for the
intersection.  This is a computation-definition of the limit, not an appeal
to completeness. -/
theorem cauchyStabilize_valid
    {candidate : ComplexCompute} {radius : Nat -> Rat}
    (hcandidate_ordered : forall n, (candidate.compute n).Ordered)
    (hcandidate_shrinks : WidthsShrinkToZero candidate.compute)
    (hfuture : forall k n, k <= n ->
      (candidate.compute n).NestedIn
        (QBox.expand (candidate.compute k) (radius k)))
    (hradius_shrinks : ShrinksToZero radius) :
    (cauchyStabilize candidate radius).Valid := by
  have hcontains := cauchyStabilizeCompute_contains_future hfuture
  have hcurrent := cauchyStabilizeCompute_contained_in_current_expand
    candidate.compute radius
  have hnest := cauchyStabilizeCompute_nested candidate.compute radius
  have hordered : forall n,
      ((cauchyStabilize candidate radius).compute n).Ordered := by
    intro n
    exact QBox.ordered_of_nested (hcandidate_ordered n)
      (hcontains n n (Nat.le_refl n))
  constructor
  · intro n
    exact (QBox.ordered_iff_width_height_nonneg _).1 (hordered n)
  · constructor
    · intro n m hnm
      have hbox := hnest n m hnm
      exact ⟨hbox.1.1, hbox.2.1, hbox.1.2, hbox.2.2⟩
    · intro eps
      let half : QPos := ⟨eps.val / 2, by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property
          ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2))⟩
      let quarter : QPos := ⟨eps.val / 4, by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property
          ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 4))⟩
      obtain ⟨Nc, hNc⟩ := hcandidate_shrinks half
      obtain ⟨Nr, hNr⟩ := hradius_shrinks quarter
      refine ⟨Nat.max Nc Nr, ?_⟩
      intro n hn
      have hcn : Nc <= n := Nat.le_trans (Nat.le_max_left _ _) hn
      have hrn : Nr <= n := Nat.le_trans (Nat.le_max_right _ _) hn
      have hc := hNc n hcn
      have hr := hNr n hrn
      have hcontained := hcurrent n
      have hwidthHeight := QBox.width_height_le_of_nested hcontained
      constructor
      · rw [QBox.expand_width] at hwidthHeight
        calc
          ((cauchyStabilize candidate radius).compute n).width <=
              (candidate.compute n).width + 2 * radius n := hwidthHeight.1
          _ <= half.val + 2 * quarter.val :=
            rat_add_le_add hc.1
              (Rat.mul_le_mul_of_nonneg_left hr (by decide +kernel : (0 : Rat) <= 2))
          _ = eps.val := by
            dsimp [half, quarter]
            rw [Rat.div_def, Rat.div_def]
            grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm,
              Rat.mul_inv_cancel]
      · rw [QBox.expand_height] at hwidthHeight
        calc
          ((cauchyStabilize candidate radius).compute n).height <=
              (candidate.compute n).height + 2 * radius n := hwidthHeight.2
          _ <= half.val + 2 * quarter.val :=
            rat_add_le_add hc.2
              (Rat.mul_le_mul_of_nonneg_left hr (by decide +kernel : (0 : Rat) <= 2))
          _ = eps.val := by
            dsimp [half, quarter]
            rw [Rat.div_def, Rat.div_def]
            grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm,
              Rat.mul_inv_cancel]

private theorem half_pos_complex {q : Rat} (hq : 0 < q) : 0 < q / 2 := by
  rw [Rat.div_def]
  exact Rat.mul_pos hq ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2))

private theorem add_halves_complex (q : Rat) : q / 2 + q / 2 = q := by
  rw [Rat.div_def]
  grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm, Rat.mul_assoc,
    Rat.mul_comm, Rat.mul_inv_cancel]

private theorem valid_re_order
    {compute : Nat -> QBox}
    (h : ComplexCompute.ValidCompute compute) (n : Nat) :
    (compute n).lo.re <= (compute n).hi.re := by
  have hw := (h.1 n).1
  unfold QBox.width at hw
  grind [Rat.sub_eq_add_neg]

private theorem valid_im_order
    {compute : Nat -> QBox}
    (h : ComplexCompute.ValidCompute compute) (n : Nat) :
    (compute n).lo.im <= (compute n).hi.im := by
  have hh := (h.1 n).2
  unfold QBox.height at hh
  grind [Rat.sub_eq_add_neg]

theorem addCompute_valid {z w : ComplexCompute}
    (hz : z.Valid) (hw : w.Valid) :
    ComplexCompute.ValidCompute (fun n =>
      let Z := z.compute n
      let W := w.compute n
      { lo := QComplex.add Z.lo W.lo, hi := QComplex.add Z.hi W.hi }) := by
  constructor
  · intro n
    have hzre := valid_re_order hz n
    have hwre := valid_re_order hw n
    have hzim := valid_im_order hz n
    have hwim := valid_im_order hw n
    constructor
    · unfold QBox.width QComplex.add
      grind [Rat.sub_eq_add_neg]
    · unfold QBox.height QComplex.add
      grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      have hznm := hz.2.1 n m hnm
      have hwnm := hw.2.1 n m hnm
      unfold QComplex.add
      constructor
      · grind
      · constructor
        · grind
        · constructor
          · grind
          · grind
    · intro eps
      let eps2 : QPos := ⟨eps.val / 2, half_pos_complex eps.property⟩
      obtain ⟨Nz, hNz⟩ := hz.2.2 eps2
      obtain ⟨Nw, hNw⟩ := hw.2.2 eps2
      refine ⟨Nat.max Nz Nw, ?_⟩
      intro n hn
      have hnz : Nz <= n := Nat.le_trans (Nat.le_max_left Nz Nw) hn
      have hnw : Nw <= n := Nat.le_trans (Nat.le_max_right Nz Nw) hn
      have hzeps := hNz n hnz
      have hweps := hNw n hnw
      constructor
      · unfold QBox.width QComplex.add
        have hzeps' :
            (z.compute n).hi.re - (z.compute n).lo.re <= eps2.val := by
          simpa [QBox.width] using hzeps.1
        have hweps' :
            (w.compute n).hi.re - (w.compute n).lo.re <= eps2.val := by
          simpa [QBox.width] using hweps.1
        calc
          (z.compute n).hi.re + (w.compute n).hi.re -
              ((z.compute n).lo.re + (w.compute n).lo.re)
              <= eps2.val + eps2.val := by
            grind [Rat.sub_eq_add_neg]
          _ = eps.val := add_halves_complex eps.val
      · unfold QBox.height QComplex.add
        have hzeps' :
            (z.compute n).hi.im - (z.compute n).lo.im <= eps2.val := by
          simpa [QBox.height] using hzeps.2
        have hweps' :
            (w.compute n).hi.im - (w.compute n).lo.im <= eps2.val := by
          simpa [QBox.height] using hweps.2
        calc
          (z.compute n).hi.im + (w.compute n).hi.im -
              ((z.compute n).lo.im + (w.compute n).lo.im)
              <= eps2.val + eps2.val := by
            grind [Rat.sub_eq_add_neg]
          _ = eps.val := add_halves_complex eps.val

theorem add_valid {z w : ComplexCompute}
    (hz : z.Valid) (hw : w.Valid) : (add z w).Valid :=
  addCompute_valid hz hw

theorem negCompute_valid {z : ComplexCompute}
    (hz : z.Valid) :
    ComplexCompute.ValidCompute (fun n =>
      let Z := z.compute n
      { lo := { re := -Z.hi.re, im := -Z.hi.im },
        hi := { re := -Z.lo.re, im := -Z.lo.im } }) := by
  constructor
  · intro n
    have hzre := valid_re_order hz n
    have hzim := valid_im_order hz n
    constructor
    · unfold QBox.width
      change 0 <= -(z.compute n).lo.re - -(z.compute n).hi.re
      grind [Rat.sub_eq_add_neg]
    · unfold QBox.height
      change 0 <= -(z.compute n).lo.im - -(z.compute n).hi.im
      grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      have hznm := hz.2.1 n m hnm
      constructor
      · exact Rat.neg_le_neg hznm.2.1
      · constructor
        · exact Rat.neg_le_neg hznm.1
        · constructor
          · exact Rat.neg_le_neg hznm.2.2.2
          · exact Rat.neg_le_neg hznm.2.2.1
    · intro eps
      obtain ⟨N, hN⟩ := hz.2.2 eps
      refine ⟨N, ?_⟩
      intro n hn
      have hzeps := hN n hn
      constructor
      · unfold QBox.width
        change -(z.compute n).lo.re - -(z.compute n).hi.re <= eps.val
        have hzeps' :
            (z.compute n).hi.re - (z.compute n).lo.re <= eps.val := by
          simpa [QBox.width] using hzeps.1
        grind [Rat.sub_eq_add_neg]
      · unfold QBox.height
        change -(z.compute n).lo.im - -(z.compute n).hi.im <= eps.val
        have hzeps' :
            (z.compute n).hi.im - (z.compute n).lo.im <= eps.val := by
          simpa [QBox.height] using hzeps.2
        grind [Rat.sub_eq_add_neg]

theorem neg_valid {z : ComplexCompute} (hz : z.Valid) : (neg z).Valid :=
  negCompute_valid hz

theorem sub_valid {z w : ComplexCompute}
    (hz : z.Valid) (hw : w.Valid) : (sub z w).Valid :=
  add_valid hz (neg_valid hw)

/-- Left multiplication by the rational imaginary unit.

This is written directly as a coordinate rotation rather than routed through
the still-unproved general complex interval product.  Consequently it is
already available for certified inputs such as `i * pi / 2`: it sends
`x + i y` to `-y + i x` using only endpoint reversal and coordinate exchange.
-/
def mulI (z : ComplexCompute) : ComplexCompute where
  compute := fun n =>
    let Z := z.compute n
    { lo := { re := -Z.hi.im, im := Z.lo.re },
      hi := { re := -Z.lo.im, im := Z.hi.re } }

/-- The direct coordinate rotation preserves validity of a complex raw
algorithm.  The new real width is the old imaginary height, and conversely,
so the proof consumes exactly the two shrinking-width certificates already
present in `ComplexCompute.Valid`. -/
theorem mulI_valid {z : ComplexCompute} (hz : z.Valid) : (mulI z).Valid := by
  constructor
  · intro n
    have hre := valid_re_order hz n
    have him := valid_im_order hz n
    constructor
    · change 0 <= -(z.compute n).lo.im - -(z.compute n).hi.im
      grind [Rat.sub_eq_add_neg]
    · change 0 <= (z.compute n).hi.re - (z.compute n).lo.re
      grind [Rat.sub_eq_add_neg]
  · constructor
    · intro n m hnm
      have hnest := hz.2.1 n m hnm
      constructor
      · change -(z.compute n).hi.im <= -(z.compute m).hi.im
        exact Rat.neg_le_neg hnest.2.2.2
      · constructor
        · change -(z.compute m).lo.im <= -(z.compute n).lo.im
          exact Rat.neg_le_neg hnest.2.2.1
        · constructor
          · change (z.compute n).lo.re <= (z.compute m).lo.re
            exact hnest.1
          · change (z.compute m).hi.re <= (z.compute n).hi.re
            exact hnest.2.1
    · intro eps
      obtain ⟨N, hN⟩ := hz.2.2 eps
      refine ⟨N, ?_⟩
      intro n hn
      have hwidthHeight := hN n hn
      constructor
      · change -(z.compute n).lo.im - -(z.compute n).hi.im <= eps.val
        have hheight : (z.compute n).hi.im - (z.compute n).lo.im <= eps.val :=
          by simpa [QBox.height] using hwidthHeight.2
        grind [Rat.sub_eq_add_neg]
      · change (z.compute n).hi.re - (z.compute n).lo.re <= eps.val
        simpa [QBox.width] using hwidthHeight.1

/-- Multiplication by the imaginary unit respects the raw overlap relation.
No validity or boundedness assumption is needed: it is only a permutation and
endpoint reversal of the two rational coordinate intervals. -/
theorem mulI_equiv {z w : ComplexCompute} (hzw : z.Equiv w) :
    (mulI z).Equiv (mulI w) := by
  intro n
  have hover := (compareAt_overlap_iff z w n n).1 (hzw n)
  apply (compareAt_overlap_iff (mulI z) (mulI w) n n).2
  change QBox.Overlaps
    { lo := { re := -(z.compute n).hi.im, im := (z.compute n).lo.re },
      hi := { re := -(z.compute n).lo.im, im := (z.compute n).hi.re } }
    { lo := { re := -(w.compute n).hi.im, im := (w.compute n).lo.re },
      hi := { re := -(w.compute n).lo.im, im := (w.compute n).hi.re } }
  unfold QBox.Overlaps at hover ⊢
  exact ⟨
    ⟨Rat.neg_le_neg hover.2.2, hover.1.1⟩,
    ⟨Rat.neg_le_neg hover.1.2, hover.2.1⟩⟩

/-- Embed a certified raw real on the imaginary axis.  This is the concrete
constructor for represented arguments of the form `i * x`; it does not claim
the missing general complex multiplication theorem. -/
def imaginaryAxis (x : RealCompute) : ComplexCompute :=
  mulI (ofRealCompute x)

theorem imaginaryAxis_valid {x : RealCompute} (hx : x.Valid) :
    (imaginaryAxis x).Valid :=
  mulI_valid (ofRealCompute_valid x hx)

/-- Imaginary-axis embedding respects equivalence of real raw
representatives. -/
theorem imaginaryAxis_equiv {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y) :
    (imaginaryAxis x).Equiv (imaginaryAxis y) :=
  mulI_equiv (ofRealCompute_equiv_of_equiv hx hy hxy)

theorem imaginaryAxis_compute (x : RealCompute) (n : Nat) :
    (imaginaryAxis x).compute n =
      { lo := { re := 0, im := (x.compute n).lo },
        hi := { re := 0, im := (x.compute n).hi } } := by
  rfl

/-- Nonnegative rational scaling preserves validity of a complex raw
algorithm.  Both coordinate widths are multiplied by the same rational, so a
requested output tolerance is pulled back through a positive scale factor. -/
theorem scaleRat_valid_of_nonneg {r : Rat} (hr : 0 <= r)
    {z : ComplexCompute} (hz : z.Valid) : (scaleRat r z).Valid := by
  constructor
  · intro n
    have hre := valid_re_order hz n
    have him := valid_im_order hz n
    constructor
    · simp only [scaleRat, QBox.scaleRat, if_pos hr, QBox.width]
      change 0 <= r * (z.compute n).hi.re - r * (z.compute n).lo.re
      have hmul := Rat.mul_le_mul_of_nonneg_left hre hr
      grind [Rat.sub_eq_add_neg, Rat.mul_add]
    · simp only [scaleRat, QBox.scaleRat, if_pos hr, QBox.height]
      change 0 <= r * (z.compute n).hi.im - r * (z.compute n).lo.im
      have hmul := Rat.mul_le_mul_of_nonneg_left him hr
      grind [Rat.sub_eq_add_neg, Rat.mul_add]
  · constructor
    · intro n m hnm
      have hnest := hz.2.1 n m hnm
      simp only [scaleRat, QBox.scaleRat, if_pos hr]
      exact ⟨
        Rat.mul_le_mul_of_nonneg_left hnest.1 hr,
        Rat.mul_le_mul_of_nonneg_left hnest.2.1 hr,
        Rat.mul_le_mul_of_nonneg_left hnest.2.2.1 hr,
        Rat.mul_le_mul_of_nonneg_left hnest.2.2.2 hr⟩
    · intro eps
      by_cases hrzero : r = 0
      · subst r
        refine ⟨0, ?_⟩
        intro n _hn
        constructor <;>
          grind [scaleRat, QBox.scaleRat, QBox.width, QBox.height,
            Rat.sub_eq_add_neg]
      · have hrpos : 0 < r := by grind
        let scaled : QPos :=
          ⟨eps.val / r, by
            rw [Rat.div_def]
            exact Rat.mul_pos eps.property ((Rat.inv_pos).2 hrpos)⟩
        obtain ⟨N, hN⟩ := hz.2.2 scaled
        refine ⟨N, ?_⟩
        intro n hn
        have hwidthHeight := hN n hn
        have hscale : r * scaled.val = eps.val := by
          dsimp [scaled]
          rw [Rat.div_def]
          have hrne : r ≠ 0 := Rat.ne_of_gt hrpos
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        constructor
        · have hwidth :
            (z.compute n).hi.re - (z.compute n).lo.re <= scaled.val :=
            by simpa [QBox.width] using hwidthHeight.1
          simp only [scaleRat, QBox.scaleRat, if_pos hr, QBox.width]
          change r * (z.compute n).hi.re - r * (z.compute n).lo.re <= eps.val
          calc
            r * (z.compute n).hi.re - r * (z.compute n).lo.re =
                r * ((z.compute n).hi.re - (z.compute n).lo.re) := by
                  grind [Rat.sub_eq_add_neg, Rat.mul_add]
            _ <= r * scaled.val :=
              Rat.mul_le_mul_of_nonneg_left hwidth hr
            _ = eps.val := hscale
        · have hheight :
            (z.compute n).hi.im - (z.compute n).lo.im <= scaled.val :=
            by simpa [QBox.height] using hwidthHeight.2
          simp only [scaleRat, QBox.scaleRat, if_pos hr, QBox.height]
          change r * (z.compute n).hi.im - r * (z.compute n).lo.im <= eps.val
          calc
            r * (z.compute n).hi.im - r * (z.compute n).lo.im =
                r * ((z.compute n).hi.im - (z.compute n).lo.im) := by
                  grind [Rat.sub_eq_add_neg, Rat.mul_add]
            _ <= r * scaled.val :=
              Rat.mul_le_mul_of_nonneg_left hheight hr
            _ = eps.val := hscale

/-- Nonnegative rational scaling respects complex raw equivalence.  This is
the small compatibility lemma needed to pass from the certified input
`i * pi` to `i * pi / 2`. -/
theorem scaleRat_equiv_of_nonneg {r : Rat} (hr : 0 <= r)
    {z w : ComplexCompute} (hzw : z.Equiv w) :
    (scaleRat r z).Equiv (scaleRat r w) := by
  intro n
  have hover := (compareAt_overlap_iff z w n n).1 (hzw n)
  apply (compareAt_overlap_iff (scaleRat r z) (scaleRat r w) n n).2
  simp only [scaleRat, QBox.scaleRat, if_pos hr]
  change QBox.Overlaps
    { lo := { re := r * (z.compute n).lo.re, im := r * (z.compute n).lo.im },
      hi := { re := r * (z.compute n).hi.re, im := r * (z.compute n).hi.im } }
    { lo := { re := r * (w.compute n).lo.re, im := r * (w.compute n).lo.im },
      hi := { re := r * (w.compute n).hi.re, im := r * (w.compute n).hi.im } }
  unfold QBox.Overlaps at hover ⊢
  exact ⟨
    ⟨Rat.mul_le_mul_of_nonneg_left hover.1.1 hr,
      Rat.mul_le_mul_of_nonneg_left hover.1.2 hr⟩,
    ⟨Rat.mul_le_mul_of_nonneg_left hover.2.1 hr,
      Rat.mul_le_mul_of_nonneg_left hover.2.2 hr⟩⟩

def mul (z w : ComplexCompute) : ComplexCompute where
  compute := fun eps => QBox.mul (z.compute eps) (w.compute eps)

instance : HMul ComplexCompute ComplexCompute ComplexCompute where
  hMul := mul

def divReal (z : ComplexCompute) (x : RealCompute) : ComplexCompute where
  compute := fun eps =>
    QBox.mul (z.compute eps) (QBox.ofRealInterval ((x.compute eps).inv))

instance : HDiv ComplexCompute RealCompute ComplexCompute where
  hDiv := divReal

def pow (z : ComplexCompute) : Nat -> ComplexCompute
  | 0 => one
  | n + 1 => pow z n * z

instance : Pow ComplexCompute Nat where
  pow := pow

def ApartZero (z : ComplexCompute) : Prop :=
  Exists fun n : Nat =>
    (z.compute n).hi.re < 0 \/ 0 < (z.compute n).lo.re \/
    (z.compute n).hi.im < 0 \/ 0 < (z.compute n).lo.im

def HasComputableInv (z : ComplexCompute) : Prop :=
  z.Valid -> ApartZero z -> Exists fun w : ComplexCompute => w.Valid

def divByApart (_z w : ComplexCompute) : Prop :=
  w.Valid -> ApartZero w -> Exists fun quotient : ComplexCompute => quotient.Valid

end ComplexCompute

end ComputableAnalysis

namespace ComputableAnalysis.RealCompute
theorem prefixStabilize_width_le_current_expand
    (candidate : RealCompute) (radius : Nat -> Rat) (n : Nat) :
    ((prefixStabilize candidate radius).compute n).width <=
      (candidate.compute n).width + 2 * radius n := by
  have hcontains := prefixStabilize_contained_in_current_expand candidate radius n
  exact Rat.le_trans
    (QInterval.width_le_of_contains hcontains)
    (by rw [QInterval.expand_width]; exact Rat.le_refl)


end ComputableAnalysis.RealCompute

namespace ComputableAnalysis.ComplexCompute
theorem cauchyStabilize_width_le_current_expand
    {candidate : ComplexCompute} {radius : Nat -> Rat}
    (n : Nat) :
    ((cauchyStabilize candidate radius).compute n).width <=
      (candidate.compute n).width + 2 * radius n := by
  have hcurrent := cauchyStabilizeCompute_contained_in_current_expand
    candidate.compute radius n
  have hwidthHeight := QBox.width_height_le_of_nested hcurrent
  rw [QBox.expand_width] at hwidthHeight
  exact hwidthHeight.1

theorem cauchyStabilize_height_le_current_expand
    {candidate : ComplexCompute} {radius : Nat -> Rat}
    (n : Nat) :
    ((cauchyStabilize candidate radius).compute n).height <=
      (candidate.compute n).height + 2 * radius n := by
  have hcurrent := cauchyStabilizeCompute_contained_in_current_expand
    candidate.compute radius n
  have hwidthHeight := QBox.width_height_le_of_nested hcurrent
  rw [QBox.expand_height] at hwidthHeight
  exact hwidthHeight.2


end ComputableAnalysis.ComplexCompute


