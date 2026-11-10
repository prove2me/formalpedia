-- Prove2me | Definitions.Def_HighPrecSAC1_Main_Floating
-- name    : HighPrecSAC1_Main_Floating
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:22:25.422037+00:00
-- url     : https://prove2.me/theorems/378e6992-bef7-4a09-ade1-05045c2d3073
-- title:
--   Normalized binary floating-point words and numerical circuit interfaces
-- statement:
--   A word has a zero flag, a nonnegative odd significand of binary length at most p, and an integer exponent with sign-magnitude width at most b. Its value is zero or M times 2 to the exponent minus the significand length. The fixed bit layout and its decoder are explicit. Floor and ceiling on the appropriate binary grid define directed rounding for positive reals, and return zero at zero. Numerical circuit families must accept every valid encoding and produce valid output words with the specified numerical relation; invalid input encodings have no prescribed behavior.
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Definitions and constructions, §§2, 3, 6, 7, printed p. 10 (PDF 11)

import Definitions.Def_HighPrecSAC1_Main_Uniformity

namespace HighPrecSAC1.Main

/-- Definition 2.4; the exponent uses sign-magnitude binary. -/
structure FloatRep where
  zero : Bool
  significand : ℕ
  exponent : ℤ

noncomputable def FloatRep.value (w : FloatRep) : ℝ :=
  if w.zero then 0 else (w.significand : ℝ) * (2 : ℝ)^(w.exponent - bitLength w.significand)

def FloatRep.Valid (p b : ℕ) (w : FloatRep) : Prop :=
  1 ≤ p ∧ 1 ≤ b ∧ (w.zero = true ∨
    (0 < w.significand ∧ Odd w.significand ∧ bitLength w.significand ≤ p ∧
      w.exponent.natAbs < 2^(b-1)))

noncomputable def IsFloat (p b : ℕ) (x : ℝ) : Prop :=
  ∃ w : FloatRep, w.Valid p b ∧ w.value = x

noncomputable def HasPrecision (p : ℕ) (x : ℝ) : Prop := ∃ b, IsFloat p b x

def wordLength (p b : ℕ) : ℕ := 1 + p + b

/-- zero flag, p low-to-high significand bits, sign, b-1 magnitude bits. -/
def FloatRep.encode (p b : ℕ) (w : FloatRep) : Fin (wordLength p b) → Bool := fun i =>
  if i.val = 0 then w.zero else
  if i.val ≤ p then w.significand.testBit (i.val-1) else
  if i.val = p+1 then decide (w.exponent < 0) else
    w.exponent.natAbs.testBit (i.val-p-2)

def bitsNat (w : ℕ → Bool) (length : ℕ) : ℕ :=
  ∑ i ∈ Finset.range length, if w i then 2^i else 0

def decode (p b : ℕ) (w : Fin (wordLength p b) → Bool) : FloatRep :=
  let bit := fun i => if h : i < wordLength p b then w ⟨i,h⟩ else false
  let mag := bitsNat (fun i => bit (p+2+i)) (b-1)
  ⟨bit 0, bitsNat (fun i => bit (i+1)) p,
    if bit (p+1) then -(mag : ℤ) else (mag : ℤ)⟩

noncomputable def Encodes (p b : ℕ) (w : Fin (wordLength p b) → Bool) (x : ℝ) : Prop :=
  (decode p b w).Valid p b ∧ (decode p b w).value = x

noncomputable def roundDown (s : ℕ) (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else
    let u := (2 : ℝ) ^ (⌊lg x⌋ + 1 - (s : ℤ))
    (⌊x / u⌋ : ℝ) * u

noncomputable def roundUp (s : ℕ) (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else
    let u := (2 : ℝ) ^ (⌊lg x⌋ + 1 - (s : ℤ))
    (⌈x / u⌉ : ℝ) * u

noncomputable def posSub (x y : ℝ) : ℝ := max (x-y) 0
noncomputable def err (t : ℕ) : ℝ := (2 : ℝ)^(-(t : ℤ))

/-- Flatten words consecutively, indexed by operand then bit. -/
def packWords {m p b : ℕ} (w : Fin m → Fin (wordLength p b) → Bool) :
    Fin (m * wordLength p b) → Bool := fun i =>
  w ⟨i.val / wordLength p b, Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using i.isLt)⟩
    ⟨i.val % wordLength p b, Nat.mod_lt _ (by unfold wordLength; omega)⟩

/-- The numerical circuit relation includes validity, fixed output layout and every input encoding.
    The size and uniformity parameter is n; the input has m(n) words. -/
noncomputable def Numerical (m p b outputs po bo : ℕ → ℕ) (d : ℕ → ℝ)
    (relation : ∀ n, (Fin (m n) → ℝ) → (Fin (outputs n) → ℝ) → Prop)
    (start : ℕ := 1) : Prop :=
  ∃ C : ∀ n, BCircuit (m n * wordLength (p n) (b n))
      (outputs n * wordLength (po n) (bo n)),
    BUniform C start ∧ BPoly C ∧ BDepthBound C d (max 3 start) ∧
    ∀ n, start ≤ n → ∀ w : Fin (m n) → Fin (wordLength (p n) (b n)) → Bool,
      (∀ j, (decode (p n) (b n) (w j)).Valid (p n) (b n)) →
      ∃ z : Fin (outputs n) → Fin (wordLength (po n) (bo n)) → Bool,
        bEval (C n) (packWords w) = packWords z ∧
        (∀ j, (decode (po n) (bo n) (z j)).Valid (po n) (bo n)) ∧
        relation n (fun j => (decode (p n) (b n) (w j)).value)
          (fun j => (decode (po n) (bo n) (z j)).value)

end HighPrecSAC1.Main


