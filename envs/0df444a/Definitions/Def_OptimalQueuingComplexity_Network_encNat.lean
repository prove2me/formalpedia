-- Prove2me | Definitions.Def_OptimalQueuingComplexity_Network_encNat
-- name    : OptimalQueuingComplexity_Network_encNat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T09:03:17.005696+00:00
-- url     : https://prove2.me/theorems/1b0fb083-15f3-4134-89ec-b9be7a1ebf99
-- title:
--   Length-faithful binary encodings of naturals, integers, rationals and tables
-- statement:
--   Instances of the decision problems of this mission are presented to Turing machines as bit strings built by concatenation of self-delimiting pieces.
--
--   * A natural number $n$ is written as its binary digits $b_0 b_1 \dots b_{m-1}$ (least significant first, none for $n = 0$), each digit doubled, followed by the terminator $01$:
--   $$\mathrm{encNat}(n) = b_0 b_0\, b_1 b_1 \cdots b_{m-1} b_{m-1}\, 0\, 1,$$
--   so its length is $2m + 2 = O(\log n)$.
--   * An integer is a sign bit (1 iff negative) followed by $\mathrm{encNat}$ of its absolute value; a rational number is the encoding of the numerator of its reduced form followed by $\mathrm{encNat}$ of its (positive) denominator.
--   * A Boolean is one bit; an element $i$ of $\{0, \dots, n-1\}$ is $\mathrm{encNat}(i)$; an optional value is $0$ for "none" and $1$ followed by the value's encoding otherwise.
--   * A table $f : \{0,\dots,n-1\} \to \alpha$ is the concatenation $e(f(0))\, e(f(1)) \cdots e(f(n-1))$ of its entries.
--
--   These encodings are length-faithful: the encoded length of an instance is polynomial in its bit size and conversely. This matters for exponential-time classes, where an encoding with exponential padding (such as iterated Cantor pairing) would make membership in EXP artificially easy.
--
--   **Formalization Note.** `encNat` uses Mathlib's `Nat.bits`. The table encoding does not repeat the table's length: every instance encoding writes its dimensions first.
-- source:
--   Papadimitriou & Tsitsiklis, The Complexity of Optimal Queuing Network Control, Math. Oper. Res. 24(2) (1999), p. 295, Section 2 (instances are given by finite sets, rationals and integers); encoding convention of this mission

import Mathlib

namespace OptimalQueuingComplexity.Network

/-- Self-delimiting binary numeral for a natural number `n`: the binary digits of `n`
(`Nat.bits n`, least significant first; empty for `n = 0`), each digit written twice, followed
by the terminator `01` (i.e. `[false, true]`). Its length is `2·(number of binary digits of n) + 2`,
so it is logarithmic in `n`. This is the length-faithful encoding used for every natural number
of an instance (never `Encodable`/`Nat.pair`, whose padding is exponential). -/
def encNat (n : ℕ) : List Bool :=
  (n.bits.flatMap fun b => [b, b]) ++ [false, true]

/-- An integer in sign-and-magnitude form: one sign bit (`true` iff negative), then the
magnitude as `encNat`. -/
def encInt (z : ℤ) : List Bool :=
  decide (z < 0) :: encNat z.natAbs

/-- A rational number as the pair (numerator, denominator) of its reduced form: `encInt` of the
numerator followed by `encNat` of the (positive) denominator. -/
def encRat (q : ℚ) : List Bool :=
  encInt q.num ++ encNat q.den

/-- A Boolean as the single bit itself. -/
def encBool (b : Bool) : List Bool := [b]

/-- An element `i` of `Fin n` as the binary numeral `encNat i`. -/
def encFin {n : ℕ} (i : Fin n) : List Bool := encNat i.val

/-- An optional value: `[false]` for `none`, and `true` followed by the value's encoding for
`some a`. -/
def encOption {α : Type} (e : α → List Bool) : Option α → List Bool
  | none => [false]
  | some a => true :: e a

/-- A table `f : Fin n → α` as the concatenation `e (f 0) ++ e (f 1) ++ … ++ e (f (n-1))` of its
entries in index order. The length `n` is not repeated here: every instance encoding writes
its dimensions first, so the table is self-delimiting in context. -/
def encTable {n : ℕ} {α : Type} (e : α → List Bool) (f : Fin n → α) : List Bool :=
  (List.finRange n).flatMap fun i => e (f i)

end OptimalQueuingComplexity.Network


