-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_CyclicTokenMasks
-- name    : Sensitivity214439_PairedSemantic_Solutions_CyclicTokenMasks
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:45:37.166802+00:00
-- url     : https://prove2.me/theorems/2888464a-c10b-44cb-8961-32f4b97866be
-- title:
--   Integer encoding and rotated masks for cyclic tokens
-- statement:
--   Encode a token $(m,b)\in\operatorname{Fin}(n)\times\operatorname{Fin}(2)$ as $2m+b$. This encoding is injective, lies below $2n$, and recovers the macro and side by quotient and remainder modulo two.
--
--   Adjacency masks are rotations, by twice the source macro, of one of two base masks selected by the source side. Marker masks are rotations of one marker base mask. The bit identities identify these rotations with subtraction of the source macro, so a finite check at displacement zero determines all translated adjacency and marker relations.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/CyclicTokenMasks.lean lines 8–104; SHA256 95d63f7560160d20452b98d4c425f380bf929651b8759588895108e5f89c9bb6; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Ring.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Nat.Bitwise

namespace SensitivityCyclicTokens
end SensitivityCyclicTokens



/-! Compact bit-mask rows for a two-token cyclic graph. -/

namespace SensitivityCyclicTokens

def rotateMask (width shift mask : ℕ) : ℕ :=
  ((mask <<< shift) ||| (mask >>> (width - shift))) &&& (2 ^ width - 1)

theorem testBit_rotateMask {width shift mask i : ℕ}
    (hs : shift < width) (hi : i < width) (hm : mask < 2 ^ width) :
    (rotateMask width shift mask).testBit i =
      mask.testBit ((i + width - shift) % width) := by
  simp only [rotateMask, Nat.testBit_and, Nat.testBit_or,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    hi, decide_true, Bool.and_true]
  by_cases his : shift ≤ i
  · have hbig : width ≤ width - shift + i := by omega
    have hfalse : mask.testBit (width - shift + i) = false :=
      Nat.testBit_lt_two_pow (hm.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hbig))
    have heq : i + width - shift = (i - shift) + width := by omega
    have hsmall : i - shift < width := by omega
    simp only [his, decide_true, Bool.true_and, hfalse, Bool.or_false,
      heq, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt hsmall]
  · have hsmall : i + width - shift < width := by omega
    have heq : width - shift + i = i + width - shift := by omega
    simp only [his, decide_false, Bool.false_and, Bool.false_or,
      heq, Nat.mod_eq_of_lt hsmall]

def encode {n : ℕ} (token : Fin n × Fin 2) : ℕ := 2 * token.1.val + token.2.val

theorem encode_lt {n : ℕ} (token : Fin n × Fin 2) : encode token < 2 * n := by
  have hv := token.1.isLt
  have hb := token.2.isLt
  unfold encode
  omega

theorem encode_injective {n : ℕ} : Function.Injective (@encode n) := by
  intro a b hab
  have ha := a.2.isLt
  have hb := b.2.isLt
  unfold encode at hab
  apply Prod.ext <;> apply Fin.ext <;> omega

theorem encode_div_two {n : ℕ} (token : Fin n × Fin 2) :
    encode token / 2 = token.1.val := by
  have hb := token.2.isLt
  unfold encode
  omega

theorem encode_mod_two {n : ℕ} (token : Fin n × Fin 2) :
    encode token % 2 = token.2.val := by
  have hb := token.2.isLt
  unfold encode
  omega

theorem token_difference {n : ℕ} (v w : Fin n) (b : Fin 2) :
    (encode (w, b) + 2 * n - 2 * v.val) % (2 * n) = encode (w - v, b) := by
  have hv := v.isLt
  have hw := w.isLt
  have hb := b.isLt
  have hsub : (w - v).val = (w.val + n - v.val) % n := by
    rw [Fin.val_sub]
    congr 1
    omega
  unfold encode
  dsimp only
  rw [hsub]
  by_cases hvw : v.val ≤ w.val
  · have heq : w.val + n - v.val = (w.val - v.val) + n := by omega
    have heq' : 2 * w.val + b.val + 2 * n - 2 * v.val =
        (2 * (w.val - v.val) + b.val) + 2 * n := by omega
    have hd : w.val - v.val < n := by omega
    have ht : 2 * (w.val - v.val) + b.val < 2 * n := by omega
    simp only [heq, heq', Nat.add_mod, Nat.mod_self, Nat.add_zero,
      Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt ht]
  · have hd : w.val + n - v.val < n := by omega
    have ht : 2 * w.val + b.val + 2 * n - 2 * v.val < 2 * n := by omega
    rw [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt ht]
    omega

def adjacency (n base0 base1 : ℕ) (v : ℕ) : ℕ :=
  rotateMask (2 * n) (2 * (v / 2)) (if v % 2 = 0 then base0 else base1)

def marker (n base : ℕ) (v : ℕ) : ℕ := rotateMask (2 * n) (2 * v) base

theorem adjacency_token {n base0 base1 : ℕ}
    (h0 : base0 < 2 ^ (2 * n)) (h1 : base1 < 2 ^ (2 * n))
    (a b : Fin n × Fin 2) :
    (adjacency n base0 base1 (encode a)).testBit (encode b) =
      (if a.2.val = 0 then base0 else base1).testBit (encode (b.1 - a.1, b.2)) := by
  unfold adjacency
  rw [encode_div_two, encode_mod_two]
  rw [testBit_rotateMask (by have h := a.1.isLt; omega) (encode_lt b)
    (by split <;> assumption), token_difference]

theorem marker_token {n base : ℕ} (hbase : base < 2 ^ (2 * n))
    (v : Fin n) (b : Fin n × Fin 2) :
    (marker n base v.val).testBit (encode b) =
      base.testBit (encode (b.1 - v, b.2)) := by
  unfold marker
  rw [testBit_rotateMask (by have h := v.isLt; omega) (encode_lt b) hbase,
    token_difference]



end SensitivityCyclicTokens


