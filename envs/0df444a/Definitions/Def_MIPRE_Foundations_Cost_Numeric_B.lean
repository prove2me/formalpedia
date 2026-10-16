-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
-- name    : MIPRE_Foundations_Cost_Numeric_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:33:54.212354+00:00
-- url     : https://prove2.me/theorems/c1871a29-1cbc-4449-9c06-875372cdf12c
-- title:
--   Supplement to the binary-number programs: well-scopedness of the decrement and value lemmas for bit strings
-- statement:
--   This bundle adds eight lemmas to the already published bundle `MIPRE_Foundations_Cost_Numeric` (binary numbers as bit strings, least significant bit first: the value `MIPRE.Cost.bitsVal`, the zero test `isZeroProg`, the decrement `decBody`/`decProg` and the next-level map). It contains no new definitions. Throughout, `BitStr = List Bool`, `bitsVal l = l.foldr Nat.bit 0`, `encode l` is the `cons`-chain of the bits of `l`, and `List.replicate j b` is the string of $j$ copies of the bit $b$.
--
--   Programs. `MIPRE.Cost.Prog.decBody_wellScoped : decBody.WellScoped 1` and `MIPRE.Cost.Prog.decProg_wellScoped : decProg.WellScoped 1`: the body of the decrement loop and the decrement program are closed (well scoped in a one-entry environment).
--
--   Values. `MIPRE.Cost.bitsVal_bits (n : ℕ) : bitsVal n.bits = n`. `MIPRE.Cost.bitsVal_eq_zero_iff (l) : bitsVal l = 0 ↔ l.any id = false`. `MIPRE.Cost.exists_split_of_any (l) (h : l.any id = true) : ∃ j rest, l = List.replicate j false ++ true :: rest`. `MIPRE.Cost.bitsVal_replicate_true_append (j rest)` is the carry identity
--
--   $$\mathrm{bitsVal}\,(\mathtt{true}^{\,j} \cdot \mathtt{false} \cdot r) + 1 = \mathrm{bitsVal}\,(\mathtt{false}^{\,j} \cdot \mathtt{true} \cdot r).$$
--
--   Sizes. `MIPRE.Cost.size_encode_replicate_false_append (j rest) : (encode (List.replicate j false ++ true :: rest)).size = 2 * j + (encode rest).size + 4`, and `MIPRE.Cost.size_two_mul_add_one (n) : Nat.size (2 * n + 1) = Nat.size n + 1`.
--
--   These are the facts the binary arithmetic bundles consume: the split of a nonzero numeral as $\mathtt{false}^j \cdot \mathtt{true} \cdot r$ and the carry identity are what the specification of the borrow (`decBits`) rests on, and the size equations feed the cost accounting of programs that walk a numeral.
--
--   **Formalization Note**. The bundle is a delta: it adds these declarations to the published bundle `MIPRE_Foundations_Cost_Numeric`, whose definitions they are about. `bitsVal` is defined on canonical and non-canonical strings alike (trailing `false` bits allowed), which is why the decrement is specified through it rather than through `Nat.bits`. A bit encodes as `nil` (`false`, size $1$) or `cons nil nil` (`true`, size $3$) and a string as the `cons`-chain of its bits, which gives the constants $2j$ and $4$ in the size equation. `Nat.size` is the number of binary digits. `l.any id` is the Boolean "some bit of `l` is set".
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Numeric.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Numeric.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Cost_Numeric does not carry);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric

/-!
# The closure library, part IV: binary numbers

Programs on binary numbers presented as bit strings (LSB first, as in `Nat.bits`), used by
the bit-query program of the recursive compression argument: the zero test
(`isZeroProg`) and decrement (`decProg`). Decrement flips the leading `false`s to `true`
and the first `true` to `false`; it may leave a non-canonical representation (trailing
`false`s), which is why the specifications are in terms of the *value* `bitsVal` of a bit
string rather than `Nat.bits`.

Costs: every list walk is quadratic in this model (the loop state is rebuilt each
iteration, copying the tail), so bounds have the form `(iterations + 1) · (S + c)` with `S`
dominating the sizes involved.
-/

namespace MIPRE.Cost

/-! ## Bit strings as data -/

theorem size_encode_replicate_false_append (j : ℕ) (rest : BitStr) :
    (encode (List.replicate j false ++ true :: rest)).size = 2 * j + (encode rest).size + 4 := by
  induction j with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, encode_bitStr_cons, Data.size_cons,
      Data.ofBool_true, Data.size_nil]
    omega
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append, encode_bitStr_cons, Data.size_cons,
      Data.ofBool_false, Data.size_nil, ih]
    omega

theorem bitsVal_bits (n : ℕ) : bitsVal n.bits = n := Nat.foldr_bit_bits n

theorem bitsVal_eq_zero_iff (l : BitStr) : bitsVal l = 0 ↔ l.any id = false := by
  induction l with
  | nil => simp
  | cons b l ih =>
    cases b <;> simp [Nat.bit_val, ih]

theorem bitsVal_replicate_true_append (j : ℕ) (rest : BitStr) :
    bitsVal (List.replicate j true ++ false :: rest) + 1 =
      bitsVal (List.replicate j false ++ true :: rest) := by
  induction j with
  | zero => simp [Nat.bit_val]
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append, bitsVal_cons, Nat.bit_val,
      Bool.toNat_false, Bool.toNat_true]
    omega

/-- A bit string with a `true` bit splits as `false^j ++ true :: rest`. -/
theorem exists_split_of_any (l : BitStr) (h : l.any id = true) :
    ∃ j rest, l = List.replicate j false ++ true :: rest := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    cases b with
    | true => exact ⟨0, l, rfl⟩
    | false =>
      simp only [List.any_cons, id, Bool.false_or] at h
      obtain ⟨j, rest, rfl⟩ := ih h
      exact ⟨j + 1, rest, by simp [List.replicate_succ]⟩

namespace Prog

/-! ## Zero test -/

/-! ## Decrement -/

theorem decBody_wellScoped : decBody.WellScoped 1 := by
  simp [decBody, WellScoped]

theorem decProg_wellScoped : decProg.WellScoped 1 :=
  ⟨⟨Nat.zero_lt_one, trivial⟩,
    ⟨⟨Nat.zero_lt_succ 1, decBody_wellScoped.mono (by omega) _⟩,
      revOntoProg_wellScoped.mono (by omega) _⟩⟩

end Prog

/-! ## The next level index -/

theorem size_two_mul_add_one (n : ℕ) : Nat.size (2 * n + 1) = Nat.size n + 1 := by
  rw [← Nat.bit_true_apply, Nat.size_bit (by rw [Nat.bit_true_apply]; omega)]

end MIPRE.Cost


