-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Numeric
-- name    : MIPRE_Foundations_Cost_Numeric
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-12T16:06:05.608106+00:00
-- url     : https://prove2.me/theorems/870282b4-94a1-45c6-93c2-79fa7bdd3dc4
-- title:
--   The closure library IV: binary numbers, zero test, decrement and the next-level map $n \mapsto 2n+1$
-- statement:
--   This bundle contains the programs on binary numbers used by the bit-query program of the recursive compression argument, and the "next level" map of the recursion.
--
--   `MIPRE.Cost.bitsVal` $l$ is the value $\sum_i l_i\, 2^i$ of a bit string $l$ read least significant bit first, defined for canonical and non-canonical representations alike (trailing zero bits are allowed).
--
--   `MIPRE.Cost.Prog.isZeroBody` and `MIPRE.Cost.Prog.isZeroProg` $= \mathtt{loop}\ \mathrm{isZeroBody}$ walk a bit string and return the encoding of the Boolean "some bit is set": $\mathtt{nil}$ (false) exactly when the value is zero, and $\mathtt{cons}(\mathtt{nil}, \mathtt{nil})$ (true) as soon as a set bit is met. `MIPRE.Cost.Prog.decBody` and `MIPRE.Cost.Prog.decProg` compute the decrement of a nonzero binary number: a first phase, the loop of `decBody`, flips the leading $0$ bits to $1$, pushing them onto an accumulator, and the first $1$ bit to $0$; a second phase reverses the accumulator back onto the remaining bits with `revOntoProg`. The output is a bit string whose value is one less than that of the input.
--
--   `MIPRE.Cost.PolyTimeFun.next` is the polynomial-time function $\mathbb{N} \to \mathbb{N}$,
--   $$n \longmapsto 2n + 1,$$
--   which on binary encodings prepends a $1$ bit: its program is $\mathtt{cons}(\mathtt{const}(\mathtt{cons}(\mathtt{nil}, \mathtt{nil})), \mathtt{var}\ 0)$ and its time bound $X + 5$.
--
--   The lemmas proved in the bundle are the simp equations for the encodings of bits and bit strings (including $\mathrm{encode}(l) = \mathrm{list}(\mathrm{map}\ \mathrm{ofBool}\ l)$), the recursion equations of `bitsVal`, the encoding identity $\mathrm{encode}(2n + 1) = \mathtt{cons}(\mathtt{cons}(\mathtt{nil}, \mathtt{nil}), \mathrm{encode}\ n)$ on which `next` rests, and the application equation of `next`.
--
--   **Formalization Note**. Decrement may leave a non-canonical representation with trailing zero bits, which is why the specifications of these programs are stated in terms of the value `bitsVal` of a bit string rather than Mathlib's canonical `Nat.bits`. Every list walk is quadratic in this model, because the loop state is rebuilt at each iteration and the tail is copied, so the cost bounds have the form $(\text{iterations} + 1)(S + c)$ with $S$ dominating the sizes involved. The next level of the compression recursion is $2n + 1$ rather than the paper's $n + 1$: incrementing a binary numeral needs a carry propagation, whereas prepending a bit is a single node; the argument is unchanged, since the levels $n, 2n + 1, 4n + 3, \dots$ still grow without bound and $|2n + 1| = |n| + 1$ keeps every overhead polynomial in $|e| + |n|$.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Numeric.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Numeric.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary

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

@[simp] theorem Data.ofBool_false : Data.ofBool false = .nil := rfl

@[simp] theorem Data.ofBool_true : Data.ofBool true = .cons .nil .nil := rfl

@[simp] theorem encode_bool (b : Bool) : encode b = Data.ofBool b := rfl

@[simp] theorem encode_bitStr_nil : encode ([] : BitStr) = Data.nil := rfl

@[simp] theorem encode_bitStr_cons (b : Bool) (l : BitStr) :
    encode (b :: l) = Data.cons (Data.ofBool b) (encode l) := rfl

theorem encode_bitStr_eq_list (l : BitStr) : encode l = Data.list (l.map Data.ofBool) :=
  Data.ofList_eq_list _ _

/-- The value of a bit string (LSB first), canonical or not. -/
def bitsVal (l : BitStr) : ℕ := l.foldr Nat.bit 0

@[simp] theorem bitsVal_nil : bitsVal [] = 0 := rfl

@[simp] theorem bitsVal_cons (b : Bool) (l : BitStr) :
    bitsVal (b :: l) = Nat.bit b (bitsVal l) := rfl

namespace Prog

/-! ## Zero test -/

/-- Body of `isZeroProg`: walk the bits; stop with `nil` (zero) at the end, with
`cons nil nil` (nonzero) at the first `true` bit. -/
def isZeroBody : Prog :=
  .elim 0 (.cons .nil .nil)
    (.elim 0 (.cons (.cons .nil .nil) (.var 1)) (.cons .nil (.cons .nil .nil)))

/-- `isZeroProg` on a bit string computes `encode (l.any id)`: `nil` iff the value is zero. -/
def isZeroProg : Prog := .loop isZeroBody

/-! ## Decrement -/

/-- Body of the first phase of `decProg`: on state `cons bits acc`, a leading `false` bit
is turned into a `true` pushed on `acc`; at the first `true` bit the loop stops with the pair
`cons (false :: acc) rest`, which the second phase (`revOntoProg`) reverses onto `rest`. -/
def decBody : Prog :=
  .elim 0 .nil (.elim 0 (.cons .nil (.cons (.var 1) .nil))
    (.elim 0 (.cons (.cons .nil .nil) (.cons (.var 1) (.cons (.cons .nil .nil) (.var 3))))
      (.cons .nil (.cons (.cons .nil (.var 5)) (.var 3)))))

/-- `decProg` on the bits of a nonzero number computes the bits of its predecessor. -/
def decProg : Prog := .let_ (.cons (.var 0) .nil) (.let_ (.loop decBody) revOntoProg)

end Prog

/-! ## The next level index -/

theorem encode_two_mul_add_one (n : ℕ) :
    encode (2 * n + 1) = Data.cons (.cons .nil .nil) (encode n) := by
  have h : (2 * n + 1).bits = true :: n.bits := by
    rw [← Nat.bit_true_apply]
    exact Nat.bits_append_bit n true (fun _ => rfl)
  show encode (2 * n + 1).bits = _
  rw [h]
  rfl

/-- `n ↦ 2 n + 1` on binary numerals: prepend a `true` bit. This is the "next level"
map of the recursive compression argument (the paper's `n + 1` would need a carry
propagation; `2 n + 1` is one node). -/
noncomputable def PolyTimeFun.next : PolyTimeFun ℕ ℕ where
  toFun n := 2 * n + 1
  code := .cons (.const (.cons .nil .nil)) (.var 0)
  closed := ⟨trivial, Nat.zero_lt_one⟩
  timeBound := Polynomial.X + Polynomial.C 5
  computes n := by
    refine ⟨3 + (esize n + 1) + 1, ?_, ?_⟩
    · simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; omega
    · rw [encode_two_mul_add_one]
      exact Eval.cons (Eval.const _ _)
        (Eval.var_of_get (env := [encode n]) (i := 0) (v := encode n) (by simp))

@[simp] theorem PolyTimeFun.next_apply (n : ℕ) : PolyTimeFun.next n = 2 * n + 1 := rfl

end MIPRE.Cost


