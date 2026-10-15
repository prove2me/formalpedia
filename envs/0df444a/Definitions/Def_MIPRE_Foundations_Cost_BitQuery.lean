-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_BitQuery
-- name    : MIPRE_Foundations_Cost_BitQuery
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-12T16:06:24.152801+00:00
-- url     : https://prove2.me/theorems/265a5d2f-1f4e-4de1-8daa-f7f386061b28
-- title:
--   The bit-query answer and the bit-indexing program of succinct descriptions
-- statement:
--   This bundle defines the answer a succinct description must give to a bit query, and the program that computes it from an explicitly given string.
--
--   `MIPRE.Cost.bitQueryAnswer` $x\ m$, for a bit string $x \in \{0,1\}^*$ and an index $m \in \mathbb{N}$, is the encoding of the $m$-th bit of $x$ (indices from $0$) when $m < |x|$, and the out-of-range marker, the unary numeral $\mathrm{ofNat}(2)$, when $m \ge |x|$:
--   $$\mathrm{bitQueryAnswer}(x, m) = \begin{cases} \mathrm{encode}(x_m) & m < |x|,\\ \mathrm{ofNat}(2) & m \ge |x|.\end{cases}$$
--   This is the value $\varphi_e(m)$ that a succinct description $(e, n)$ of $x$ must return ([MNY, Definition 2.4]).
--
--   The cost accounting of the bit-indexing program is packaged in three functions of the bit length $L = |m|$ of the index: `MIPRE.Cost.Prog.zeroBound` $L = (L + 1)(4L + 9)$ bounds one zero test, `MIPRE.Cost.Prog.decBound` $L = (L + 2)(60L + 100)$ bounds one decrement, and `MIPRE.Cost.Prog.bitAtIter` $s_y\ L = s_y + 8L + \mathrm{zeroBound}(L) + \mathrm{decBound}(L) + 20$ bounds one iteration when the string has size at most $s_y$.
--
--   `MIPRE.Cost.Prog.bitAtBody` and `MIPRE.Cost.Prog.bitAtProg` $= \mathtt{loop}\ \mathrm{bitAtBody}$ act on the state $\mathtt{cons}(y, m)$, with $y$ an encoded bit string and $m$ an encoded binary index: the body stops with $\mathrm{ofNat}(2)$ if $y$ is exhausted; otherwise it tests $m$ for zero with `isZeroProg`, stopping with the head bit of $y$ if $m = 0$, and continuing with the tail of $y$ and the index $m - 1$ (computed by `decProg`) otherwise. Thus `bitAtProg` on $\mathtt{cons}(\mathrm{encode}\ y, \mathrm{encode}\ m)$ computes $\mathrm{bitQueryAnswer}(y, m)$, at a cost of at most $(|y| + 1)\cdot\mathrm{bitAtIter}(\mathrm{size}\ y, |m|)$.
--
--   The lemmas proved in the bundle are the three recursion equations of `bitQueryAnswer`: on the empty string every answer is the marker $\mathrm{ofNat}(2)$; on $b :: x$ the answer to the query $0$ is $\mathrm{encode}(b)$, and the answer to the query $m + 1$ is the answer to the query $m$ about $x$.
--
--   **Formalization Note**. The index is walked in binary: each zero test and each decrement copies the index, so one iteration costs $O(\mathrm{size}(y) + |m|^2)$ and the whole walk $O(|y|\cdot(\mathrm{size}(y) + |m|^2))$. This quadratic dependence on $|m|$ is the origin of the factor $(|m| + 1)^2$ in the succinctness time budget $(n + 1)(|m| + 1)^2$ of `IsSuccinctDesc`, which replaces the paper's bound of $n$ on every input (vacuous in a model that charges for reading its input). The marker for an out-of-range query is the unary numeral $2$, following [MNY], where $\varphi_e(m) = 2$ for $m \ge |x|$.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/BitQuery.lean; blueprint def:succinct

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/BitQuery.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric

/-!
# The bit-query program

`bitAtProg` on `(y, m)` — a bit string and a binary index — returns the `m`-th bit of `y`,
or the out-of-range marker `ofNat 2`: this is the answer a succinct description must give
([MNY, Definition 2.4]; `bitQueryAnswer`). It walks `y` while decrementing `m` in binary,
testing for zero at each step, so its cost is `(|y| + 1) · bitAtIter (size y) |m|` with
`bitAtIter` quadratic in `|m|` (each zero test and decrement copies the index). This is
where the `(|m| + 1) ^ 2` factor of the succinctness budget of `IsSuccinctDesc` comes from.
-/

namespace MIPRE.Cost

/-- The answer a succinct description must give to the bit-query `m` about the string
`x`: the `m`-th bit for `m < |x|`, and the out-of-range marker (the unary numeral `2`)
otherwise. -/
def bitQueryAnswer (x : BitStr) (m : ℕ) : Data :=
  if h : m < x.length then encode (x.get ⟨m, h⟩) else Data.ofNat 2

@[simp] theorem bitQueryAnswer_nil (m : ℕ) : bitQueryAnswer [] m = Data.ofNat 2 := by
  simp [bitQueryAnswer]

@[simp] theorem bitQueryAnswer_cons_zero (b : Bool) (x : BitStr) :
    bitQueryAnswer (b :: x) 0 = encode b := by
  simp [bitQueryAnswer]

@[simp] theorem bitQueryAnswer_cons_succ (b : Bool) (x : BitStr) (m : ℕ) :
    bitQueryAnswer (b :: x) (m + 1) = bitQueryAnswer x m := by
  unfold bitQueryAnswer
  by_cases h : m < x.length
  · have h' : m + 1 < (b :: x).length := by simp [h]
    rw [dif_pos h', dif_pos h]
    rfl
  · have h' : ¬ m + 1 < (b :: x).length := by simp [h]
    rw [dif_neg h', dif_neg h]

namespace Prog

/-- Cost of one zero test on a bit string of length `L`. -/
def zeroBound (L : ℕ) : ℕ := (L + 1) * (4 * L + 1 + 8)

/-- Cost of one decrement on a bit string of length `L`. -/
def decBound (L : ℕ) : ℕ := (L + 2) * (10 * (6 * L + 4) + 60)

/-- Cost of one iteration of `bitAtProg` with a string of size at most `sy` and an index of
`L` bits. -/
def bitAtIter (sy L : ℕ) : ℕ := sy + 8 * L + zeroBound L + decBound L + 20

/-- Body of `bitAtProg`: on state `cons y m`, stop with `ofNat 2` if `y` is exhausted; else
test `m` for zero: if zero, stop with the head bit of `y`; otherwise continue with the tail
of `y` and `m - 1`. -/
def bitAtBody : Prog :=
  .elim 0 .nil (.elim 0 (.cons .nil (.const (.ofNat 2)))
    (.let_ (callVar 3 isZeroProg)
      (.elim 0 (.cons .nil (.var 1))
        (.cons (.cons .nil .nil) (.cons (.var 4) (callVar 6 decProg))))))

/-- `bitAtProg` on `cons (encode y) (encode m)` computes `bitQueryAnswer y m`. -/
def bitAtProg : Prog := .loop bitAtBody

end Prog

end MIPRE.Cost


