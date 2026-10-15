-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Succinct
-- name    : MIPRE_Foundations_Cost_Succinct
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-12T16:07:47.215039+00:00
-- url     : https://prove2.me/theorems/bbf05bfc-106f-4c8c-8fb5-2281c4be68a5
-- title:
--   Succinct descriptions and the bit-query program of the compression argument
-- statement:
--   This bundle defines succinct descriptions, the central notion of the recursive compression method, and the bit-query program that produces them.
--
--   `MIPRE.Cost.IsSuccinctDesc` $c\ n\ x$ says that the pair $(c, n)$ of a program $c$ and a natural number $n$ *succinctly describes* the bit string $x \in \{0,1\}^*$:
--
--   1. $c$ is closed (well scoped at length $1$);
--   2. $|x| \le 2^n$;
--   3. for every index $m \in \mathbb{N}$, presented in binary, $c$ on the input $\mathrm{encode}(m)$ halts with the answer $\mathrm{bitQueryAnswer}(x, m)$ (the $m$-th bit of $x$, or the marker $2$ for $m \ge |x|$) at some cost $t \le (n + 1)(|m| + 1)^2$, where $|m|$ is the binary length of $m$ (`Nat.size m`).
--
--   In symbols, the third condition reads
--   $$\forall m \in \mathbb{N}\ \ \exists t \le (n + 1)\,(|m| + 1)^2 :\quad c \text{ on } \mathrm{encode}(m) \text{ halts with } \mathrm{bitQueryAnswer}(x, m) \text{ at cost } t .$$
--
--   The pair $(c, n)$ is exponentially smaller than $x$ itself; a compression procedure's guarantees are required only on genuine succinct descriptions, but it must run, in polynomial time, on all inputs.
--
--   `MIPRE.Cost.Prog.bitQueryProg` $\mathrm{univ}$ is the *bit-query program* $\beta$ of the recursive compression argument, relative to a universal program $\mathrm{univ}$: on the input $\mathrm{encode}(((c', e), n), m)$ it runs $\mathrm{univ}$ on $\mathtt{cons}(\mathrm{encode}\ c', \mathrm{encode}(e, n))$, that is, it simulates the program $c'$ on the input $(e, n)$ to obtain a string $y$ which is given only implicitly as the output of $c'$, and then answers the bit query $m$ about $y$ with `bitAtProg`. Hardcoding the triple $((c', e), n)$ into it through `hardcode` yields a succinct description of that output whenever the simulated run is fast enough for the budget. `MIPRE.Cost.bitQueryBound` $U$, for a universal machine $U$ with overhead polynomial $p_U$, is the polynomial
--   $$p_U(X + 1) + (X + 1)(X + 534) + 2X + 29$$
--   bounding the cost of the bit-query program per factor $(|m| + 1)^2$, as a function of $X = \mathrm{esize}(c') + \mathrm{esize}(e) + \mathrm{esize}(n) + t$ with $t$ the cost of the run of $c'$.
--
--   No lemma is proved inside this bundle; the correctness of the bit-query program (`bitQueryProg_runs`) and the succinctness of its hardcoded instances (`isSuccinctDesc_hardcode`) are stated separately.
--
--   **Formalization Note**. [MNY, Definition 2.4] requires the runtime of $c$ on $m$ to be at most $n$ for *all* $m$; in a cost model that charges for reading its input, as this one does, that bound is vacuous for $|m| > n$, and the formalization requires $(n + 1)(|m| + 1)^2$ instead. Any polynomial in $n$ and $|m|$ would serve, provided the same bound is used in the compression theorem for games, whose output verifiers are what get succinctly described; the quadratic factor is exactly what the bit-indexing program `bitAtProg` achieves, because each zero test and decrement of the binary index copies it. The indices $m$ enter in binary, under the `SizedEncoding ℕ` instance, and the paper's Turing machine $e$ is a closed program of the ambient model.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Succinct.lean; blueprint def:succinct; [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Definition 2.4

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Succinct.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit

/-!
# Succinct descriptions and the bit-query program

`IsSuccinctDesc c n x` is [MNY, Definition 2.4] (blueprint `def:succinct`), with the time
bound adapted to the ambient model (see the module docstring of
`MIPRE.Foundations.Compression`). The **bit-query program** `bitQueryProg univ` of the
recursive compression argument answers bit-queries about a string that is only given
*implicitly*, as the output of a program `c'` on an input `(e, n)`: on
`encode (((c', e), n), m)` it simulates `c'` on `encode (e, n)` through the universal machine
and indexes the result with `bitAtProg`. Its correctness is conditional on the run of `c'`
(`bitQueryProg_runs`), and hardcoding `((c', e), n)` into it gives a succinct description of
that output whenever the run is fast enough for the budget (`isSuccinctDesc_hardcode`).
-/

namespace MIPRE.Cost

open Polynomial

/-! ## Succinct descriptions ([MNY, Definition 2.4]; blueprint `def:succinct`) -/

/-- `(c, n)` **succinctly describes** the bit string `x`: `c` is a closed program, `x` has
length at most `2 ^ n`, and `c` answers every bit-query `m` (presented in binary; the
answer is `bitQueryAnswer x m`) within cost `(n + 1) * (|m| + 1) ^ 2`.

[MNY, Definition 2.4], with the time bound adapted as discussed in the module docstring of
`MIPRE.Foundations.Compression`. The pair `(c, n)` is exponentially smaller than `x` itself;
a compression procedure's guarantees are only required on genuine succinct descriptions,
but it must *run* (in polynomial time) on all inputs. -/
def IsSuccinctDesc (c : Prog) (n : ℕ) (x : BitStr) : Prop :=
  c.WellScoped 1 ∧ x.length ≤ 2 ^ n ∧
    ∀ m : ℕ, ∃ t ≤ (n + 1) * (Nat.size m + 1) ^ 2, c.Runs (encode m) (bitQueryAnswer x m) t

namespace Prog

/-- The bit-query program: on `encode (((c', e), n), m)`, run `univ` on
`cons (encode c') (encode (e, n))` to obtain the string `y`, then answer the bit-query `m`
about `y` with `bitAtProg`. -/
def bitQueryProg (univ : Prog) : Prog :=
  .elim 0 .nil (.elim 0 .nil (.elim 0 .nil
    (.let_ (.cons (.var 0) (.cons (.var 1) (.var 3)))
      (.let_ (callVar 0 univ)
        (.let_ (.cons (.var 0) (.var 7))
          (callVar 0 bitAtProg))))))

end Prog

/-- The cost of the bit-query program, as a polynomial in
`s = esize c' + esize e + esize n + t` (with `t` the cost of the run of `c'`), per
`(|m| + 1) ^ 2`. -/
noncomputable def bitQueryBound (U : UniversalMachine) : Polynomial ℕ :=
  U.bound.comp (X + C 1) + (X + C 1) * (X + C 534) + C 2 * X + C 29

end MIPRE.Cost


