-- Prove2me | Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
-- name    : MIPRE_Foundations_Repeat_MapLoop
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T14:38:02.790204+00:00
-- url     : https://prove2.me/theorems/278709fe-e1ed-4979-be25-82d1a7e0e829
-- title:
--   Definitions of MapLoop: The block loop of the repeated sampler The repeated sampler of `thm:parallel-repetition` answers a marginal, linear or…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Repeat.MapLoop` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The block loop of the repeated sampler. The repeated sampler of `thm:parallel-repetition` answers a marginal, linear or factor query on `𝔽₂^{k s}` by cutting the vectors of the query into `k` blocks of `s` coordinates, asking the input sampler about each block, and concatenating the answers (`planning/repetition-verifier.md`, R3(b)). This module is that loop: * `pairTakeProg` cuts the first `s` elements off two lists at once; * `mapBody` is the body of the loop, on the state `(s, remU, remY, ctx, acc)`: stop with `acc` once `remU` is exhausted, and otherwise cut a block off `remU` and `remY`,…
--
--   **Definitions** (9): `MIPRE.Cost.Prog.mapAcc` (The output of the loop from the pairs of blocks: the answers, each reversed, in reverse order, in front of `acc`.); `MIPRE.Cost.Prog.mapBody` (The body of the block loop, with `univ` the universal machine.); `MIPRE.Cost.Prog.mapCtx` (The context of the loop: the input sampler `S̄` and the fixed part `(n, kind, w, j)` of the query.); `MIPRE.Cost.Prog.mapIter` (The per-iteration budget of the loop, in a bound `Z` on the sizes in play.); `MIPRE.Cost.Prog.mapQuery` (The input of the universal machine for one block: `(S̄, (n, kind, w, j, blockU, blockY))`.); `MIPRE.Cost.Prog.mapState` (The state of the loop.); `MIPRE.Cost.Prog.mapStepCost` (The cost of one iteration, in the numeral `s`, the sizes `U, Y` of the remainders, `C` of the context, `A` of the accumulator, and the cost…); `MIPRE.Cost.Prog.pairTakeCost` (The cost of `pairTakeProg` on a numeral `s` and lists of sizes `U`, `Y`.); `MIPRE.Cost.Prog.pairTakeProg` (On `cons us (cons remU remY)` with `us` the unary numeral `s`: the pair of remainders and the pair of blocks, `cons remU' (cons remY' (cons…).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Repeat.MapLoop` (`MIPRE/Foundations/Repeat/MapLoop.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 14 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Repeat/MapLoop.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/MapLoop.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Theorems.Thm_MIPRE_Cost_Prog_revOntoProg_runs

/-!
# The block loop of the repeated sampler

The repeated sampler of `thm:parallel-repetition` answers a marginal, linear or factor query
on `𝔽₂^{k s}` by cutting the vectors of the query into `k` blocks of `s` coordinates, asking
the input sampler about each block, and concatenating the answers
(`planning/repetition-verifier.md`, R3(b)). This module is that loop:

* `pairTakeProg` cuts the first `s` elements off two lists at once;
* `mapBody` is the body of the loop, on the state `(s, remU, remY, ctx, acc)`: stop with `acc`
  once `remU` is exhausted, and otherwise cut a block off `remU` and `remY`, build the query
  `(n, kind, w, j, blockU, blockY)` from the context `ctx = (S̄, n, kind, w, j)`, run the input
  sampler `S̄` on it through the universal machine `univ`, and push the answer, reversed, onto
  `acc`;
* `mapLoop_runs` is the loop: its output is the reversed concatenation of the answers on the
  pairs of blocks `Data.chunkPairs`, in time `(|remU| + 1)` times a quadratic in a bound `Z`
  on the sizes in play and the cost `Tu` of one call.

The loop is uniform in the query kind: the blocks of an absent vector are empty, which is the
encoding of the empty bit string, so a marginal or factor query — whose last component is
empty — goes through the same code as a linear one. The answers are a parameter `f` of the
run lemma, known only on the pairs of blocks that occur: on well-formed queries they are the
input sampler's answers, on arbitrary ones whatever it halts with.
-/

namespace MIPRE.Cost

open Data

namespace Prog

/-! ## Cutting a block off two lists -/

/-- On `cons us (cons remU remY)` with `us` the unary numeral `s`: the pair of remainders and
the pair of blocks, `cons remU' (cons remY' (cons blockU blockY))`. -/
def pairTakeProg : Prog :=
  .elim 0 .nil
    (.elim 1 .nil
      (.let_ (.cons (.var 2) (.cons (.var 0) .nil))
        (.let_ (.loop takeBody)
          (.let_ (.cons (.var 4) (.cons (.var 3) .nil))
            (.let_ (.loop takeBody)
              (.elim 2 .nil
                (.elim 2 .nil
                  (.let_ (callVar 3 revProg)
                    (.let_ (callVar 2 revProg)
                      (.cons (.var 4) (.cons (.var 2) (.cons (.var 1) (.var 0)))))))))))))

/-- The cost of `pairTakeProg` on a numeral `s` and lists of sizes `U`, `Y`. -/
def pairTakeCost (s U Y : ℕ) : ℕ :=
  2 * ((s + 1) * (U + Y + 2 * s + 21)) + 2 * ((U + 2) * (U + Y + 13)) +
    2 * ((Y + 2) * (U + Y + 13)) + 4 * s + 8 * U + 8 * Y + 40

/-! ## The loop body -/

/-- The context of the loop: the input sampler `S̄` and the fixed part `(n, kind, w, j)` of the
query. -/
def mapCtx (sD nD kD wD jD : Data) : Data := .cons sD (.cons nD (.cons kD (.cons wD jD)))

/-- The input of the universal machine for one block: `(S̄, (n, kind, w, j, blockU, blockY))`. -/
def mapQuery (sD nD kD wD jD cU cY : Data) : Data :=
  .cons sD (.cons nD (.cons kD (.cons wD (.cons jD (.cons cU cY)))))

/-- The state of the loop. -/
def mapState (s : ℕ) (remU remY : List Data) (ctx : Data) (acc : List Data) : Data :=
  .cons (ofNat s) (.cons (list remU) (.cons (list remY) (.cons ctx (list acc))))

/-- The body of the block loop, with `univ` the universal machine. -/
def mapBody (univ : Prog) : Prog :=
  .elim 0 .nil
    (.elim 1 .nil
      (.elim 1 .nil
        (.elim 1 .nil
          (.elim 4 (.cons .nil (.var 1))
            (.let_ (.cons (.var 8) (.cons (.var 6) (.var 4)))
              (.let_ (callVar 0 pairTakeProg)
                (.elim 0 .nil
                  (.elim 1 .nil
                    (.elim 1 .nil
                      (.elim 10 .nil
                        (.elim 1 .nil
                          (.elim 1 .nil
                            (.elim 1 .nil
                              (.let_ (.cons (.var 6) (.cons (.var 4) (.cons (.var 2)
                                  (.cons (.var 0) (.cons (.var 1) (.cons (.var 8) (.var 9)))))))
                                (.let_ (callVar 0 univ)
                                  (.let_ (.cons (.var 0) (.var 21))
                                    (.let_ (callVar 0 revOntoProg)
                                      (.cons (.cons .nil .nil)
                                        (.cons (.var 28) (.cons (.var 16) (.cons (.var 14)
                                          (.cons (.var 22) (.var 0)))))))))))))))))))))))

/-- The cost of one iteration, in the numeral `s`, the sizes `U, Y` of the remainders, `C` of
the context, `A` of the accumulator, and the cost `Tu` of the call. -/
def mapStepCost (s U Y C A Tu : ℕ) : ℕ :=
  pairTakeCost s U Y + (Tu + 1) * (Tu + A + 12) + 6 * s + 6 * U + 6 * Y + 3 * C + 3 * A +
    4 * Tu + 70

/-- The output of the loop from the pairs of blocks: the answers, each reversed, in reverse
order, in front of `acc`. -/
def mapAcc (f : List Data → List Data → Data) (pairs : List (List Data × List Data))
    (acc : List Data) : List Data :=
  (pairs.map fun p => (toList (f p.1 p.2)).reverse).reverse.flatten ++ acc

/-- The per-iteration budget of the loop, in a bound `Z` on the sizes in play. -/
def mapIter (Z : ℕ) : ℕ := 22 * (Z + 30) ^ 2

end Prog

end MIPRE.Cost


