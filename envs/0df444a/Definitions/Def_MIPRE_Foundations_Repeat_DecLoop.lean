-- Prove2me | Definitions.Def_MIPRE_Foundations_Repeat_DecLoop
-- name    : MIPRE_Foundations_Repeat_DecLoop
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T14:38:31.649969+00:00
-- url     : https://prove2.me/theorems/50f1bf58-f47f-43ab-8e08-0b88cbfc1d1e
-- title:
--   Definitions of DecLoop: The coordinate loop of the repeated decider The repeated decider of `thm:parallel-repetition` runs the input decider…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Repeat.DecLoop` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The coordinate loop of the repeated decider. The repeated decider of `thm:parallel-repetition` runs the input decider `D̄` on each of the `k` coordinates of its input (`planning/repetition-verifier.md`, R3(c)). This module is that loop, on the state `(k, remX, remY, remA, remB, ctx)` — `k` a unary counter, `remX, remY` the questions still to be cut into blocks of `s`, `remA, remB` the answers still to be checked, `ctx = (D̄, n, s, B)`: * `preProg` cuts a block off `remX` and `remY`, checks that the current answers are bit strings of length at most `B` (`okBits`), and returns the query `(D̄,…
--
--   **Definitions** (14): `MIPRE.Cost.Prog.DecAcc` (**Acceptance of the coordinate loop**: `k` answers on each side, each a bit string of length at most `B`, and the input decider, through…); `MIPRE.Cost.Prog.coordBody` (The body of the coordinate loop: on the exhausted counter, `finalProg`; otherwise the step on the decremented state.); `MIPRE.Cost.Prog.coordIter` (The per-iteration budget of the loop, in a bound `Z` on the sizes and the cost `Tu` of a call.); `MIPRE.Cost.Prog.decCtx` (The context of the loop: the input decider `D̄`, the index `n`, and `s`, `B` in unary.); `MIPRE.Cost.Prog.decQueries` (The potential queries of the loop, in order: one per coordinate while answers remain.); `MIPRE.Cost.Prog.decQuery` (The query to the universal machine on one coordinate: `(D̄, (n, x_i, y_i, a_i, b_i))`.); `MIPRE.Cost.Prog.decState` (The state of the loop.); `MIPRE.Cost.Prog.finalProg` (On the exhausted counter: accept iff no answer is left over.); `MIPRE.Cost.Prog.okBits` (`d` is the encoding of a bit string of length at most `B`: the walk `bitWalk` against the unary budget `B` ends with the string exhausted.); `MIPRE.Cost.Prog.preCost` (The cost of `preProg` at `s`, `B`, on remainders of sizes `U, Y`, answer lists of sizes `A, Bs`, a context of size `C` and a counter of…); `MIPRE.Cost.Prog.preProg` (Before the call: cut a block off `remX` and `remY`, check the current answers, and return the query with the next state — or `nil`.); and -20 more.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Repeat.DecLoop` (`MIPRE/Foundations/Repeat/DecLoop.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 22 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Repeat/DecLoop.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DecLoop.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
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
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_Eval_of_append_of_wellScoped

/-!
# The coordinate loop of the repeated decider

The repeated decider of `thm:parallel-repetition` runs the input decider `D̄` on each of the
`k` coordinates of its input (`planning/repetition-verifier.md`, R3(c)). This module is that
loop, on the state `(k, remX, remY, remA, remB, ctx)` — `k` a unary counter, `remX, remY` the
questions still to be cut into blocks of `s`, `remA, remB` the answers still to be checked,
`ctx = (D̄, n, s, B)`:

* `preProg` cuts a block off `remX` and `remY`, checks that the current answers are bit
  strings of length at most `B` (`okBits`), and returns the query `(D̄, (n, x_i, y_i, a_i, b_i))`
  for the universal machine with the next state, or `nil` when a check fails;
* `stepProg` runs the query through `univ` and continues when the answer is `1`;
* `finalProg` accepts, once the counter is exhausted, when no answer is left over;
* `coordBody` is the body of the loop.

Two readings of the loop are proved: a forward one, `decLoop_of_acc` — the loop accepts when
every coordinate passes (`DecAcc`) — and an *inversion*, `decLoop_inv` — the loop accepts
only then, obtained from `stepProg_inv` by determinism of the semantics. The inversion is
what the game equivalence of the repeated verifier needs, since the input decider may not
halt on inputs it does not accept. A third, `decLoop_runs_bounded`, is the forward reading
with costs, against an oracle for the answers of `univ`, for the time bound.
-/

namespace MIPRE.Cost

open Data

namespace Prog

/-! ## Bit strings of bounded length -/

/-- `d` is the encoding of a bit string of length at most `B`: the walk `bitWalk` against the
unary budget `B` ends with the string exhausted. -/
def okBits (B : ℕ) (d : Data) : Bool :=
  match bitWalk d (ofNat B) with
  | .cons .nil _ => true
  | _ => false

/-! ## The state and the programs -/

/-- The context of the loop: the input decider `D̄`, the index `n`, and `s`, `B` in unary. -/
def decCtx (dD nD : Data) (s B : ℕ) : Data := .cons dD (.cons nD (.cons (ofNat s) (ofNat B)))

/-- The query to the universal machine on one coordinate: `(D̄, (n, x_i, y_i, a_i, b_i))`. -/
def decQuery (dD nD xi yi ai bi : Data) : Data :=
  .cons dD (.cons nD (.cons xi (.cons yi (.cons ai bi))))

/-- The state of the loop. -/
def decState (uk : Data) (remX remY remA remB : List Data) (ctx : Data) : Data :=
  .cons uk (.cons (list remX) (.cons (list remY) (.cons (list remA) (.cons (list remB) ctx))))

/-- On the exhausted counter: accept iff no answer is left over. -/
def finalProg : Prog :=
  .elim 0 .nil
    (.elim 1 .nil
      (.elim 1 .nil
        (.elim 0
          (.elim 1 .nil (.elim 0 (.cons .nil (.cons .nil .nil)) (.cons .nil .nil)))
          (.cons .nil .nil))))

/-- Before the call: cut a block off `remX` and `remY`, check the current answers, and return
the query with the next state — or `nil`. -/
def preProg : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 1 .nil (.elim 1 .nil (.elim 1 .nil
    (.elim 2 .nil (.elim 2 .nil
      (.elim 5 .nil (.elim 1 .nil (.elim 1 .nil
        (.let_ (.cons (.var 0) (.cons (.var 16) (.var 14)))
          (.let_ (callVar 0 pairTakeProg)
            (.let_ (.cons (.var 10) (.var 3))
              (.let_ (callVar 0 bitWalkProg)
                (.elim 0 .nil
                  (.elim 0
                    (.let_ (.cons (.var 12) (.var 7))
                      (.let_ (callVar 0 bitWalkProg)
                        (.elim 0 .nil
                          (.elim 0
                            (.elim 8 .nil (.elim 1 .nil (.elim 1 .nil
                              (.cons (.cons (.var 20) (.cons (.var 18) (.cons (.var 0)
                                  (.cons (.var 1) (.cons (.var 24) (.var 22))))))
                                (.cons (.var 34) (.cons (.var 4) (.cons (.var 2)
                                  (.cons (.var 25) (.cons (.var 23) (.var 27))))))))))
                            .nil))))
                    .nil)))))))))))))))

/-- The cost of `preProg` at `s`, `B`, on remainders of sizes `U, Y`, answer lists of sizes
`A, Bs`, a context of size `C` and a counter of size `K`. -/
def preCost (s B U Y A Bs C K : ℕ) : ℕ :=
  pairTakeCost s U Y + (B + 1) * (A + (2 * B + 1) + 21) + (B + 1) * (Bs + (2 * B + 1) + 21) +
    8 * (U + Y + A + Bs + C + K) + 8 * s + 8 * B + 120

/-- The result of `preProg` on a state with answers `ai, bi` at hand. -/
def preResult (dD nD : Data) (s B : ℕ) (uk : Data) (remX remY : List Data) (ai bi : Data)
    (remA remB : List Data) : Data :=
  if okBits B ai && okBits B bi then
    .cons (decQuery dD nD (list (remX.take s)) (list (remY.take s)) ai bi)
      (decState uk (remX.drop s) (remY.drop s) remA remB (decCtx dD nD s B))
  else .nil

/-! ## The step: the call to the input decider -/

/-- One coordinate: `preProg`, then the query through `univ`, continuing when the answer is
`1` (`cons nil nil`), stopping with `0` otherwise. -/
def stepProg (univ : Prog) : Prog :=
  .let_ (callVar 0 preProg)
    (.elim 0 (.cons .nil .nil)
      (.let_ (callVar 0 univ)
        (.elim 0 (.cons .nil .nil)
          (.elim 0 (.elim 1 (.cons (.cons .nil .nil) (.var 4)) (.cons .nil .nil))
            (.cons .nil .nil)))))

/-- The result of the step from the answer `r` of `univ`: continue with `st'` on `1`. -/
def stepResult (st' r : Data) : Data :=
  if r = .cons .nil .nil then .cons (.cons .nil .nil) st' else .cons .nil .nil

/-! ## The body -/

/-- The body of the coordinate loop: on the exhausted counter, `finalProg`; otherwise the
step on the decremented state. -/
def coordBody (univ : Prog) : Prog :=
  .elim 0 .nil
    (.elim 0 (callVar 1 finalProg)
      (.let_ (.cons (.var 1) (.var 3)) (callVar 0 (stepProg univ))))

/-! ## The loop -/

/-- **Acceptance of the coordinate loop**: `k` answers on each side, each a bit string of
length at most `B`, and the input decider, through `univ`, answering `1` on every
coordinate. -/
def DecAcc (univ : Prog) (dD nD : Data) (s B : ℕ) :
    ℕ → List Data → List Data → List Data → List Data → Prop
  | 0, _, _, remA, remB => remA = [] ∧ remB = []
  | k + 1, remX, remY, ai :: remA', bi :: remB' =>
      okBits B ai = true ∧ okBits B bi = true ∧
      (∃ t, Eval [decQuery dD nD (list (remX.take s)) (list (remY.take s)) ai bi] univ
        (.cons .nil .nil) t) ∧
      DecAcc univ dD nD s B k (remX.drop s) (remY.drop s) remA' remB'
  | _ + 1, _, _, [], _ => False
  | _ + 1, _, _, _ :: _, [] => False

/-! ## The loop with costs -/

/-- The potential queries of the loop, in order: one per coordinate while answers remain. -/
def decQueries (dD nD : Data) (s : ℕ) :
    ℕ → List Data → List Data → List Data → List Data → List Data
  | 0, _, _, _, _ => []
  | k + 1, remX, remY, ai :: remA', bi :: remB' =>
      decQuery dD nD (list (remX.take s)) (list (remY.take s)) ai bi ::
        decQueries dD nD s k (remX.drop s) (remY.drop s) remA' remB'
  | _ + 1, _, _, [], _ => []
  | _ + 1, _, _, _ :: _, [] => []

/-- The per-iteration budget of the loop, in a bound `Z` on the sizes and the cost `Tu` of a
call. -/
def coordIter (Z Tu : ℕ) : ℕ := 40 * (Z + 30) ^ 2 + Tu

end Prog

end MIPRE.Cost


