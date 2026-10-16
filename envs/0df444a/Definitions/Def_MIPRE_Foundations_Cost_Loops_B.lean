-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Loops_B
-- name    : MIPRE_Foundations_Cost_Loops_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:21:00.400733+00:00
-- url     : https://prove2.me/theorems/f4e29a9a-d8be-4818-9844-3b76d6209f22
-- title:
--   List reversal in the ambient model: the program `revProg` and its run (loops addendum)
-- statement:
--   This bundle adds five declarations to the already published bundle `MIPRE_Foundations_Cost_Loops`, the loop part of the closure library of the ambient cost model, where lists are `cons`-chains (`Data.list`) and every program is closed with its input in variable $0$. The one definition kept is the reversal program $\mathrm{revProg} = \mathrm{let\_}\,(\mathrm{cons}\,(\mathrm{var}\,0)\,\mathrm{nil})\,\mathrm{revOntoProg}$: it pairs the input list with an empty accumulator and runs the loop `revOntoProg`, which on $\mathrm{cons}\,xs\,acc$ computes $\mathrm{reverse}\,xs \mathbin{+\!\!+} acc$. The embedded theorems are that the loop body `revOntoBody`, the loop `revOntoProg` and `revProg` are well scoped at one variable (`WellScoped 1`, that is, closed programs), and the run of `revProg`: for every list $l$ of data,
--
--   $$\exists\, t \le (|l| + 2)\cdot\big(\mathrm{size}(\mathrm{list}\,l) + 13\big),\qquad \mathrm{revProg}.\mathrm{Runs}\,(\mathrm{list}\,l)\,(\mathrm{list}\,(\mathrm{reverse}\,l))\,t,$$
--
--   where $|l|$ is the length of $l$ and $\mathrm{size}$ the number of nodes of a datum. Reversal is one of the list primitives the semidecider and the interpreter programs are built from.
--
--   **Formalization Note** The cost bound is stated as `(l.length + 1 + 1) * ((Data.list l).size + 1 + 12)`, in the library's convention of bounds of the form (iterations + 1) · (S + c) with S dominating the sizes involved. `Prog.Runs x r t` is the evaluation relation `Eval [x] p r t` from the one-element environment; the existential over `t` gives a run of some cost under the bound, not an exact cost. `revProg` is a `def` of type `Prog`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Loops.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Loops.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Cost_Loops does not carry);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Theorems.Thm_MIPRE_Cost_Prog_revOntoProg_runs

/-!
# The closure library, part II: loops

The generic reasoning principle for `loop` (`Eval.loop_of_invariant`: an invariant, a
strictly decreasing measure and a uniform bound on the body's cost give a run of the loop
with cost `≤ (μ + 1) · (B + 1)`), and the list and unary-numeral primitives of the library
proved by direct induction: reversal onto an accumulator (`revOntoProg`, `revProg`) and
length in unary (`lenProg`). Lists are `cons`-chains (`Data.list`); unary numerals are lists
of `nil`s (`Data.ofNat`).

Conventions: every program is closed and takes its input in variable `0`; a loop's state
is the input itself or a pair assembled by `let_` in front of the loop; the body stops with
`cons nil result` and continues with `cons (cons nil nil) state'`. Costs are stated as
bounds of the form `(iterations + 1) · (S + c)` where `S` is any number dominating the sizes
involved, so that the bound is one atom for `omega` throughout an induction.
-/

namespace MIPRE.Cost

/-! ## Lists as data -/

namespace Data

end Data

/-! ## The loop principle -/

namespace Eval

end Eval

/-! ## Reversal onto an accumulator -/

namespace Prog

theorem revOntoBody_wellScoped : revOntoBody.WellScoped 1 := by
  simp [revOntoBody, WellScoped]

theorem revOntoProg_wellScoped : revOntoProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, revOntoBody_wellScoped⟩

/-- Reversal of a list: `revProg` on `xs` computes `reverse xs`. -/
def revProg : Prog := .let_ (.cons (.var 0) .nil) revOntoProg

theorem revProg_wellScoped : revProg.WellScoped 1 :=
  ⟨⟨Nat.zero_lt_one, trivial⟩, revOntoProg_wellScoped.mono (by omega) _⟩

theorem revProg_runs (l : List Data) :
    ∃ t ≤ (l.length + 1 + 1) * ((Data.list l).size + 1 + 12),
      revProg.Runs (.list l) (.list l.reverse) t := by
  obtain ⟨t, ht, hrun⟩ := revOntoProg_runs l [] [Data.list l] ((Data.list l).size + 1)
    (by simp)
  refine ⟨(Data.list l).size + 1 + 1 + 1 + t + 1, ?_, ?_⟩
  · have h2 : (l.length + 1 + 1) * ((Data.list l).size + 1 + 12) =
        (l.length + 1) * ((Data.list l).size + 1 + 12) + ((Data.list l).size + 1 + 12) :=
      Nat.succ_mul _ _
    omega
  · have hpre := Eval.cons (Eval.var_of_get (env := [Data.list l]) (i := 0) (v := .list l)
      (by simp)) (Eval.nil [Data.list l])
    have hrun' : Eval (Data.cons (.list l) .nil :: [Data.list l]) revOntoProg
        (.list l.reverse) t := by simpa using hrun
    exact Eval.let_ hpre hrun'

/-! ## Length in unary -/

end Prog

end MIPRE.Cost


