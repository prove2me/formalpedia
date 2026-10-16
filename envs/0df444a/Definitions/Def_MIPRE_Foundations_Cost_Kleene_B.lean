-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
-- name    : MIPRE_Foundations_Cost_Kleene_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:23:55.924863+00:00
-- url     : https://prove2.me/theorems/03d14e52-686d-4c8b-9b5d-22b43ae84649
-- title:
--   Inverting a variable call: a run of `callVar i q` is a run of `q` (Kleene addendum)
-- statement:
--   This bundle adds one theorem, and no new definitions, to the already published bundle `MIPRE_Foundations_Cost_Kleene`, the efficient Kleene recursion theorem of the ambient cost model (blueprint `lem:kleene`, [MNY, Lemma 2.3]). In the closure library, $\mathrm{callVar}\,i\,q = \mathrm{let\_}\,(\mathrm{var}\,i)\,q$ calls the closed program $q$ on the value of variable $i$ of the current environment. The added lemma is the backward direction of this call: for every environment $env$, index $i$, program $q$ that is well scoped at one variable (`WellScoped 1`), result $r$ and cost $t$,
--
--   $$\mathrm{Eval}\ env\ (\mathrm{callVar}\,i\,q)\ r\ t \;\Longrightarrow\; \exists\, t' \le t,\quad q.\mathrm{Runs}\,(env.\mathrm{get}\,i)\,r\,t'.$$
--
--   It is the lemma that lets the fixed-point construction read a run of the two-argument program $G$ back as a run of the program it calls, which is how the time transfer of the fixed point is bounded by that of its image.
--
--   **Formalization Note** The statement is `callVar_runs_rev {env : Env} {i : ℕ} {q : Prog} (hq : q.WellScoped 1) {r : Data} {t : ℕ} (h : Eval env (callVar i q) r t) : ∃ t' ≤ t, q.Runs (env.get i) r t'`. `Prog.Runs x r t` is `Eval [x] q r t`, evaluation from the one-element environment, and `Env.get` reads the environment with `nil` beyond its end; the well-scopedness hypothesis is what allows the environment to be cut down to that one element.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Kleene.lean; [MNY, Lemma 2.3]

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Kleene.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Cost_Kleene does not carry);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Theorems.Thm_MIPRE_Cost_Eval_of_append_of_wellScoped

/-!
# Efficient Kleene recursion

The efficient fixed-point theorem `efficient_fixed_point` (blueprint `lem:kleene`;
[MNY, Lemma 2.3]), by the classical construction: for a polynomial-time map `F` on
programs, let `G` be the program that on `cons x v` (with `x` the description of a program
`x'`) computes `s(x', x') = hardcode x' (encode x')`, applies `F` to it, and runs the result
on `v` through the universal machine; the fixed point is `e = hardcode G (encode G)`, since
`e` on `v` is `G` on `cons (encode G) v`, which runs `F (hardcode G (encode G)) = F e` on
`v`. The time transfer is the universal machine's, plus the fixed cost of computing `F e`
and a copy of the input.
-/

namespace MIPRE.Cost

open Polynomial

namespace Prog

/-- Inverting a call: a run of `callVar i q` is a run of the closed `q` on the value of
variable `i`. -/
theorem callVar_runs_rev {env : Env} {i : ℕ} {q : Prog} (hq : q.WellScoped 1) {r : Data}
    {t : ℕ} (h : Eval env (callVar i q) r t) : ∃ t' ≤ t, q.Runs (env.get i) r t' := by
  change Eval env (.let_ (.var i) q) r t at h
  cases h with
  | let_ h₁ h₂ =>
    cases h₁
    exact ⟨_, by omega,
      Eval.of_append_of_wellScoped (env := [env.get i]) (extra := env) h₂ hq⟩

end Prog

/-! ## The fixed point, as data

The construction is exposed (`kleeneFix`) with its overhead spelled out (`kleeneFix_runs_of`),
because the polynomial-time halting reduction (`planning/polytime-halting.md`) needs the overhead
of the fixed point of a *family* `F_M` of maps to be bounded uniformly in `M`: the existential
polynomial of `efficient_fixed_point` below depends on `F`, and only the explicit form shows how. -/

/-! ## The fixed-point theorem (blueprint `lem:kleene`; [MNY, Lemma 2.3]) -/

end MIPRE.Cost


