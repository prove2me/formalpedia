-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_Correct
-- name    : MIPRE_TM_CookLevin_Correct
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:00:57.632237+00:00
-- url     : https://prove2.me/theorems/5d2644a5-d52f-4acd-8ad7-02cc496d5bcf
-- title:
--   Definitions of Correct: Correctness of the Cook–Levin tableau The tableau formula of `S` steps of a machine `M` (`tableau`) is satisfiable,…
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.Correct` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Correctness of the Cook–Levin tableau. The tableau formula of `S` steps of a machine `M` (`tableau`) is satisfiable, with the fixed input tapes holding their strings, iff `M` accepts some completion of the free input tapes within `S` steps (`planning/succinct-cook-levin.md`, S1; `answer_reduction.tex` `lem:correct-tableau`). Acceptance is `AcceptsIn`: halted at time `S` with output string exactly `[acc]`. * **Completeness** (`tableau_sat_of_acceptsIn`): the assignment of an accepting run (`runAssign`) satisfies every clause; the window clauses because the windows of a run are locally…
--
--   **Definitions** (1): `MIPRE.TM.CookLevin.AcceptsIn` (Acceptance within `S` steps: halted at time `S`, having output exactly `[acc]`.).
--
--   **Embedded lemmas** (8): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `lit_eval_false`, `lit_eval_true`, `runAssign_cell`, `runAssign_emitBad`, `runAssign_emitOne`, `runAssign_emitted`, `runAssign_head`, `runAssign_state`.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.Correct` (`MIPRE/TM/CookLevin/Correct.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 11 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Correct.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Correct.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_CookLevin_Semantics

/-!
# Correctness of the Cook–Levin tableau

The tableau formula of `S` steps of a machine `M` (`tableau`) is satisfiable, with the fixed
input tapes holding their strings, iff `M` accepts some completion of the free input tapes
within `S` steps (`planning/succinct-cook-levin.md`, S1; `answer_reduction.tex`
`lem:correct-tableau`). Acceptance is `AcceptsIn`: halted at time `S` with output string
exactly `[acc]`.

* **Completeness** (`tableau_sat_of_acceptsIn`): the assignment of an accepting run
  (`runAssign`) satisfies every clause; the window clauses because the windows of a run are
  locally consistent (`locallyConsistent_localCfgOf`) and the check circuit computes local
  consistency, its specification being the hypothesis `hchk`.
* **Soundness** (`acceptsIn_of_tableau_sat`): a satisfying assignment determines the free
  input strings from its time-`0` rows, and its rows encode the configurations of the run on
  those inputs, by induction on time: at each step the window clauses force, through the
  check circuit, local consistency of every window, and a locally consistent window whose
  time-`t` part is that of a configuration has the time-`t + 1` part of its successor
  (`post_of_pre`). The acceptance row and the emission bookkeeping then give acceptance.

Both directions use the head bounds `headsIn_cfgAt`: along a run, a head moves at most one
cell per step, so at every time `t ≤ S` every head is on an interior cell of the tableau.
-/

namespace MIPRE.TM.CookLevin

open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos)

section

variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}

/-- Acceptance within `S` steps: halted at time `S`, having output exactly `[acc]`. -/
def AcceptsIn (input : Fin i → List Symbol) (S : ℕ) : Prop :=
  (M.configs (M.initCfg input) S).state = none ∧ M.outputString (M.initCfg input) S = [acc]

/-! ## Head bounds along a run -/

/-! ## The output string of an accepting run -/

/-! ## The assignment of a run, by variable -/

variable (chk : Circuit)

@[simp] theorem runAssign_cell (t : Fin (S + 1)) (d : Tape i w) (p : Pos S) (v : CellVal Symbol) :
    runAssign M acc (input := input) chk (.cell t d p v) =
      baseAssign M acc (input := input) chk.gates.length (.cell t d p v) := rfl

@[simp] theorem runAssign_head (t : Fin (S + 1)) (d : Tape i w) (p : Pos S) :
    runAssign M acc (input := input) chk (.head t d p) =
      baseAssign M acc (input := input) chk.gates.length (.head t d p) := rfl

@[simp] theorem runAssign_state (t : Fin (S + 1)) (q : Option State) :
    runAssign M acc (input := input) chk (.state t q) =
      baseAssign M acc (input := input) chk.gates.length (.state t q) := rfl

@[simp] theorem runAssign_emitOne (t : Fin S) :
    runAssign M acc (input := input) chk (.emitOne t) =
      baseAssign M acc (input := input) chk.gates.length (.emitOne t) := rfl

@[simp] theorem runAssign_emitBad (t : Fin S) :
    runAssign M acc (input := input) chk (.emitBad t) =
      baseAssign M acc (input := input) chk.gates.length (.emitBad t) := rfl

@[simp] theorem runAssign_emitted (t : Fin (S + 1)) :
    runAssign M acc (input := input) chk (.emitted t) =
      baseAssign M acc (input := input) chk.gates.length (.emitted t) := rfl

/-! ## Clause evaluation -/

variable {G : ℕ}

omit [Fintype Symbol] [Fintype State] [DecidableEq Symbol] [DecidableEq State] in
@[simp] theorem lit_eval_true (f : TabVar i w Symbol State S G → Bool) (v) :
    (Lit.eval f ⟨v, true⟩) = f v := rfl

omit [Fintype Symbol] [Fintype State] [DecidableEq Symbol] [DecidableEq State] in
@[simp] theorem lit_eval_false (f : TabVar i w Symbol State S G → Bool) (v) :
    (Lit.eval f ⟨v, false⟩) = !f v := rfl

/-! ## Cells -/

/-! ## Completeness: the window clauses -/

/-! ## Completeness: the other clauses -/

variable (s₀ s₁ : Symbol) (fixed : Fin i → Option (List Symbol))

end

end MIPRE.TM.CookLevin


