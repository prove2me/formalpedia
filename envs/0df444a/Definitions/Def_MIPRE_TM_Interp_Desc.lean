-- Prove2me | Definitions.Def_MIPRE_TM_Interp_Desc
-- name    : MIPRE_TM_Interp_Desc
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:03:41.451107+00:00
-- url     : https://prove2.me/theorems/646d67b7-e4bb-447d-8586-3b2a7ec0b768
-- title:
--   Definitions of Desc: Tape descriptions A work tape is described by the list it holds from cell `0` (blank elsewhere) and its head position;…
-- statement:
--   The definitions of the module `MIPRE.TM.Interp.Desc` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Tape descriptions. A work tape is described by the list it holds from cell `0` (blank elsewhere) and its head position; a configuration by its control and the six descriptions (`Desc`). Every routine becomes a transformation of descriptions (`D_write`, `D_copyTree`, …), so that the correctness of a step of the evaluation machine is a chain of such transformations followed by list algebra (`overwrite`).
--
--   **Definitions** (4): `MIPRE.TM.Interp.Desc` (The configuration `c` has control `q` and its work tapes are as described by `ds`.); `MIPRE.TM.Interp.TapeIs` (The tape `τ` with head `pos` is as described by `s`.); `MIPRE.TM.Interp.TapeSt` (A tape holding exactly `l` from cell `0`, its head at cell `p`.); `MIPRE.TM.Interp.overwrite` (Writing `w` over `l` from position `p` (no gap: `p ≤ l.length`).).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `overwrite_cons_succ`, `overwrite_zero`.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.Interp.Desc` (`MIPRE/TM/Interp/Desc.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 21 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/Desc.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Desc.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Language
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Reach
import Definitions.Def_MIPRE_TM_Interp_Routines
import Definitions.Def_MIPRE_TM_Interp_Repr
import Definitions.Def_MIPRE_TM_Interp_CopyTree
import Definitions.Def_MIPRE_TM_Interp_GetEnv

/-!
# Tape descriptions

A work tape is described by the list it holds from cell `0` (blank elsewhere) and its head
position; a configuration by its control and the six descriptions (`Desc`). Every routine
becomes a transformation of descriptions (`D_write`, `D_copyTree`, …), so that the
correctness of a step of the evaluation machine is a chain of such transformations followed
by list algebra (`overwrite`).
-/

namespace MIPRE.TM.Interp

open Turing MultiInputTM Phase MIPRE.Cost

variable {input : Fin 7 → List Sym}

/-! ## One tape -/

/-- A tape holding exactly `l` from cell `0`, its head at cell `p`. -/
@[ext] structure TapeSt where
  l : List Sym
  p : ℕ

/-- The tape `τ` with head `pos` is as described by `s`. -/
def TapeIs (τ : Tape) (pos : ℤ) (s : TapeSt) : Prop :=
  Holds τ 0 s.l ∧ (∀ q : ℤ, q < 0 → τ q = none) ∧ (∀ q : ℤ, (s.l.length : ℤ) ≤ q → τ q = none) ∧
    pos = s.p

/-- Writing `w` over `l` from position `p` (no gap: `p ≤ l.length`). -/
def overwrite (l : List Sym) (p : ℕ) (w : List Sym) : List Sym :=
  l.take p ++ w ++ l.drop (p + w.length)

@[simp] theorem overwrite_zero (l w : List Sym) : overwrite l 0 w = w ++ l.drop w.length := by
  simp [overwrite]

@[simp] theorem overwrite_cons_succ (a : Sym) (l : List Sym) (p : ℕ) (w : List Sym) :
    overwrite (a :: l) (p + 1) w = a :: overwrite l p w := by
  simp only [overwrite, List.take_succ_cons, List.cons_append, List.cons.injEq, true_and]
  rw [show p + 1 + w.length = (p + w.length) + 1 by omega, List.drop_succ_cons]

namespace TapeIs

variable {τ : Tape} {pos : ℤ} {s : TapeSt}

end TapeIs

/-! ## A configuration -/

/-- The configuration `c` has control `q` and its work tapes are as described by `ds`. -/
def Desc (c : Cfg input) (q : Option Ctl) (ds : WT → TapeSt) : Prop :=
  c.state = q ∧ ∀ t, TapeIs (c.workTapes t) (c.workTapePos t) (ds t)

namespace Desc

variable {c : Cfg input} {q : Option Ctl} {ds : WT → TapeSt}

end Desc

/-! ## The routines on descriptions -/

section Routines

variable {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt}

end Routines

end MIPRE.TM.Interp


