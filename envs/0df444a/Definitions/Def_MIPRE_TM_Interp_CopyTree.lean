-- Prove2me | Definitions.Def_MIPRE_TM_Interp_CopyTree
-- name    : MIPRE_TM_Interp_CopyTree
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:01:25.744978+00:00
-- url     : https://prove2.me/theorems/6aba0a94-5c9a-496c-bf08-bbef593a6ddb
-- title:
--   Definitions of CopyTree: The `copyTree` routine Copying (or skipping) a preorder-serialized value: a scan with a unary counter of the pending…
-- statement:
--   The definitions of the module `MIPRE.TM.Interp.CopyTree` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The `copyTree` routine. Copying (or skipping) a preorder-serialized value: a scan with a unary counter of the pending subtrees on `CNT`, one more per `1` (a node with two children, itself consumed) and one fewer per `0` (a leaf), finishing when none is pending. The scan from `d ≥ 1` pending subtrees over `S(v)` leaves `d - 1` pending (`copyTree_scan`), finishing when `d = 1`; the instruction starts with one (`exec_copyTree`).
--
--   **Definitions** (2): `MIPRE.TM.Interp.DstEff` (The effect of writing `l` at the head of `t`: `l` held from the old head, the rest of the tape kept, the head past `l`.); `MIPRE.TM.Interp.scanExit` (The control at `(k, pc, p1)` if `d ≠ 1`, else at the next instruction.).
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.Interp.CopyTree` (`MIPRE/TM/Interp/CopyTree.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 19 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/CopyTree.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/CopyTree.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# The `copyTree` routine

Copying (or skipping) a preorder-serialized value: a scan with a unary counter of the
pending subtrees on `CNT`, one more per `1` (a node with two children, itself consumed) and
one fewer per `0` (a leaf), finishing when none is pending. The scan from `d ≥ 1` pending
subtrees over `S(v)` leaves `d - 1` pending (`copyTree_scan`), finishing when `d = 1`; the
instruction starts with one (`exec_copyTree`).
-/

namespace MIPRE.TM.Interp

open Turing MultiInputTM Phase MIPRE.Cost

variable {input : Fin 7 → List Sym}

/-- The control at `(k, pc, p1)` if `d ≠ 1`, else at the next instruction. -/
def scanExit (k : ProgId) (pc : Fin maxPc) (hpc : pc.val + 1 < maxPc) (d : ℕ) : Option Ctl :=
  if d = 1 then next_ k pc hpc else some ⟨k, pc, p1⟩

/-- The effect of writing `l` at the head of `t`: `l` held from the old head, the rest of
the tape kept, the head past `l`. -/
structure DstEff (t : WT) (c c' : Cfg input) (l : List Sym) : Prop where
  holds : Holds (c'.workTapes t) (c.workTapePos t) l
  outside : ∀ q, (q < c.workTapePos t ∨ c.workTapePos t + l.length ≤ q) →
    c'.workTapes t q = c.workTapes t q
  pos : c'.workTapePos t = c.workTapePos t + l.length

end MIPRE.TM.Interp


