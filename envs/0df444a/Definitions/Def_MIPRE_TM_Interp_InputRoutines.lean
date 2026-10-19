-- Prove2me | Definitions.Def_MIPRE_TM_Interp_InputRoutines
-- name    : MIPRE_TM_Interp_InputRoutines
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:01:24.447219+00:00
-- url     : https://prove2.me/theorems/fda2837b-20ac-40dd-aad9-34087c25c406
-- title:
--   Definitions of InputRoutines: The input-tape routines `copyUnary`, `copyInputBits`, `checkLen` and `buildAnswer` read an input tape from its head to…
-- statement:
--   The definitions of the module `MIPRE.TM.Interp.InputRoutines` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The input-tape routines. `copyUnary`, `copyInputBits`, `checkLen` and `buildAnswer` read an input tape from its head to the blank after the input, writing on a work tape; their specifications are by induction on the remaining suffix of the input.
--
--   **Definitions** (3): `MIPRE.TM.Interp.WEff` (The effect of writing `l` at the head of `t` (as in `CopyTree.lean`).); `MIPRE.TM.Interp.answerBits` (The written form of an answer suffix: `S(encode (l.map boolOf))`.); `MIPRE.TM.Interp.boolOf` (The bit of an input symbol.).
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.Interp.InputRoutines` (`MIPRE/TM/Interp/InputRoutines.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 19 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/InputRoutines.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/InputRoutines.lean (definition bundle: declarations the uploaded statements rest on);
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
# The input-tape routines

`copyUnary`, `copyInputBits`, `checkLen` and `buildAnswer` read an input tape from its
head to the blank after the input, writing on a work tape; their specifications are by
induction on the remaining suffix of the input.
-/

namespace MIPRE.TM.Interp

open Turing MultiInputTM Phase MIPRE.Cost
open MultiTapeTM (moveInputPos)

variable {input : Fin 7 → List Sym}

/-- The effect of writing `l` at the head of `t` (as in `CopyTree.lean`). -/
structure WEff (t : WT) (c c' : Cfg input) (l : List Sym) : Prop where
  holds : Holds (c'.workTapes t) (c.workTapePos t) l
  outside : ∀ q, (q < c.workTapePos t ∨ c.workTapePos t + l.length ≤ q) →
    c'.workTapes t q = c.workTapes t q
  pos : c'.workTapePos t = c.workTapePos t + l.length

/-! ## `copyUnary` -/

/-! ## `copyInputBits` -/

/-! ## `checkLen` -/

/-! ## `buildAnswer` -/

/-- The bit of an input symbol. -/
def boolOf : Sym → Bool
  | .one => true
  | _ => false

/-- The written form of an answer suffix: `S(encode (l.map boolOf))`. -/
def answerBits (l : List Sym) : List Sym := S (Data.ofList Data.ofBool (l.map boolOf))

end MIPRE.TM.Interp


