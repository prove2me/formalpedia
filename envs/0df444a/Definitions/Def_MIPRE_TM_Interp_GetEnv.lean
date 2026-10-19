-- Prove2me | Definitions.Def_MIPRE_TM_Interp_GetEnv
-- name    : MIPRE_TM_Interp_GetEnv
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:02:45.64029+00:00
-- url     : https://prove2.me/theorems/c555bf53-82cb-48c5-80d7-88bd8a226673
-- title:
--   Definitions of GetEnv: The `getEnv` routine With the unary index `S(ofNat i)` under the head of `C` and the environment `envRepr env` on `E`…
-- statement:
--   The definitions of the module `MIPRE.TM.Interp.GetEnv` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The `getEnv` routine. With the unary index `S(ofNat i)` under the head of `C` and the environment `envRepr env` on `E` with its head at the end, `getEnv` writes `S(env.get i)` at the head of `X`: it walks left over `i` separators (phases `p1`–`p3`), then to the start of the element (`p4`), copies it (`p5`) and returns the head of `E` to the end (`p8`); past the start of the environment the index is out of range, the rest of it is consumed (`p6`, `p7`) and `nil` is written (`p9`). The proof is by induction on the index, over the suffix of the environment not yet passed.
--
--   **Definitions** (1): `MIPRE.TM.Interp.EnvTape` (A tape holding the environment from `0`, blank before.).
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.Interp.GetEnv` (`MIPRE/TM/Interp/GetEnv.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 20 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/GetEnv.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/GetEnv.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# The `getEnv` routine

With the unary index `S(ofNat i)` under the head of `C` and the environment `envRepr env` on
`E` with its head at the end, `getEnv` writes `S(env.get i)` at the head of `X`: it walks
left over `i` separators (phases `p1`–`p3`), then to the start of the element (`p4`), copies
it (`p5`) and returns the head of `E` to the end (`p8`); past the start of the environment
the index is out of range, the rest of it is consumed (`p6`, `p7`) and `nil` is written
(`p9`). The proof is by induction on the index, over the suffix of the environment not yet
passed.
-/

namespace MIPRE.TM.Interp

open Turing MultiInputTM Phase MIPRE.Cost

variable {input : Fin 7 → List Sym}

/-- A tape holding the environment from `0`, blank before. -/
structure EnvTape (τ : Tape) (env : Env) : Prop where
  holds : Holds τ 0 (envRepr env)
  before : BlankBefore τ 0
  beyond : BlankBeyond τ (envRepr env).length

/-! ## The scans -/

/-! ## The walk -/

end MIPRE.TM.Interp


