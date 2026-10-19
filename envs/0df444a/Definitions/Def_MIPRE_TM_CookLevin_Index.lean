-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_Index
-- name    : MIPRE_TM_CookLevin_Index
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:56:25.204703+00:00
-- url     : https://prove2.me/theorems/6f508d7f-25fa-4ab4-9b23-e35323b57e76
-- title:
--   Definitions of Index: The canonical index of a tableau variable `idxOf e G T v` is the index of the variable `v` in the described 3SAT…
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.Index` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The canonical index of a tableau variable. `idxOf e G T v` is the index of the variable `v` in the described 3SAT formula: the *answer index* `j < 4T` for a cell of one of the two free tapes inside the answer block — tape `5` for `j < 2T` and tape `6` otherwise, position `r / 2 + 3` for `r = j mod 2T`, the value `1` for `r` odd and the blank for `r` even — and the structured index (`encodeVar`) for every other variable. So the first `4T` variables of the formula are exactly the two answer blocks, which is what item 1 of `thm:succinct-sat` needs, and `decodeVar_fieldsOf_idxOf` says that…
--
--   **Definitions** (7): `MIPRE.TM.CookLevin.Desc.IsAnsCell` (The cell is an *answer cell*: at time `0` on a free tape, inside the answer block, holding `1` or the blank.); `MIPRE.TM.CookLevin.Desc.ansIdx` (The answer index of an answer cell.); `MIPRE.TM.CookLevin.Desc.idxOf` (The canonical index of a tableau variable: the answer index for an answer cell, the structured index (`encodeVar`) otherwise.); `MIPRE.TM.CookLevin.Desc.instDecidableIsAnsCell`; `MIPRE.TM.CookLevin.Desc.rOf` (The offset of an answer index inside its block.); `MIPRE.TM.CookLevin.Desc.tapeIdx` (The tape code of an answer index: `5` for the first block, `6` for the second.); `MIPRE.TM.CookLevin.Desc.valOf` (The cell value of an answer index: `1` for an odd offset, the blank for an even one.).
--
--   **Embedded lemmas** (5): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `ansIdx_lt`, `bitsVal_encodeVar_lt`, `flag_lt_m`, `four_T_le_flag`, `idxOf_lt`.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.Index` (`MIPRE/TM/CookLevin/Index.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 52 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Index.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Index.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Language
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_CookLevin_Layout
import Definitions.Def_MIPRE_TM_CookLevin_FieldFml
import Definitions.Def_MIPRE_TM_CookLevin_Kinds
import Definitions.Def_MIPRE_TM_CookLevin_Families
import Definitions.Def_MIPRE_TM_CookLevin_Window
import Definitions.Def_MIPRE_TM_CookLevin_FamilyFml
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Reach
import Definitions.Def_MIPRE_TM_Interp_Routines
import Definitions.Def_MIPRE_TM_Interp_Repr
import Definitions.Def_MIPRE_TM_Interp_CopyTree
import Definitions.Def_MIPRE_TM_Interp_GetEnv
import Definitions.Def_MIPRE_TM_Interp_Desc
import Definitions.Def_MIPRE_TM_Interp_Step
import Definitions.Def_MIPRE_TM_Interp_InputRoutines
import Definitions.Def_MIPRE_TM_Interp_Run
import Definitions.Def_MIPRE_Foundations_SAT_Table
import Definitions.Def_MIPRE_TM_CookLevin_Params
import Definitions.Def_MIPRE_TM_CookLevin_AnsEnd
import Theorems.Thm_MIPRE_SAT_bitsVal_lt
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_length_encodeVar

/-!
# The canonical index of a tableau variable

`idxOf e G T v` is the index of the variable `v` in the described 3SAT formula: the *answer
index* `j < 4T` for a cell of one of the two free tapes inside the answer block — tape `5`
for `j < 2T` and tape `6` otherwise, position `r / 2 + 3` for `r = j mod 2T`, the value `1`
for `r` odd and the blank for `r` even — and the structured index (`encodeVar`) for every
other variable. So the first `4T` variables of the formula are exactly the two answer blocks,
which is what item 1 of `thm:succinct-sat` needs, and `decodeVar_fieldsOf_idxOf` says that
decoding the canonical index returns the variable. `decodeVar_ans` is the other half: every
index below `4T` decodes to the answer variable it stands for
(`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost

/-! ## Reading an index built from a number -/

/-! ## The answer variables -/

variable (e G T : ℕ)

/-- The offset of an answer index inside its block. -/
def rOf (j : ℕ) : ℕ := if j < 2 * T then j else j - 2 * T

/-- The tape code of an answer index: `5` for the first block, `6` for the second. -/
def tapeIdx (j : ℕ) : ℕ := if j < 2 * T then 5 else 6

/-- The cell value of an answer index: `1` for an odd offset, the blank for an even one. -/
def valOf (j : ℕ) : CellVal Sym := if rOf T j % 2 = 1 then .sym .one else .blank

/-- `4T` fits below the flag bit. -/
theorem four_T_le_flag (hT : T ≤ Sof e) : 4 * T ≤ 2 ^ flagOff e G := by
  have h1 : (4 : ℕ) * 2 ^ e = 2 ^ (e + 2) := by rw [pow_add]; ring
  have h2 : (2 : ℕ) ^ (e + 2) ≤ 2 ^ flagOff e G :=
    Nat.pow_le_pow_right (by omega) (by unfold flagOff W; omega)
  have h3 : 4 * T ≤ 4 * 2 ^ e := by
    have : T ≤ 2 ^ e := by rw [Sof] at hT; exact hT
    omega
  omega

theorem flag_lt_m : flagOff e G < mOf e G := by unfold flagOff mOf; omega

/-! ## The canonical index -/

/-- The cell is an *answer cell*: at time `0` on a free tape, inside the answer block, holding
`1` or the blank. -/
def IsAnsCell (T : ℕ) (t : Fin (Sof e + 1)) (d : Tape 7 6) (p : Pos (Sof e)) (v : CellVal Sym) :
    Prop :=
  (t : ℕ) = 0 ∧ (tapeCode d = 5 ∨ tapeCode d = 6) ∧ 3 ≤ (p : ℕ) ∧ (p : ℕ) - 3 < T ∧
    (v = .blank ∨ v = .sym .one)

instance (T : ℕ) (t : Fin (Sof e + 1)) (d : Tape 7 6) (p : Pos (Sof e)) (v : CellVal Sym) :
    Decidable (IsAnsCell e T t d p v) := by unfold IsAnsCell; infer_instance

/-- The answer index of an answer cell. -/
def ansIdx (T : ℕ) (d : Tape 7 6) (p : Pos (Sof e)) (v : CellVal Sym) : ℕ :=
  (if tapeCode d = 5 then 0 else 2 * T) + 2 * ((p : ℕ) - 3) + (if v = .sym .one then 1 else 0)

/-- The canonical index of a tableau variable: the answer index for an answer cell, the
structured index (`encodeVar`) otherwise. -/
noncomputable def idxOf : TabVar 7 6 Sym Ctl (Sof e) G → ℕ
  | .cell t d p v =>
      if IsAnsCell e T t d p v then ansIdx e T d p v else bitsVal (encodeVar e G (.cell t d p v))
  | .head t d p => bitsVal (encodeVar e G (.head t d p))
  | .state t q => bitsVal (encodeVar e G (.state t q))
  | .emitOne t => bitsVal (encodeVar e G (.emitOne t))
  | .emitBad t => bitsVal (encodeVar e G (.emitBad t))
  | .emitted t => bitsVal (encodeVar e G (.emitted t))
  | .aux t js g => bitsVal (encodeVar e G (.aux t js g))

theorem bitsVal_encodeVar_lt (v : TabVar 7 6 Sym Ctl (Sof e) G) :
    bitsVal (encodeVar e G v) < 2 ^ mOf e G := by
  have := bitsVal_lt (encodeVar e G v)
  rwa [length_encodeVar] at this

theorem ansIdx_lt (hT : T ≤ Sof e) {t : Fin (Sof e + 1)} {d : Tape 7 6} {p : Pos (Sof e)}
    {v : CellVal Sym} (h : IsAnsCell e T t d p v) : ansIdx e T d p v < 4 * T := by
  obtain ⟨-, -, -, hpT, -⟩ := h
  unfold ansIdx
  split_ifs <;> omega

theorem idxOf_lt (hT : T ≤ Sof e) (v : TabVar 7 6 Sym Ctl (Sof e) G) :
    idxOf e G T v < 2 ^ mOf e G := by
  have hfl := four_T_le_flag e G T hT
  have h2 : (2 : ℕ) ^ flagOff e G < 2 ^ mOf e G :=
    Nat.pow_lt_pow_right (by omega) (flag_lt_m e G)
  cases v with
  | cell t d p v =>
    rw [idxOf]
    split_ifs with h
    · have := ansIdx_lt e T hT h
      omega
    · exact bitsVal_encodeVar_lt e G _
  | head t d p => exact bitsVal_encodeVar_lt e G _
  | state t q => exact bitsVal_encodeVar_lt e G _
  | emitOne t => exact bitsVal_encodeVar_lt e G _
  | emitBad t => exact bitsVal_encodeVar_lt e G _
  | emitted t => exact bitsVal_encodeVar_lt e G _
  | aux t js g => exact bitsVal_encodeVar_lt e G _

end MIPRE.TM.CookLevin.Desc


