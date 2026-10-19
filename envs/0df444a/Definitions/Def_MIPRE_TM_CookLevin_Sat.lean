-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_Sat
-- name    : MIPRE_TM_CookLevin_Sat
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:06:14.933786+00:00
-- url     : https://prove2.me/theorems/81b48193-d89d-4132-ae78-382984e2e243
-- title:
--   Definitions of Sat: The described formula and the answers The two halves of item 1 of `thm:succinct-sat` for the describer: a satisfying…
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.Sat` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The described formula and the answers. The two halves of item 1 of `thm:succinct-sat` for the describer: a satisfying assignment of the described formula extending the two answer blocks exists iff the blocks are the two-bit tape encodings (`tapeBits`) of strings of length at most `T` that the decider accepts within `T` (`planning/succinct-cook-levin.md`, S3). The bridge in both directions is the decoding: an assignment of the formula gives the tableau assignment `w ∘ idxOf` (`sat_tableau_of_sat_formula3`), and an assignment of the tableau gives the formula assignment `decodeVar · |>.elim…
--
--   **Definitions** (2): `MIPRE.TM.CookLevin.Desc.boolsOf` (The bit string of a list of symbols over `{0, 1}`.); `MIPRE.TM.CookLevin.Desc.wOf` (The assignment of the described formula read off a tableau assignment through the decoding.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `length_bits`, `length_boolsOf`.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.Sat` (`MIPRE/TM/CookLevin/Sat.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 57 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Sat.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Sat.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_TM_CookLevin_Index
import Definitions.Def_MIPRE_TM_CookLevin_Describer
import Definitions.Def_MIPRE_TM_CookLevin_Semantics
import Definitions.Def_MIPRE_TM_CookLevin_Correct
import Definitions.Def_MIPRE_TM_CookLevin_Sound

/-!
# The described formula and the answers

The two halves of item 1 of `thm:succinct-sat` for the describer: a satisfying assignment of
the described formula extending the two answer blocks exists iff the blocks are the two-bit
tape encodings (`tapeBits`) of strings of length at most `T` that the decider accepts within
`T` (`planning/succinct-cook-levin.md`, S3).

The bridge in both directions is the decoding: an assignment of the formula gives the tableau
assignment `w ∘ idxOf` (`sat_tableau_of_sat_formula3`), and an assignment of the tableau gives
the formula assignment `decodeVar · |>.elim false` (`sat_formula3_of_sat_tableau`). The answer
blocks match because the canonical index of an answer cell is its answer index (`idxOf_ans`)
and because a time-`0` row of a free tape reads exactly the tape encoding of the string it
holds (`decide_val_inputCellVal`).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Fml

/-! ## The two-bit tape encoding on a time-`0` row -/

@[simp] theorem length_bits (l : BitStr) : (bits l).length = l.length := List.length_map _

/-- The bit string of a list of symbols over `{0, 1}`. -/
def boolsOf (s : List Sym) : BitStr := s.map fun c => decide (c = Sym.one)

@[simp] theorem length_boolsOf (s : List Sym) : (boolsOf s).length = s.length := List.length_map _

/-! ## The two bridges -/

section Bridge

variable (e T : ℕ) (D : Prog) (n : ℕ) (x y : BitStr)

/-- The assignment of the described formula read off a tableau assignment through the
decoding. -/
noncomputable def wOf (A : TabVar 7 6 Sym Ctl (Sof e) Gc → Bool) (i : Fin (2 ^ mOf e Gc)) : Bool :=
  (decodeVar e Gc (fieldsOf e Gc T (bitsOfNat (mOf e Gc) (i : ℕ)))).elim false A

end Bridge

/-! ## The input tapes of the machine -/

/-! ## Item 1 of the theorem -/

section Main

variable (𝒟 : Decider) (n T : ℕ) (x y : BitStr) (e : ℕ)

end Main

end MIPRE.TM.CookLevin.Desc


