-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_Params
-- name    : MIPRE_TM_CookLevin_Params
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:07:49.344528+00:00
-- url     : https://prove2.me/theorems/85bacaff-e2ad-43d4-b52b-2d5e72ba69e9
-- title:
--   Definitions of Params: The parameters of the describer: the check circuit and the tableau length Two constants and one choice
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.Params` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The parameters of the describer: the check circuit and the tableau length. Two constants and one choice. * `chk` is the check circuit of the interpreter machine: the truth-table circuit (`Fml.table`) of its local check predicate `checkPred U 1`, of `winCard 7 6 Sym Ctl` inputs and at most `7 · 2 ^ winCard` gates — an enormous constant, exactly as the paper's `lem:pack-check-size`, and formally harmless. `chk_isCheckCircuit` is the hypothesis of `lem:correct-tableau`; `Gc` is its gate count. * `eOf T σ = 5 (⌈log T⌉ + ⌈log σ⌉) + 24` is the exponent of the tableau length: under the validity…
--
--   **Definitions** (4): `MIPRE.TM.CookLevin.Desc.Gc` (The number of gates of the check circuit.); `MIPRE.TM.CookLevin.Desc.chk` (**The check circuit of the interpreter machine**: a truth-table circuit of `chkFun`, taken from `Fml.exists_circuit`.); `MIPRE.TM.CookLevin.Desc.chkFun` (The local check predicate of the interpreter machine as a Boolean function of the window bits, in the canonical order.); `MIPRE.TM.CookLevin.Desc.eOf` (The exponent of the tableau length: `5 (⌈log T⌉ + ⌈log σ⌉) + 24`.).
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.Params` (`MIPRE/TM/CookLevin/Params.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 50 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Params.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Params.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPRE_SAT_Fml_exists_circuit

/-!
# The parameters of the describer: the check circuit and the tableau length

Two constants and one choice.

* `chk` is the check circuit of the interpreter machine: the truth-table circuit
  (`Fml.table`) of its local check predicate `checkPred U 1`, of `winCard 7 6 Sym Ctl` inputs
  and at most `7 · 2 ^ winCard` gates — an enormous constant, exactly as the paper's
  `lem:pack-check-size`, and formally harmless. `chk_isCheckCircuit` is the hypothesis of
  `lem:correct-tableau`; `Gc` is its gate count.
* `eOf T σ = 5 (⌈log T⌉ + ⌈log σ⌉) + 24` is the exponent of the tableau length: under the
  validity hypotheses and `|a|, |b| ≤ T`, the accepting run of `U` is shorter than
  `2 ^ eOf T σ` (`runBound_le_two_pow`), so the tableau of `Sof (eOf T σ)` steps is long
  enough. The bound comes from an explicit fifth-power majorant of `runBound`
  (`runBound_le`) (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost

/-! ## The check circuit -/

open Classical in
/-- The local check predicate of the interpreter machine as a Boolean function of the window
bits, in the canonical order. -/
noncomputable def chkFun (x : Fin (winCard 7 6 Sym Ctl) → Bool) : Bool :=
  decide (checkPred U Sym.one fun wv => x (Fintype.equivFin _ wv))

/-- **The check circuit of the interpreter machine**: a truth-table circuit of `chkFun`,
taken from `Fml.exists_circuit`. It is never unfolded: its defining term mentions
`Fintype.card (WinVar 7 6 Sym Ctl)`, whose evaluation does not terminate in practice. -/
noncomputable def chk : Circuit := (Fml.exists_circuit (winCard 7 6 Sym Ctl) chkFun).choose

/-- The number of gates of the check circuit. -/
noncomputable def Gc : ℕ := chk.gates.length

/-! ## The tableau length -/

section RunBound

variable (D : Prog) (n T Q σ : ℕ) (x y a b : BitStr)

end RunBound

/-- The exponent of the tableau length: `5 (⌈log T⌉ + ⌈log σ⌉) + 24`. -/
def eOf (T σ : ℕ) : ℕ := 5 * Nat.size T + 5 * Nat.size σ + 24

end MIPRE.TM.CookLevin.Desc


