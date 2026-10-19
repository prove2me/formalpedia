-- Prove2me | Definitions.Def_MIPRE_TM_Interp_Run
-- name    : MIPRE_TM_Interp_Run
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:06:49.4608+00:00
-- url     : https://prove2.me/theorems/b4e35b6b-1255-4263-a2c8-272cb9d7cecb
-- title:
--   Definitions of Run: The run of the interpreter The inputs of `U` (`uInput`), the initialization (`init_run`), the simulation of a run of…
-- statement:
--   The definitions of the module `MIPRE.TM.Interp.Run` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The run of the interpreter. The inputs of `U` (`uInput`), the initialization (`init_run`), the simulation of a run of the evaluation machine (`sim_run`), and the acceptance theorem: on the inputs `(𝒟, n, T, x, y, a, b)` with `|a|, |b| ≤ T`, `U` accepts (halts having output `1`) iff `𝒟` accepts `(n, x, y, a, b)` within cost `T`, and then within an explicit polynomial number of steps.
--
--   **Definitions** (9): `MIPRE.TM.Interp.InPos` (The input heads are at the positions `f`.); `MIPRE.TM.Interp.V0` (The size bound on the machine's values along the run.); `MIPRE.TM.Interp.Z0` (The size bound on the representations along the run.); `MIPRE.TM.Interp.initBound` (The bound on the steps of the initialization.); `MIPRE.TM.Interp.runBound` (The bound on the accepting run of `U`.); `MIPRE.TM.Interp.stepB` (The bound on the steps of `U` for one step of the machine, from representations of size at most `Z` with a scratch tape of length at most…); `MIPRE.TM.Interp.szBound` (A bound on `sz` from `CfgBound V L P K`.); `MIPRE.TM.Interp.uInput` (The seven inputs of `U`: the program, `n`, the budget `T` in unary, `x`, `y` as the bits of their encodings, and the answers `a`, `b` as…); `MIPRE.TM.Interp.vSize` (The value of the encoded input.).
--
--   **Embedded lemmas** (49): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `A_ne_B`, `A_ne_N`, `A_ne_PROG`, `A_ne_T`, `A_ne_XS`, `A_ne_YS`, `B_ne_A`, `B_ne_N`, `B_ne_PROG`, `B_ne_T`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.Interp.Run` (`MIPRE/TM/Interp/Run.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 34 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/Run.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Run.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_TM_Interp_Desc
import Definitions.Def_MIPRE_TM_Interp_Step
import Definitions.Def_MIPRE_TM_Interp_InputRoutines
import Theorems.Thm_MIPRE_Cost_Machine_eval_of_steps
import Theorems.Thm_MIPRE_Cost_Machine_eval_steps_bound
import Theorems.Thm_MIPRE_Cost_Machine_eval_steps_count

/-!
# The run of the interpreter

The inputs of `U` (`uInput`), the initialization (`init_run`), the simulation of a run of the
evaluation machine (`sim_run`), and the acceptance theorem: on the inputs
`(𝒟, n, T, x, y, a, b)` with `|a|, |b| ≤ T`, `U` accepts (halts having output `1`) iff `𝒟`
accepts `(n, x, y, a, b)` within cost `T`, and then within an explicit polynomial number of
steps.
-/

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false

namespace MIPRE.TM.Interp

open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)

/-! ## The inputs -/

/-- The seven inputs of `U`: the program, `n`, the budget `T` in unary, `x`, `y` as the bits
of their encodings, and the answers `a`, `b` as raw bit strings. -/
def uInput (D : Prog) (n Tb : ℕ) (x y a b : BitStr) : Fin 7 → List Sym :=
  ![S D.toData, S (encode n), List.replicate Tb .one, S (encode x), S (encode y), bits a, bits b]

@[simp] theorem uInput_PROG (D n Tb x y a b) : uInput D n Tb x y a b PROG = S D.toData := rfl
@[simp] theorem uInput_N (D n Tb x y a b) : uInput D n Tb x y a b N = S (encode n) := rfl
@[simp] theorem uInput_T (D n Tb x y a b) : uInput D n Tb x y a b T = List.replicate Tb .one := rfl
@[simp] theorem uInput_XS (D n Tb x y a b) : uInput D n Tb x y a b XS = S (encode x) := rfl
@[simp] theorem uInput_YS (D n Tb x y a b) : uInput D n Tb x y a b YS = S (encode y) := rfl
@[simp] theorem uInput_A (D n Tb x y a b) : uInput D n Tb x y a b A = bits a := rfl
@[simp] theorem uInput_B (D n Tb x y a b) : uInput D n Tb x y a b B = bits b := rfl

/-! ## Input heads -/

variable {input : Fin 7 → List Sym}

/-- The input heads are at the positions `f`. -/
def InPos (c : Cfg input) (f : IT → ℕ) : Prop := ∀ j, (c.inputPos j : ℕ) = f j

section Names

@[simp] theorem PROG_ne_N : PROG ≠ N := by decide
@[simp] theorem PROG_ne_T : PROG ≠ T := by decide
@[simp] theorem PROG_ne_XS : PROG ≠ XS := by decide
@[simp] theorem PROG_ne_YS : PROG ≠ YS := by decide
@[simp] theorem PROG_ne_A : PROG ≠ A := by decide
@[simp] theorem PROG_ne_B : PROG ≠ B := by decide
@[simp] theorem N_ne_PROG : N ≠ PROG := by decide
@[simp] theorem N_ne_T : N ≠ T := by decide
@[simp] theorem N_ne_XS : N ≠ XS := by decide
@[simp] theorem N_ne_YS : N ≠ YS := by decide
@[simp] theorem N_ne_A : N ≠ A := by decide
@[simp] theorem N_ne_B : N ≠ B := by decide
@[simp] theorem T_ne_PROG : T ≠ PROG := by decide
@[simp] theorem T_ne_N : T ≠ N := by decide
@[simp] theorem T_ne_XS : T ≠ XS := by decide
@[simp] theorem T_ne_YS : T ≠ YS := by decide
@[simp] theorem T_ne_A : T ≠ A := by decide
@[simp] theorem T_ne_B : T ≠ B := by decide
@[simp] theorem XS_ne_PROG : XS ≠ PROG := by decide
@[simp] theorem XS_ne_N : XS ≠ N := by decide
@[simp] theorem XS_ne_T : XS ≠ T := by decide
@[simp] theorem XS_ne_YS : XS ≠ YS := by decide
@[simp] theorem XS_ne_A : XS ≠ A := by decide
@[simp] theorem XS_ne_B : XS ≠ B := by decide
@[simp] theorem YS_ne_PROG : YS ≠ PROG := by decide
@[simp] theorem YS_ne_N : YS ≠ N := by decide
@[simp] theorem YS_ne_T : YS ≠ T := by decide
@[simp] theorem YS_ne_XS : YS ≠ XS := by decide
@[simp] theorem YS_ne_A : YS ≠ A := by decide
@[simp] theorem YS_ne_B : YS ≠ B := by decide
@[simp] theorem A_ne_PROG : A ≠ PROG := by decide
@[simp] theorem A_ne_N : A ≠ N := by decide
@[simp] theorem A_ne_T : A ≠ T := by decide
@[simp] theorem A_ne_XS : A ≠ XS := by decide
@[simp] theorem A_ne_YS : A ≠ YS := by decide
@[simp] theorem A_ne_B : A ≠ B := by decide
@[simp] theorem B_ne_PROG : B ≠ PROG := by decide
@[simp] theorem B_ne_N : B ≠ N := by decide
@[simp] theorem B_ne_T : B ≠ T := by decide
@[simp] theorem B_ne_XS : B ≠ XS := by decide
@[simp] theorem B_ne_YS : B ≠ YS := by decide
@[simp] theorem B_ne_A : B ≠ A := by decide

end Names

/-! ## The input routines on descriptions -/

section Routines

variable {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt} {f : IT → ℕ}

end Routines

/-! ## The initialization -/

/-- The bound on the steps of the initialization. -/
def initBound (D : Prog) (n : ℕ) (x y a b : BitStr) (Tb : ℕ) : ℕ :=
  3 * Tb + 8 * (a.length + b.length) + (S D.toData).length + (S (encode n)).length +
    (S (encode x)).length + (S (encode y)).length + 40

/-! ## The size of a bounded representation -/

/-- A bound on `sz` from `CfgBound V L P K`. -/
def szBound (V L P K : ℕ) : ℕ := (V + P + 2) + (L * V + L) + K * (V + P + L * V + L + 4) + 1

/-! ## The simulation of a run -/

/-- The bound on the steps of `U` for one step of the machine, from representations of size at
most `Z` with a scratch tape of length at most `xl`. -/
def stepB (Z xl : ℕ) : ℕ := 100 * (Z + xl + 1) + Z + 30

/-! ## Acceptance -/

/-- The value of the encoded input. -/
abbrev vSize (n : ℕ) (x y a b : BitStr) : ℕ := (encode (n, x, y, a, b)).size

/-- The size bound on the machine's values along the run. -/
abbrev V0 (n : ℕ) (x y a b : BitStr) (Tb : ℕ) : ℕ := max (vSize n x y a b) Tb

/-- The size bound on the representations along the run. -/
abbrev Z0 (D : Prog) (n : ℕ) (x y a b : BitStr) (Tb : ℕ) : ℕ :=
  szBound (V0 n x y a b Tb) (1 + 2 * Tb) (esize D) Tb

/-- The bound on the accepting run of `U`. -/
def runBound (D : Prog) (n : ℕ) (x y a b : BitStr) (Tb : ℕ) : ℕ :=
  initBound D n x y a b Tb + 3 * Tb * stepB (Z0 D n x y a b Tb) (3 * Tb * Z0 D n x y a b Tb) +
    V0 n x y a b Tb + 16

end MIPRE.TM.Interp


