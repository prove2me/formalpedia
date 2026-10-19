-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_PaddingParams
-- name    : MIPRE_TM_CookLevin_PaddingParams
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:04:33.203645+00:00
-- url     : https://prove2.me/theorems/7e14a0e1-ef5e-4755-b7ee-d899304acbf2
-- title:
--   Definitions of PaddingParams: Effective parameters for exact succinct padding Both dimensions and the exact gate count are computed from binary…
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.PaddingParams` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Effective parameters for exact succinct padding. Both dimensions and the exact gate count are computed from binary parameters in polynomial time in their bit lengths. Only the logarithmically bounded inner dimension is expanded to unary; the much larger gate count stays binary.
--
--   **Definitions** (5): `MIPRE.TM.CookLevin.Pad.ParamInput`; `MIPRE.TM.CookLevin.Pad.gateCountProg` (Binary computation of the exact gate count.); `MIPRE.TM.CookLevin.Pad.innerDimParamsU` (Compute the common input width in unary from the four binary parameters.); `MIPRE.TM.CookLevin.Pad.outerDimProg` (Binary computation of the outer power-of-two dimension.); `MIPRE.TM.CookLevin.Pad.paddingParams` (The two padded-describer parameters, with an ambient polynomial-time program.).
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.PaddingParams` (`MIPRE/TM/CookLevin/PaddingParams.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 80 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/PaddingParams.lean; blueprint prop:pcp-padded-describer

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/PaddingParams.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
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
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
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
import Definitions.Def_MIPRE_TM_CookLevin_LayoutProg
import Definitions.Def_MIPRE_TM_CookLevin_FieldProg
import Definitions.Def_MIPRE_TM_CookLevin_FamilyProg
import Definitions.Def_MIPRE_TM_CookLevin_DescProg
import Definitions.Def_MIPRE_TM_CookLevin_Semantics
import Definitions.Def_MIPRE_TM_CookLevin_Correct
import Definitions.Def_MIPRE_TM_CookLevin_Sound
import Definitions.Def_MIPRE_TM_CookLevin_Sat
import Definitions.Def_MIPRE_TM_CookLevin_Assemble
import Definitions.Def_MIPRE_TM_CookLevin_Link
import Definitions.Def_MIPRE_TM_CookLevin_Decoupled
import Definitions.Def_MIPRE_TM_CookLevin_DecoupledProg
import Definitions.Def_MIPRE_Foundations_SAT_Padding
import Definitions.Def_MIPRE_Foundations_SAT_Rename
import Definitions.Def_MIPRE_Foundations_SAT_PowerPadding
import Definitions.Def_MIPRE_TM_CookLevin_Padded
import Definitions.Def_MIPRE_Foundations_SAT_GatePadding
import Definitions.Def_MIPRE_TM_CookLevin_ExactPadding

/-!
# Effective parameters for exact succinct padding

Both dimensions and the exact gate count are computed from binary parameters
in polynomial time in their bit lengths. Only the logarithmically bounded
inner dimension is expanded to unary; the much larger gate count stays binary.
-/

namespace MIPRE.TM.CookLevin.Pad

open SAT Cost Cost.PolyTimeFun Desc

abbrev ParamInput := ℕ × ℕ × ℕ × ℕ

/-- Compute the common input width in unary from the four binary parameters. -/
noncomputable def innerDimParamsU : PolyTimeFun ParamInput Unary :=
  ceilPowerProg.comp (mU (eP.comp ((fst.comp snd).pair (snd.comp (snd.comp snd)))))

/-- Binary computation of the outer power-of-two dimension. -/
noncomputable def outerDimProg : PolyTimeFun ParamInput ℕ :=
  let small := ap₂ addU (ap₁ (nsmulU 6) innerDimParamsU) (const (unary 5))
  let total := ap₂ addUnary (roundUpProg gatePoly) small
  ap₁ pow2P (ap₁ sizeU (ap₁ predN total))

/-- Binary computation of the exact gate count. -/
noncomputable def gateCountProg : PolyTimeFun ParamInput ℕ :=
  ap₂ subUnary outerDimProg
    (ap₂ addU (ap₁ (nsmulU 5) innerDimParamsU) (const (unary 5)))

/-- The two padded-describer parameters, with an ambient polynomial-time program. -/
noncomputable def paddingParams : PolyTimeFun ParamInput (ℕ × ℕ) :=
  (unaryToBin.comp innerDimParamsU).pair gateCountProg

end MIPRE.TM.CookLevin.Pad


