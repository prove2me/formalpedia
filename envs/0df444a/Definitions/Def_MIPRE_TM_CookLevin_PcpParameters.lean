-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_PcpParameters
-- name    : MIPRE_TM_CookLevin_PcpParameters
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:13:45.674696+00:00
-- url     : https://prove2.me/theorems/37179261-0733-4460-8f63-976345683035
-- title:
--   Definitions of PcpParameters: Effective parameters for the classical PCP The odd extension degree makes the field admissible
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.PcpParameters` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Effective parameters for the classical PCP. The odd extension degree makes the field admissible. Its size is large enough for the classical majority argument, and both power-of-two dimensions divide the field size. It is also *eventually larger than every fixed power* of `8 (Q + 1) m'` (`pcpParams_field_eventually_large`): the degree carries the square of `s = size Q + size m' + 3`, and `8 (Q + 1) m' < 2^s`, so `(8 (Q + 1) m')^e < 2^{s e} ≤ q` once `s ≥ e`. Answer reduction's low-degree test needs a field polynomially larger than `m'` with an exponent this module need not know; the degree…
--
--   **Definitions** (7): `MIPRE.TM.CookLevin.Pad.fieldBase` (The base of the field degree: `8 (Q + 1) m' < 2^{fieldBase}`.); `MIPRE.TM.CookLevin.Pad.fieldBaseU` (The field degree's base, in unary.); `MIPRE.TM.CookLevin.Pad.fieldDegree` (An odd degree giving at least 82 field elements per outer coordinate, and eventually more than any fixed power of `8 (Q + 1) m'`.); `MIPRE.TM.CookLevin.Pad.fieldDegreeProg` (Compute the extension degree from binary parameters without expanding the field.); `MIPRE.TM.CookLevin.Pad.fieldDegreeU` (The field degree in unary, for the existing Shoup modulus program.); `MIPRE.TM.CookLevin.Pad.pcpParams` (The complete classical PCP parameters.); `MIPRE.TM.CookLevin.Pad.pcpParamsProg` (The actual program for the three fields of `PcpDecider.paramsProg`.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `length_fieldBaseU`, `power_dvd_of_le`.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.PcpParameters` (`MIPRE/TM/CookLevin/PcpParameters.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 85 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/PcpParameters.lean; blueprint lem:pcp-effective-parameters

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/PcpParameters.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
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
import Mathlib.Data.Nat.Factorization.Basic
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
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
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
import Definitions.Def_MIPRE_TM_CookLevin_PaddingParams
import Theorems.Thm_MIPRE_TM_CookLevin_Pad_outerDimProg_apply

/-!
# Effective parameters for the classical PCP

The odd extension degree makes the field admissible. Its size is large enough
for the classical majority argument, and both power-of-two dimensions divide
the field size. It is also *eventually larger than every fixed power* of
`8 (Q + 1) m'` (`pcpParams_field_eventually_large`): the degree carries the square of
`s = size Q + size m' + 3`, and `8 (Q + 1) m' < 2^s`, so `(8 (Q + 1) m')^e < 2^{s e} ≤ q` once
`s ≥ e`. Answer reduction's low-degree test needs a field polynomially larger than `m'` with an
exponent this module need not know; the degree stays polylogarithmic
(`fieldDegree_le`).
-/

namespace MIPRE.TM.CookLevin.Pad

open SAT Cost Cost.PolyTimeFun Desc

/-- The base of the field degree: `8 (Q + 1) m' < 2^{fieldBase}`. -/
noncomputable def fieldBase (n T Q σ : ℕ) : ℕ := Nat.size Q + Nat.size (outerDim n T Q σ) + 3

/-- An odd degree giving at least 82 field elements per outer coordinate, and eventually more
than any fixed power of `8 (Q + 1) m'`. -/
noncomputable def fieldDegree (n T Q σ : ℕ) : ℕ :=
  2 * (fieldBase n T Q σ ^ 2 + Nat.size (outerDim n T Q σ)) + 7

/-- The complete classical PCP parameters. -/
noncomputable def pcpParams (n T Q σ : ℕ) : PcpParams :=
  ⟨fieldDegree n T Q σ, innerDim T σ, gateCount n T Q σ⟩

theorem power_dvd_of_le {j k : ℕ} (h : 2 ^ j ≤ 2 ^ k) : 2 ^ j ∣ 2 ^ k := by
  have hj : j ≤ k := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h
  exact pow_dvd_pow 2 hj

/-- The field degree's base, in unary. -/
noncomputable def fieldBaseU : PolyTimeFun ParamInput Unary :=
  ap₂ addU (ap₂ addU (sizeU.comp (fst.comp (snd.comp snd))) (sizeU.comp outerDimProg))
    (const (unary 3))

@[simp] theorem length_fieldBaseU (p : ParamInput) :
    (fieldBaseU p).length = fieldBase p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  simp [fieldBaseU, fieldBase, outerDimProg_apply]
  omega

/-- The field degree in unary, for the existing Shoup modulus program. -/
noncomputable def fieldDegreeU : PolyTimeFun ParamInput Unary :=
  ap₂ addU (ap₁ (nsmulU 2) (ap₂ addU
      (LowDegree.DegreeArithmetic.mulUnaryProg.comp (fieldBaseU.pair fieldBaseU))
      (sizeU.comp outerDimProg)))
    (const (unary 7))

/-- Compute the extension degree from binary parameters without expanding the field. -/
noncomputable def fieldDegreeProg : PolyTimeFun ParamInput ℕ :=
  unaryToBin.comp fieldDegreeU

/-- The actual program for the three fields of `PcpDecider.paramsProg`. -/
noncomputable def pcpParamsProg : PolyTimeFun ParamInput (ℕ × ℕ × ℕ) :=
  fieldDegreeProg.pair paddingParams

end MIPRE.TM.CookLevin.Pad


