-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_FamilyProg
-- name    : MIPRE_TM_CookLevin_FamilyProg
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:30:49.522545+00:00
-- url     : https://prove2.me/theorems/effb2a74-901a-4d39-99ca-251b04b59564
-- title:
--   Definitions of FamilyProg: The family formulas as programs Every formula of `FamilyFml.lean` as a program reading a shared input: a candidate of…
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.FamilyProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The family formulas as programs. Every formula of `FamilyFml.lean` as a program reading a shared input: a candidate of readers (`CandR`), the width `e` in unary, and the data the explicit families need. The statement of each is `progR … i = familyF (eu i).length Gc … (C.ev i)`, and its proof is `simp` over the constants of the layout — the shape of the formula matches definitionally, because `CandR.ev` is a structure literal of the programs' own values. The constants are the only content: `Sof e = 2 ^ e` and `2 * Sof e + k = 2 ^ (e + 1) + k` come from `pow2P` and `incN`, and `numR` turns a…
--
--   **Definitions** (85): `MIPRE.TM.CookLevin.Desc.SofAddR` (`Sof e + k`.); `MIPRE.TM.CookLevin.Desc.SofR` (`Sof e`.); `MIPRE.TM.CookLevin.Desc.addRelR` (`addConstRel`.); `MIPRE.TM.CookLevin.Desc.andR` (`andList` of readers.); `MIPRE.TM.CookLevin.Desc.andTwo` (`and` of two readers.); `MIPRE.TM.CookLevin.Desc.ansEndR` (`ansEndF`.); `MIPRE.TM.CookLevin.Desc.auxEqR` (`auxEqF`.); `MIPRE.TM.CookLevin.Desc.auxMatchR` (`auxMatchN`.); `MIPRE.TM.CookLevin.Desc.bdryCellR` (`bdryCellF`.); `MIPRE.TM.CookLevin.Desc.bdryHeadR` (`bdryHeadF`.); `MIPRE.TM.CookLevin.Desc.bdryPredR` (`bdryPredF`.); `MIPRE.TM.CookLevin.Desc.bdryR` (`bdryF`.); `MIPRE.TM.CookLevin.Desc.cellEqR` (`cellEqF`.); `MIPRE.TM.CookLevin.Desc.cellValR` (`cellValF`.); `MIPRE.TM.CookLevin.Desc.emitBadR` (`emitBadF`.); `MIPRE.TM.CookLevin.Desc.emitMonoR` (`emitMonoF`.); `MIPRE.TM.CookLevin.Desc.emitOnceR` (`emitOnceF`.); `MIPRE.TM.CookLevin.Desc.emitOneR` (`emitOneF`.); `MIPRE.TM.CookLevin.Desc.emitPredR` (`emitPredF`.); `MIPRE.TM.CookLevin.Desc.emitStepR` (`emitStepF`.); `MIPRE.TM.CookLevin.Desc.emitZeroR` (`emitZeroF`.); `MIPRE.TM.CookLevin.Desc.eqC` (`eqConst`.); `MIPRE.TM.CookLevin.Desc.eqF` (`eqFields`.); `MIPRE.TM.CookLevin.Desc.finalEmittedR` (`finalEmittedF`.); `MIPRE.TM.CookLevin.Desc.finalPredR` (`finalPredF`.); `MIPRE.TM.CookLevin.Desc.finalStateR` (`finalStateF`.); `MIPRE.TM.CookLevin.Desc.freeBdryR` (`freeBdryF`.); `MIPRE.TM.CookLevin.Desc.freeBlankR` (`freeBlankF`.); `MIPRE.TM.CookLevin.Desc.freeNandR` (`freeNandF`.); and 27 more.
--
--   **Embedded lemmas** (88): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `SofAddR_apply`, `SofR_apply`, `addRelR_apply`, `andR_apply`, `andTwo_apply`, `ansEndR_apply`, `auxEqR_apply`, `auxMatchR_apply`, `bdryCellR_apply`, `bdryHeadR_apply`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.FamilyProg` (`MIPRE/TM/CookLevin/FamilyProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 59 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/FamilyProg.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/FamilyProg.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
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
import Definitions.Def_MIPRE_TM_CookLevin_LayoutProg
import Definitions.Def_MIPRE_TM_CookLevin_FieldProg
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_nbitsR_const
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_nbitsR_num

/-!
# The family formulas as programs

Every formula of `FamilyFml.lean` as a program reading a shared input: a candidate of
readers (`CandR`), the width `e` in unary, and the data the explicit families need. The
statement of each is `progR … i = familyF (eu i).length Gc … (C.ev i)`, and its proof is
`simp` over the constants of the layout — the shape of the formula matches definitionally,
because `CandR.ev` is a structure literal of the programs' own values.

The constants are the only content: `Sof e = 2 ^ e` and `2 * Sof e + k = 2 ^ (e + 1) + k`
come from `pow2P` and `incN`, and `numR` turns a number and a width into the bit string of
the field constant (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Cost.PolyTimeFun

variable {ι : Type*} [SizedEncoding ι]

/-! ## Conjunctions and disjunctions of readers -/

/-- `andList` of readers. -/
noncomputable def andR (fs : List (PolyTimeFun ι Fml)) : PolyTimeFun ι Fml :=
  ap₁ andListP (listOf fs)

@[simp] theorem andR_apply (fs : List (PolyTimeFun ι Fml)) (i : ι) :
    andR fs i = Fml.andList (fs.map fun f => f i) := by
  rw [andR, ap₁_apply, listOf_apply, andListP_apply]

/-- `orList` of readers. -/
noncomputable def orR (fs : List (PolyTimeFun ι Fml)) : PolyTimeFun ι Fml :=
  ap₁ orListP (listOf fs)

@[simp] theorem orR_apply (fs : List (PolyTimeFun ι Fml)) (i : ι) :
    orR fs i = Fml.orList (fs.map fun f => f i) := by
  rw [orR, ap₁_apply, listOf_apply, orListP_apply]

/-- `and` of two readers. -/
noncomputable def andTwo (f g : PolyTimeFun ι Fml) : PolyTimeFun ι Fml := ap₂ Fml.andF f g

@[simp] theorem andTwo_apply (f g : PolyTimeFun ι Fml) (i : ι) :
    andTwo f g i = Fml.and (f i) (g i) := rfl

/-- `or` of two readers. -/
noncomputable def orTwo (f g : PolyTimeFun ι Fml) : PolyTimeFun ι Fml := ap₂ Fml.orF f g

@[simp] theorem orTwo_apply (f g : PolyTimeFun ι Fml) (i : ι) :
    orTwo f g i = Fml.or (f i) (g i) := rfl

/-- `not` of a reader. -/
noncomputable def notR (f : PolyTimeFun ι Fml) : PolyTimeFun ι Fml := ap₁ Fml.notF f

@[simp] theorem notR_apply (f : PolyTimeFun ι Fml) (i : ι) : notR f i = Fml.not (f i) := rfl

/-- `xnor` of two readers. -/
noncomputable def xnorR (f g : PolyTimeFun ι Fml) : PolyTimeFun ι Fml := ap₂ xnorP f g

@[simp] theorem xnorR_apply (f g : PolyTimeFun ι Fml) (i : ι) :
    xnorR f g i = Fml.xnor (f i) (g i) := rfl

/-- `mux` of three readers. -/
noncomputable def muxR (s f g : PolyTimeFun ι Fml) : PolyTimeFun ι Fml := ap₃ muxP s f g

@[simp] theorem muxR_apply (s f g : PolyTimeFun ι Fml) (i : ι) :
    muxR s f g i = Fml.mux (s i) (f i) (g i) := rfl

/-- `eqConst`. -/
noncomputable def eqC (fs : PolyTimeFun ι (List Fml)) (c : PolyTimeFun ι BitStr) :
    PolyTimeFun ι Fml := ap₂ eqConstP fs c

@[simp] theorem eqC_apply (fs : PolyTimeFun ι (List Fml)) (c : PolyTimeFun ι BitStr) (i : ι) :
    eqC fs c i = Fml.eqConst (fs i) (c i) := rfl

/-- `ltConst`. -/
noncomputable def ltC (fs : PolyTimeFun ι (List Fml)) (c : PolyTimeFun ι BitStr) :
    PolyTimeFun ι Fml := ap₂ ltConstP fs c

@[simp] theorem ltC_apply (fs : PolyTimeFun ι (List Fml)) (c : PolyTimeFun ι BitStr) (i : ι) :
    ltC fs c i = Fml.ltConst (fs i) (c i) := rfl

/-- `eqFields`. -/
noncomputable def eqF (fs gs : PolyTimeFun ι (List Fml)) : PolyTimeFun ι Fml :=
  ap₂ eqFieldsP fs gs

@[simp] theorem eqF_apply (fs gs : PolyTimeFun ι (List Fml)) (i : ι) :
    eqF fs gs i = Fml.eqFields (fs i) (gs i) := rfl

/-- `ltFields`. -/
noncomputable def ltF (fs gs : PolyTimeFun ι (List Fml)) : PolyTimeFun ι Fml :=
  ap₂ ltFieldsP fs gs

@[simp] theorem ltF_apply (fs gs : PolyTimeFun ι (List Fml)) (i : ι) :
    ltF fs gs i = Fml.ltFields (fs i) (gs i) := rfl

/-- `addConstRel`. -/
noncomputable def addRelR (fs gs : PolyTimeFun ι (List Fml)) (c : PolyTimeFun ι BitStr) :
    PolyTimeFun ι Fml := addConstRelP.comp ((fs.pair gs).pair c)

@[simp] theorem addRelR_apply (fs gs : PolyTimeFun ι (List Fml)) (c : PolyTimeFun ι BitStr)
    (i : ι) : addRelR fs gs c i = Fml.addConstRel (fs i) (gs i) (c i) := rfl

/-! ## The constants of the layout -/

/-- A field constant, from a width in unary and the number. -/
noncomputable def numR (w : PolyTimeFun ι Unary) (kR : PolyTimeFun ι ℕ) :
    PolyTimeFun ι BitStr := nbitsR w (ap₁ natBits kR)

@[simp] theorem numR_apply (w : PolyTimeFun ι Unary) (kR : PolyTimeFun ι ℕ) (i : ι) :
    numR w kR i = nbits (w i).length (kR i) := nbitsR_num w kR i

/-- A field constant with a fixed value. -/
noncomputable def numC (w : PolyTimeFun ι Unary) (k : ℕ) : PolyTimeFun ι BitStr :=
  nbitsR w (bitsR k)

@[simp] theorem numC_apply (w : PolyTimeFun ι Unary) (k : ℕ) (i : ι) :
    numC w k i = nbits (w i).length k := nbitsR_const w k i

section Consts

variable (eu : PolyTimeFun ι Unary)

/-- `Sof e`. -/
noncomputable def SofR : PolyTimeFun ι ℕ := ap₁ pow2P eu

@[simp] theorem SofR_apply (i : ι) : SofR eu i = Sof (eu i).length := rfl

/-- `2 * Sof e`, as `Sof (e + 1)`. -/
noncomputable def twoSR : PolyTimeFun ι ℕ := ap₁ pow2P (ap₂ addU eu (const (unary 1)))

@[simp] theorem twoSR_apply (i : ι) : twoSR eu i = 2 * Sof (eu i).length := by
  rw [twoSR, ap₁_apply, pow2P_apply, ap₂_apply, length_addU, const_apply, length_unary, Sof,
    pow_succ, mul_comm]

/-- `Sof e + k`. -/
noncomputable def SofAddR (k : ℕ) : PolyTimeFun ι ℕ := ap₁ (incN k) (SofR eu)

@[simp] theorem SofAddR_apply (k : ℕ) (i : ι) : SofAddR eu k i = Sof (eu i).length + k := by
  rw [SofAddR, ap₁_apply, incN_apply, SofR_apply]

/-- `2 * Sof e + k`. -/
noncomputable def twoSAddR (k : ℕ) : PolyTimeFun ι ℕ := ap₁ (incN k) (twoSR eu)

@[simp] theorem twoSAddR_apply (k : ℕ) (i : ι) :
    twoSAddR eu k i = 2 * Sof (eu i).length + k := by
  rw [twoSAddR, ap₁_apply, incN_apply, twoSR_apply]

end Consts

/-! ## The kind predicates -/

section Kinds

variable (eu : PolyTimeFun ι Unary) (A B : FieldsR ι)

/-- `numEqF`. -/
noncomputable def numEqR : PolyTimeFun ι Fml :=
  andR ([eqF A.tag B.tag, eqF A.t B.t, eqF A.d B.d, eqF A.p B.p, eqF A.v B.v, eqF A.q B.q,
    eqF A.g B.g] ++ List.ofFn fun k : Fin 13 => eqF (A.js k) (B.js k))

@[simp] theorem numEqR_apply (i : ι) : numEqR A B i = numEqF (A.ev i) (B.ev i) := by
  simp [numEqR, numEqF, FieldsR.ev]

/-- `isCellF`. -/
noncomputable def isCellR : PolyTimeFun ι Fml :=
  orTwo
    (andR [A.flag, eqC A.tag (numC threeU 0), ltC A.t (numR (WU eu) (SofAddR eu 1)),
      ltC A.d (numC fourU 13), ltC A.p (numR (WU eu) (twoSAddR eu 7)), ltC A.v (numC threeU 7)])
    (andR [notR A.flag, A.ansOk, eqC A.tag (numC threeU 0), eqC A.t (numC (WU eu) 0),
      ltC A.d (numC fourU 7), ltC A.p (numR (WU eu) (twoSAddR eu 7)), ltC A.v (numC threeU 7)])

@[simp] theorem isCellR_apply (i : ι) : isCellR eu A i = isCellF (eu i).length (A.ev i) := by
  simp [isCellR, isCellF, FieldsR.ev, numCells]

/-- `isHeadF`. -/
noncomputable def isHeadR : PolyTimeFun ι Fml :=
  andR [A.flag, eqC A.tag (numC threeU 1), ltC A.t (numR (WU eu) (SofAddR eu 1)),
    ltC A.d (numC fourU 13), ltC A.p (numR (WU eu) (twoSAddR eu 7))]

@[simp] theorem isHeadR_apply (i : ι) : isHeadR eu A i = isHeadF (eu i).length (A.ev i) := by
  simp [isHeadR, isHeadF, FieldsR.ev, numCells]

/-- `isStateF`. -/
noncomputable def isStateR : PolyTimeFun ι Fml :=
  andR [A.flag, eqC A.tag (numC threeU 2), ltC A.t (numR (WU eu) (SofAddR eu 1)),
    ltC A.q (numC QbU QC)]

@[simp] theorem isStateR_apply (i : ι) : isStateR eu A i = isStateF (eu i).length (A.ev i) := by
  simp [isStateR, isStateF, FieldsR.ev]

/-- `isEmitOneF`. -/
noncomputable def isEmitOneR : PolyTimeFun ι Fml :=
  andR [A.flag, eqC A.tag (numC threeU 3), ltC A.t (numR (WU eu) (SofR eu))]

@[simp] theorem isEmitOneR_apply (i : ι) :
    isEmitOneR eu A i = isEmitOneF (eu i).length (A.ev i) := by
  simp [isEmitOneR, isEmitOneF, FieldsR.ev]

/-- `isEmitBadF`. -/
noncomputable def isEmitBadR : PolyTimeFun ι Fml :=
  andR [A.flag, eqC A.tag (numC threeU 4), ltC A.t (numR (WU eu) (SofR eu))]

@[simp] theorem isEmitBadR_apply (i : ι) :
    isEmitBadR eu A i = isEmitBadF (eu i).length (A.ev i) := by
  simp [isEmitBadR, isEmitBadF, FieldsR.ev]

/-- `isEmittedF`. -/
noncomputable def isEmittedR : PolyTimeFun ι Fml :=
  andR [A.flag, eqC A.tag (numC threeU 5), ltC A.t (numR (WU eu) (SofAddR eu 1))]

@[simp] theorem isEmittedR_apply (i : ι) :
    isEmittedR eu A i = isEmittedF (eu i).length (A.ev i) := by
  simp [isEmittedR, isEmittedF, FieldsR.ev]

/-- `isAuxF`. -/
noncomputable def isAuxR : PolyTimeFun ι Fml :=
  andR ([A.flag, eqC A.tag (numC threeU 6), ltC A.t (numR (WU eu) (SofR eu)),
    ltC A.g (numC GbU Gc)] ++
    List.ofFn fun k : Fin 13 => ltC (A.js k) (numR (WU eu) (twoSAddR eu 3)))

@[simp] theorem isAuxR_apply (i : ι) : isAuxR eu A i = isAuxF (eu i).length Gc (A.ev i) := by
  simp [isAuxR, isAuxF, FieldsR.ev]

/-! ## The same-variable formulas -/

/-- `cellEqF`. -/
noncomputable def cellEqR : PolyTimeFun ι Fml :=
  andR [eqF A.t B.t, eqF A.d B.d, eqF A.p B.p, eqF A.v B.v]

@[simp] theorem cellEqR_apply (i : ι) : cellEqR A B i = cellEqF (A.ev i) (B.ev i) := by
  simp [cellEqR, cellEqF, FieldsR.ev]

/-- `headEqF`. -/
noncomputable def headEqR : PolyTimeFun ι Fml := andR [eqF A.t B.t, eqF A.d B.d, eqF A.p B.p]

@[simp] theorem headEqR_apply (i : ι) : headEqR A B i = headEqF (A.ev i) (B.ev i) := by
  simp [headEqR, headEqF, FieldsR.ev]

/-- `stateEqF`. -/
noncomputable def stateEqR : PolyTimeFun ι Fml := andR [eqF A.t B.t, eqF A.q B.q]

@[simp] theorem stateEqR_apply (i : ι) : stateEqR A B i = stateEqF (A.ev i) (B.ev i) := by
  simp [stateEqR, stateEqF, FieldsR.ev]

/-- `auxEqF`. -/
noncomputable def auxEqR : PolyTimeFun ι Fml :=
  andR ([eqF A.t B.t, eqF A.g B.g] ++ List.ofFn fun k : Fin 13 => eqF (A.js k) (B.js k))

@[simp] theorem auxEqR_apply (i : ι) : auxEqR A B i = auxEqF (A.ev i) (B.ev i) := by
  simp [auxEqR, auxEqF, FieldsR.ev]

/-- `samePosF`. -/
noncomputable def samePosR : PolyTimeFun ι Fml := andR [eqF A.t B.t, eqF A.d B.d, eqF A.p B.p]

@[simp] theorem samePosR_apply (i : ι) : samePosR A B i = samePosF (A.ev i) (B.ev i) := by
  simp [samePosR, samePosF, FieldsR.ev]

end Kinds

/-! ## Mapping over a list read off the input -/

/-- Mapping a reader of pairs over a list read off the input. -/
noncomputable def mapR {α γ : Type*} [SizedEncoding α] [SizedEncoding γ]
    (F : PolyTimeFun (α × ι) γ) (l : PolyTimeFun ι (List α)) : PolyTimeFun ι (List γ) :=
  (mapWith F).comp (l.pair (PolyTimeFun.id _))

@[simp] theorem mapR_apply {α γ : Type*} [SizedEncoding α] [SizedEncoding γ]
    (F : PolyTimeFun (α × ι) γ) (l : PolyTimeFun ι (List α)) (i : ι) :
    mapR F l i = (l i).map fun a => F (a, i) := rfl

/-! ## Unit clauses and signs -/

section Unit

variable (eu : PolyTimeFun ι Unary) (C : CandR ι)

/-- `unitCellF`. -/
noncomputable def unitCellR : PolyTimeFun ι Fml :=
  andR [isCellR eu C.A₁, isCellR eu C.A₂, isCellR eu C.A₃, cellEqR C.A₁ C.A₂, cellEqR C.A₁ C.A₃]

@[simp] theorem unitCellR_apply (i : ι) :
    unitCellR eu C i = unitCellF (eu i).length (C.ev i) := by
  simp [unitCellR, unitCellF, CandR.ev]

/-- `unitHeadF`. -/
noncomputable def unitHeadR : PolyTimeFun ι Fml :=
  andR [isHeadR eu C.A₁, isHeadR eu C.A₂, isHeadR eu C.A₃, headEqR C.A₁ C.A₂, headEqR C.A₁ C.A₃]

@[simp] theorem unitHeadR_apply (i : ι) :
    unitHeadR eu C i = unitHeadF (eu i).length (C.ev i) := by
  simp [unitHeadR, unitHeadF, CandR.ev]

/-- `unitStateF`. -/
noncomputable def unitStateR : PolyTimeFun ι Fml :=
  andR [isStateR eu C.A₁, isStateR eu C.A₂, isStateR eu C.A₃, stateEqR C.A₁ C.A₂,
    stateEqR C.A₁ C.A₃]

@[simp] theorem unitStateR_apply (i : ι) :
    unitStateR eu C i = unitStateF (eu i).length (C.ev i) := by
  simp [unitStateR, unitStateF, CandR.ev]

/-- `unitEmitBadF`. -/
noncomputable def unitEmitBadR : PolyTimeFun ι Fml :=
  andR [isEmitBadR eu C.A₁, isEmitBadR eu C.A₂, isEmitBadR eu C.A₃, eqF C.A₁.t C.A₂.t,
    eqF C.A₁.t C.A₃.t]

@[simp] theorem unitEmitBadR_apply (i : ι) :
    unitEmitBadR eu C i = unitEmitBadF (eu i).length (C.ev i) := by
  simp [unitEmitBadR, unitEmitBadF, CandR.ev, FieldsR.ev]

/-- `unitEmittedF`. -/
noncomputable def unitEmittedR : PolyTimeFun ι Fml :=
  andR [isEmittedR eu C.A₁, isEmittedR eu C.A₂, isEmittedR eu C.A₃, eqF C.A₁.t C.A₂.t,
    eqF C.A₁.t C.A₃.t]

@[simp] theorem unitEmittedR_apply (i : ι) :
    unitEmittedR eu C i = unitEmittedF (eu i).length (C.ev i) := by
  simp [unitEmittedR, unitEmittedF, CandR.ev, FieldsR.ev]

/-- `unitAuxF`. -/
noncomputable def unitAuxR : PolyTimeFun ι Fml :=
  andR [isAuxR eu C.A₁, isAuxR eu C.A₂, isAuxR eu C.A₃, auxEqR C.A₁ C.A₂, auxEqR C.A₁ C.A₃]

@[simp] theorem unitAuxR_apply (i : ι) :
    unitAuxR eu C i = unitAuxF (eu i).length Gc (C.ev i) := by
  simp [unitAuxR, unitAuxF, CandR.ev]

/-- `sameSignsF`. -/
noncomputable def sameSignsR : PolyTimeFun ι Fml :=
  andTwo (xnorR C.σ₂ C.σ₁) (xnorR C.σ₃ C.σ₁)

@[simp] theorem sameSignsR_apply (i : ι) : sameSignsR C i = sameSignsF (C.ev i) := by
  simp [sameSignsR, sameSignsF, CandR.ev]

end Unit

/-! ## Positions and values -/

section Values

variable (eu : PolyTimeFun ι Unary) (A : FieldsR ι)

/-- `bdryF`. -/
noncomputable def bdryR : PolyTimeFun ι Fml :=
  orTwo (ltC A.p (numC (WU eu) 2)) (notR (ltC A.p (numR (WU eu) (twoSAddR eu 5))))

@[simp] theorem bdryR_apply (i : ι) : bdryR eu A i = bdryF (eu i).length (A.ev i) := by
  simp [bdryR, bdryF, FieldsR.ev]

/-- `startCellF`. -/
noncomputable def startCellR : PolyTimeFun ι Fml :=
  muxR (ltC A.d (numC fourU 7)) (eqC A.p (numC (WU eu) 3))
    (eqC A.p (numR (WU eu) (SofAddR eu 3)))

@[simp] theorem startCellR_apply (i : ι) :
    startCellR eu A i = startCellF (eu i).length (A.ev i) := by
  simp [startCellR, startCellF, FieldsR.ev]

/-- `workValF`. -/
noncomputable def workValR : PolyTimeFun ι Fml :=
  muxR (bdryR eu A) (eqC A.v (numC threeU 6)) (eqC A.v (numC threeU 5))

@[simp] theorem workValR_apply (i : ι) :
    workValR eu A i = workValF (eu i).length (A.ev i) := by
  simp [workValR, workValF, FieldsR.ev]

/-- The lookup table, written as a map over the codes paired with their positions. -/
theorem lookupList_eq (e : ℕ) (A : FieldsF) : ∀ (k : ℕ) (cs : List ℕ),
    lookupList e A k cs = (cs.zip (List.range' k cs.length)).map
      fun p => Fml.and (Fml.eqConst A.p (nbits (W e) p.2)) (Fml.eqConst A.v (nbits 3 p.1))
  | _, [] => rfl
  | k, c :: cs => by
    rw [lookupList, List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons,
      lookupList_eq e A (k + 1) cs]

/-- `lookupList`, from cell `3`. -/
noncomputable def lookupR (codes : PolyTimeFun ι (List ℕ)) : PolyTimeFun ι (List Fml) :=
  mapR (andTwo (eqC (ap₁ A.p snd) (numR (ap₁ (WU eu) snd) (ap₁ snd fst)))
      (eqC (ap₁ A.v snd) (numR threeU (ap₁ fst fst))))
    (ap₂ zip codes (ap₂ range'P (const 3) (ap₁ length codes)))

@[simp] theorem lookupR_apply (codes : PolyTimeFun ι (List ℕ)) (i : ι) :
    lookupR eu A codes i = lookupList (eu i).length (A.ev i) 3 (codes i) := by
  rw [lookupList_eq]
  simp [lookupR, FieldsR.ev]

/-- `cellValF`. -/
noncomputable def cellValR (codes : PolyTimeFun ι (List ℕ)) : PolyTimeFun ι Fml :=
  muxR (bdryR eu A) (eqC A.v (numC threeU 6))
    (muxR (andTwo (notR (ltC A.p (numC (WU eu) 3)))
        (ltC A.p (numR (WU eu) (ap₁ (incN 3) (ap₁ unaryToBin (ap₁ length codes))))))
      (ap₁ orListP (lookupR eu A codes)) (eqC A.v (numC threeU 5)))

@[simp] theorem cellValR_apply (codes : PolyTimeFun ι (List ℕ)) (i : ι) :
    cellValR eu A codes i = cellValF (eu i).length (A.ev i) (codes i) := by
  simp [cellValR, cellValF, FieldsR.ev]

/-- `unaryValF`. -/
noncomputable def unaryValR (TR : PolyTimeFun ι ℕ) : PolyTimeFun ι Fml :=
  muxR (bdryR eu A) (eqC A.v (numC threeU 6))
    (muxR (andTwo (notR (ltC A.p (numC (WU eu) 3)))
        (ltC A.p (numR (WU eu) (ap₁ (incN 3) TR))))
      (eqC A.v (numC threeU 1)) (eqC A.v (numC threeU 5)))

@[simp] theorem unaryValR_apply (TR : PolyTimeFun ι ℕ) (i : ι) :
    unaryValR eu A TR i = unaryValF (eu i).length (TR i) (A.ev i) := by
  simp [unaryValR, unaryValF, FieldsR.ev]

/-- `freeTapeF`. -/
noncomputable def freeTapeR (frees : PolyTimeFun ι (List ℕ)) : PolyTimeFun ι Fml :=
  ap₁ orListP (mapR (eqC (ap₁ A.d snd) (numR fourU fst)) frees)

@[simp] theorem freeTapeR_apply (frees : PolyTimeFun ι (List ℕ)) (i : ι) :
    freeTapeR A frees i = freeTapeF (frees i) (A.ev i) := by
  simp [freeTapeR, freeTapeF, FieldsR.ev]

/-- `tZeroF`. -/
noncomputable def tZeroR : PolyTimeFun ι Fml := eqC A.t (numC (WU eu) 0)

@[simp] theorem tZeroR_apply (i : ι) : tZeroR eu A i = tZeroF (eu i).length (A.ev i) := by
  simp [tZeroR, tZeroF, FieldsR.ev]

end Values

/-! ## The start family -/

section Start

variable (eu : PolyTimeFun ι Unary) (C : CandR ι) (tabs : PolyTimeFun ι (List (ℕ × Fml)))

/-- `startHeadF`. -/
noncomputable def startHeadR : PolyTimeFun ι Fml :=
  andR [unitHeadR eu C, sameSignsR C, tZeroR eu C.A₁, xnorR C.σ₁ (startCellR eu C.A₁)]

@[simp] theorem startHeadR_apply (i : ι) :
    startHeadR eu C i = startHeadF (eu i).length (C.ev i) := by
  simp [startHeadR, startHeadF, CandR.ev]

/-- `startStateF`. -/
noncomputable def startStateR : PolyTimeFun ι Fml :=
  andR [unitStateR eu C, sameSignsR C, tZeroR eu C.A₁,
    xnorR C.σ₁ (eqC C.A₁.q (numC QbU (qCode (some U.q₀))))]

@[simp] theorem startStateR_apply (i : ι) :
    startStateR eu C i = startStateF (eu i).length (C.ev i) := by
  simp [startStateR, startStateF, CandR.ev, FieldsR.ev]

/-- `startFixedF`. -/
noncomputable def startFixedR : PolyTimeFun ι Fml :=
  andR [unitCellR eu C, sameSignsR C, tZeroR eu C.A₁,
    ap₁ orListP (mapR (andTwo (eqC (ap₁ C.A₁.d snd) (numR fourU (ap₁ fst fst)))
      (xnorR (ap₁ C.σ₁ snd) (ap₁ snd fst))) tabs)]

@[simp] theorem startFixedR_apply (i : ι) :
    startFixedR eu C tabs i = startFixedF (eu i).length (tabs i) (C.ev i) := by
  simp [startFixedR, startFixedF, CandR.ev, FieldsR.ev]

/-- `startWorkF`. -/
noncomputable def startWorkR : PolyTimeFun ι Fml :=
  andR [unitCellR eu C, sameSignsR C, tZeroR eu C.A₁,
    notR (ltC C.A₁.d (numC fourU 7)), xnorR C.σ₁ (workValR eu C.A₁)]

@[simp] theorem startWorkR_apply (i : ι) :
    startWorkR eu C i = startWorkF (eu i).length (C.ev i) := by
  simp [startWorkR, startWorkF, CandR.ev, FieldsR.ev]

/-- `startF`. -/
noncomputable def startR : PolyTimeFun ι Fml :=
  orR [startHeadR eu C, startStateR eu C, startFixedR eu C tabs, startWorkR eu C]

@[simp] theorem startR_apply (i : ι) :
    startR eu C tabs i = startF (eu i).length (tabs i) (C.ev i) := by
  simp [startR, startF]

end Start

/-! ## The free family -/

section Free

variable (eu : PolyTimeFun ι Unary) (C : CandR ι) (frees : PolyTimeFun ι (List ℕ))

/-- `freeBdryF`. -/
noncomputable def freeBdryR : PolyTimeFun ι Fml :=
  andR [unitCellR eu C, sameSignsR C, tZeroR eu C.A₁, freeTapeR C.A₁ frees, bdryR eu C.A₁,
    xnorR C.σ₁ (eqC C.A₁.v (numC threeU 6))]

@[simp] theorem freeBdryR_apply (i : ι) :
    freeBdryR eu C frees i = freeBdryF (eu i).length (frees i) (C.ev i) := by
  simp [freeBdryR, freeBdryF, CandR.ev, FieldsR.ev]

/-- `freeOtherF`. -/
noncomputable def freeOtherR : PolyTimeFun ι Fml :=
  andR [unitCellR eu C, sameSignsR C, tZeroR eu C.A₁, freeTapeR C.A₁ frees,
    notR (bdryR eu C.A₁), notR (eqC C.A₁.v (numC threeU 0)),
    notR (eqC C.A₁.v (numC threeU 1)), notR (eqC C.A₁.v (numC threeU 5)), notR C.σ₁]

@[simp] theorem freeOtherR_apply (i : ι) :
    freeOtherR eu C frees i = freeOtherF (eu i).length (frees i) (C.ev i) := by
  simp [freeOtherR, freeOtherF, CandR.ev, FieldsR.ev]

/-- `freeTwoF`. -/
noncomputable def freeTwoR : PolyTimeFun ι Fml :=
  andR [unitCellR eu C, sameSignsR C, tZeroR eu C.A₁, freeTapeR C.A₁ frees,
    eqC C.A₁.p (numC (WU eu) 2), xnorR C.σ₁ (eqC C.A₁.v (numC threeU 5))]

@[simp] theorem freeTwoR_apply (i : ι) :
    freeTwoR eu C frees i = freeTwoF (eu i).length (frees i) (C.ev i) := by
  simp [freeTwoR, freeTwoF, CandR.ev, FieldsR.ev]

/-- `freeOneOfF`. -/
noncomputable def freeOneOfR : PolyTimeFun ι Fml :=
  andR [isCellR eu C.A₁, isCellR eu C.A₂, isCellR eu C.A₃, samePosR C.A₁ C.A₂,
    samePosR C.A₁ C.A₃, tZeroR eu C.A₁, freeTapeR C.A₁ frees, notR (bdryR eu C.A₁),
    eqC C.A₁.v (numC threeU 0), eqC C.A₂.v (numC threeU 1), eqC C.A₃.v (numC threeU 5),
    C.σ₁, C.σ₂, C.σ₃]

@[simp] theorem freeOneOfR_apply (i : ι) :
    freeOneOfR eu C frees i = freeOneOfF (eu i).length (frees i) (C.ev i) := by
  simp [freeOneOfR, freeOneOfF, CandR.ev, FieldsR.ev]

/-- `freeNandF`. -/
noncomputable def freeNandR : PolyTimeFun ι Fml :=
  andR [isCellR eu C.A₁, isCellR eu C.A₂, isCellR eu C.A₃, samePosR C.A₁ C.A₂,
    cellEqR C.A₂ C.A₃, tZeroR eu C.A₁, freeTapeR C.A₁ frees, notR (bdryR eu C.A₁),
    notR (eqF C.A₁.v C.A₂.v), notR C.σ₁, notR C.σ₂, notR C.σ₃]

@[simp] theorem freeNandR_apply (i : ι) :
    freeNandR eu C frees i = freeNandF (eu i).length (frees i) (C.ev i) := by
  simp [freeNandR, freeNandF, CandR.ev, FieldsR.ev]

/-- `freeBlankF`. -/
noncomputable def freeBlankR : PolyTimeFun ι Fml :=
  andR [isCellR eu C.A₁, isCellR eu C.A₂, isCellR eu C.A₃, cellEqR C.A₂ C.A₃,
    tZeroR eu C.A₁, freeTapeR C.A₁ frees, eqF C.A₂.t C.A₁.t, eqF C.A₂.d C.A₁.d,
    notR (ltC C.A₁.p (numC (WU eu) 3)), notR (bdryR eu C.A₂), ltF C.A₁.p C.A₂.p,
    eqC C.A₁.v (numC threeU 5), eqC C.A₂.v (numC threeU 5), notR C.σ₁, C.σ₂, C.σ₃]

@[simp] theorem freeBlankR_apply (i : ι) :
    freeBlankR eu C frees i = freeBlankF (eu i).length (frees i) (C.ev i) := by
  simp [freeBlankR, freeBlankF, CandR.ev, FieldsR.ev]

/-- `freeF`. -/
noncomputable def freeR : PolyTimeFun ι Fml :=
  orR [freeBdryR eu C frees, freeOtherR eu C frees, freeTwoR eu C frees, freeOneOfR eu C frees,
    freeNandR eu C frees, freeBlankR eu C frees]

@[simp] theorem freeR_apply (i : ι) :
    freeR eu C frees i = freeF (eu i).length (frees i) (C.ev i) := by
  simp [freeR, freeF]

end Free

/-! ## The boundary, emission and final families -/

section BEF

variable (eu : PolyTimeFun ι Unary) (C : CandR ι)

/-- `bdryCellF`. -/
noncomputable def bdryCellR : PolyTimeFun ι Fml :=
  andR [unitCellR eu C, sameSignsR C, bdryR eu C.A₁,
    xnorR C.σ₁ (eqC C.A₁.v (numC threeU 6))]

@[simp] theorem bdryCellR_apply (i : ι) :
    bdryCellR eu C i = bdryCellF (eu i).length (C.ev i) := by
  simp [bdryCellR, bdryCellF, CandR.ev, FieldsR.ev]

/-- `bdryHeadF`. -/
noncomputable def bdryHeadR : PolyTimeFun ι Fml :=
  andR [unitHeadR eu C, sameSignsR C, bdryR eu C.A₁, notR C.σ₁]

@[simp] theorem bdryHeadR_apply (i : ι) :
    bdryHeadR eu C i = bdryHeadF (eu i).length (C.ev i) := by
  simp [bdryHeadR, bdryHeadF, CandR.ev]

/-- `bdryPredF`. -/
noncomputable def bdryPredR : PolyTimeFun ι Fml := orTwo (bdryCellR eu C) (bdryHeadR eu C)

@[simp] theorem bdryPredR_apply (i : ι) :
    bdryPredR eu C i = bdryPredF (eu i).length (C.ev i) := by
  simp [bdryPredR, bdryPredF]

/-- `emitZeroF`. -/
noncomputable def emitZeroR : PolyTimeFun ι Fml :=
  andR [unitEmittedR eu C, sameSignsR C, tZeroR eu C.A₁, notR C.σ₁]

@[simp] theorem emitZeroR_apply (i : ι) :
    emitZeroR eu C i = emitZeroF (eu i).length (C.ev i) := by
  simp [emitZeroR, emitZeroF, CandR.ev]

/-- `emitStepF`. -/
noncomputable def emitStepR : PolyTimeFun ι Fml :=
  andR [isEmittedR eu C.A₁, isEmittedR eu C.A₂, isEmitOneR eu C.A₃,
    addRelR C.A₃.t C.A₁.t (numC (WU eu) 1), eqF C.A₂.t C.A₃.t, notR C.σ₁, C.σ₂, C.σ₃]

@[simp] theorem emitStepR_apply (i : ι) :
    emitStepR eu C i = emitStepF (eu i).length (C.ev i) := by
  simp [emitStepR, emitStepF, CandR.ev, FieldsR.ev]

/-- `emitMonoF`. -/
noncomputable def emitMonoR : PolyTimeFun ι Fml :=
  andR [isEmittedR eu C.A₁, isEmittedR eu C.A₂, isEmittedR eu C.A₃,
    ltC C.A₁.t (numR (WU eu) (SofR eu)), addRelR C.A₁.t C.A₂.t (numC (WU eu) 1),
    eqF C.A₃.t C.A₂.t, notR C.σ₁, C.σ₂, C.σ₃]

@[simp] theorem emitMonoR_apply (i : ι) :
    emitMonoR eu C i = emitMonoF (eu i).length (C.ev i) := by
  simp [emitMonoR, emitMonoF, CandR.ev, FieldsR.ev]

/-- `emitOneF`. -/
noncomputable def emitOneR : PolyTimeFun ι Fml :=
  andR [isEmitOneR eu C.A₁, isEmittedR eu C.A₂, isEmittedR eu C.A₃,
    addRelR C.A₁.t C.A₂.t (numC (WU eu) 1), eqF C.A₃.t C.A₂.t, notR C.σ₁, C.σ₂, C.σ₃]

@[simp] theorem emitOneR_apply (i : ι) :
    emitOneR eu C i = emitOneF (eu i).length (C.ev i) := by
  simp [emitOneR, emitOneF, CandR.ev, FieldsR.ev]

/-- `emitOnceF`. -/
noncomputable def emitOnceR : PolyTimeFun ι Fml :=
  andR [isEmitOneR eu C.A₁, isEmittedR eu C.A₂, isEmittedR eu C.A₃, eqF C.A₂.t C.A₁.t,
    eqF C.A₃.t C.A₂.t, notR C.σ₁, notR C.σ₂, notR C.σ₃]

@[simp] theorem emitOnceR_apply (i : ι) :
    emitOnceR eu C i = emitOnceF (eu i).length (C.ev i) := by
  simp [emitOnceR, emitOnceF, CandR.ev, FieldsR.ev]

/-- `emitBadF`. -/
noncomputable def emitBadR : PolyTimeFun ι Fml :=
  andR [unitEmitBadR eu C, sameSignsR C, notR C.σ₁]

@[simp] theorem emitBadR_apply (i : ι) :
    emitBadR eu C i = emitBadF (eu i).length (C.ev i) := by
  simp [emitBadR, emitBadF, CandR.ev]

/-- `emitPredF`. -/
noncomputable def emitPredR : PolyTimeFun ι Fml :=
  orR [emitZeroR eu C, emitStepR eu C, emitMonoR eu C, emitOneR eu C, emitOnceR eu C,
    emitBadR eu C]

@[simp] theorem emitPredR_apply (i : ι) :
    emitPredR eu C i = emitPredF (eu i).length (C.ev i) := by
  simp [emitPredR, emitPredF]

/-- `finalStateF`. -/
noncomputable def finalStateR : PolyTimeFun ι Fml :=
  andR [unitStateR eu C, sameSignsR C, eqC C.A₁.t (numR (WU eu) (SofR eu)),
    eqC C.A₁.q (numC QbU (qCode none)), C.σ₁]

@[simp] theorem finalStateR_apply (i : ι) :
    finalStateR eu C i = finalStateF (eu i).length (C.ev i) := by
  simp [finalStateR, finalStateF, CandR.ev, FieldsR.ev]

/-- `finalEmittedF`. -/
noncomputable def finalEmittedR : PolyTimeFun ι Fml :=
  andR [unitEmittedR eu C, sameSignsR C, eqC C.A₁.t (numR (WU eu) (SofR eu)), C.σ₁]

@[simp] theorem finalEmittedR_apply (i : ι) :
    finalEmittedR eu C i = finalEmittedF (eu i).length (C.ev i) := by
  simp [finalEmittedR, finalEmittedF, CandR.ev, FieldsR.ev]

/-- `finalPredF`. -/
noncomputable def finalPredR : PolyTimeFun ι Fml :=
  orTwo (finalStateR eu C) (finalEmittedR eu C)

@[simp] theorem finalPredR_apply (i : ι) :
    finalPredR eu C i = finalPredF (eu i).length (C.ev i) := by
  simp [finalPredR, finalPredF]

end BEF

/-! ## The five explicit families -/

/-- `mainF`. -/
noncomputable def mainR (eu : PolyTimeFun ι Unary) (C : CandR ι)
    (tabs : PolyTimeFun ι (List (ℕ × Fml))) (frees : PolyTimeFun ι (List ℕ)) :
    PolyTimeFun ι Fml :=
  orR [startR eu C tabs, freeR eu C frees, bdryPredR eu C, emitPredR eu C, finalPredR eu C]

@[simp] theorem mainR_apply (eu : PolyTimeFun ι Unary) (C : CandR ι)
    (tabs : PolyTimeFun ι (List (ℕ × Fml))) (frees : PolyTimeFun ι (List ℕ)) (i : ι) :
    mainR eu C tabs frees i = mainF (eu i).length (tabs i) (frees i) (C.ev i) := by
  simp [mainR, mainF]

/-! ## The window family

The templates of the check circuit are a *constant* of the describer — `Gc` is fixed — so
the program maps over `tplsOf Gc chk` at the Lean level and the descriptors never have to be
encoded: each becomes a `const` reader. -/

/-- `selectF`, written as a map over the pairs. -/
theorem selectF_zipWith : ∀ (hot : List Bool) (fs : List Fml),
    List.zipWith (fun b f => Fml.and (Fml.const b) f) hot fs =
      (hot.zip fs).map fun p => Fml.and (Fml.const p.1) p.2
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: hot, _ :: fs => by
    rw [List.zipWith_cons_cons, List.zip_cons_cons, List.map_cons, selectF_zipWith hot fs]

theorem selectF_eq (hot : List Bool) (fs : List Fml) :
    selectF hot fs = Fml.orList ((hot.zip fs).map fun p => Fml.and (Fml.const p.1) p.2) :=
  congrArg Fml.orList (selectF_zipWith hot fs)

/-- `selectF`. -/
noncomputable def selectR (hot : PolyTimeFun ι (List Bool)) (fs : PolyTimeFun ι (List Fml)) :
    PolyTimeFun ι Fml :=
  ap₁ orListP (mapR (andTwo (ap₁ Fml.constF (ap₁ fst fst)) (ap₁ snd fst)) (ap₂ zip hot fs))

@[simp] theorem selectR_apply (hot : PolyTimeFun ι (List Bool)) (fs : PolyTimeFun ι (List Fml))
    (i : ι) : selectR hot fs i = selectF (hot i) (fs i) := by
  rw [selectF_eq]
  simp [selectR]

section Window

variable (eu : PolyTimeFun ι Unary) (Fa A : FieldsR ι)

/-- `posF`. -/
noncomputable def posR (dHot : List Bool) (δ : BitStr) : PolyTimeFun ι Fml :=
  selectR (const dHot)
    (listOf (List.ofFn fun k : Fin 13 =>
      addRelR (Fa.js k) A.p (ap₂ padP (WU eu) (const δ))))

@[simp] theorem posR_apply (dHot : List Bool) (δ : BitStr) (i : ι) :
    posR eu Fa A dHot δ i = posF (eu i).length (Fa.ev i) (A.ev i) dHot δ := by
  simp [posR, posF, FieldsR.ev]

/-- `winMatchN`. -/
noncomputable def winMatchR (w : WDesc) : PolyTimeFun ι Fml :=
  selectR (const w.kind) (listOf [
    andR [isCellR eu A, eqF A.t Fa.t, eqC A.d (const w.d), posR eu Fa A w.dHot w.δ,
      eqC A.v (const w.v)],
    andR [isHeadR eu A, eqF A.t Fa.t, eqC A.d (const w.d), posR eu Fa A w.dHot w.δ],
    andR [isCellR eu A, addRelR Fa.t A.t (numC (WU eu) 1), eqC A.d (const w.d),
      posR eu Fa A w.dHot w.δ, eqC A.v (const w.v)],
    andR [isHeadR eu A, addRelR Fa.t A.t (numC (WU eu) 1), eqC A.d (const w.d),
      posR eu Fa A w.dHot w.δ],
    andR [isStateR eu A, eqF A.t Fa.t, eqC A.q (const w.q)],
    andR [isStateR eu A, addRelR Fa.t A.t (numC (WU eu) 1), eqC A.q (const w.q)],
    andR [isEmitOneR eu A, eqF A.t Fa.t],
    andR [isEmitBadR eu A, eqF A.t Fa.t]])

@[simp] theorem winMatchR_apply (w : WDesc) (i : ι) :
    winMatchR eu Fa A w i = winMatchN (eu i).length (Fa.ev i) (A.ev i) w := by
  simp [winMatchR, winMatchN, FieldsR.ev]

/-- `auxMatchN`. -/
noncomputable def auxMatchR (u : BitStr) : PolyTimeFun ι Fml :=
  andR ([isAuxR eu A, eqF A.t Fa.t, eqC A.g (const u)] ++
    List.ofFn fun k : Fin 13 => eqF (A.js k) (Fa.js k))

@[simp] theorem auxMatchR_apply (u : BitStr) (i : ι) :
    auxMatchR eu Fa A u i = auxMatchN (eu i).length Gc (Fa.ev i) (A.ev i) u := by
  simp [auxMatchR, auxMatchN, FieldsR.ev]

/-- `specMatchN`. -/
noncomputable def specMatchR (l : LDesc) : PolyTimeFun ι Fml :=
  muxR (const (Fml.const l.isAux)) (auxMatchR eu Fa A l.u) (winMatchR eu Fa A l.w)

@[simp] theorem specMatchR_apply (l : LDesc) (i : ι) :
    specMatchR eu Fa A l i = specMatchN (eu i).length Gc (Fa.ev i) (A.ev i) l := by
  simp [specMatchR, specMatchN]

end Window

section WindowPred

variable (eu : PolyTimeFun ι Unary) (C : CandR ι)

/-- `tplN`. -/
noncomputable def tplR (tp : NTpl) : PolyTimeFun ι Fml :=
  andR [specMatchR eu C.A₃ C.A₁ tp.1.1, xnorR C.σ₁ (const (Fml.const tp.1.2)),
    specMatchR eu C.A₃ C.A₂ tp.2.1.1, xnorR C.σ₂ (const (Fml.const tp.2.1.2)),
    specMatchR eu C.A₃ C.A₃ tp.2.2.1, xnorR C.σ₃ (const (Fml.const tp.2.2.2))]

@[simp] theorem tplR_apply (tp : NTpl) (i : ι) :
    tplR eu C tp i = tplN (eu i).length Gc tp (C.ev i) := by
  simp [tplR, tplN, CandR.ev]

/-- `windowGatesN`, on the templates of the check circuit. -/
noncomputable def windowGatesR : PolyTimeFun ι Fml :=
  orR ((tplsOf Gc chk).map fun l => orR (l.map fun tp => tplR eu C tp))

@[simp] theorem windowGatesR_apply (i : ι) :
    windowGatesR eu C i = windowGatesN (eu i).length Gc (tplsOf Gc chk) (C.ev i) := by
  simp [windowGatesR, windowGatesN, List.map_map, Function.comp_def]

/-- `windowOutF`. -/
noncomputable def windowOutR : PolyTimeFun ι Fml :=
  andR [unitAuxR eu C, sameSignsR C, eqC C.A₁.g (numC GbU (Gc - 1)), C.σ₁]

@[simp] theorem windowOutR_apply (i : ι) :
    windowOutR eu C i = windowOutF (eu i).length Gc (C.ev i) := by
  simp [windowOutR, windowOutF, CandR.ev, FieldsR.ev]

/-- `windowN`. -/
noncomputable def windowR : PolyTimeFun ι Fml :=
  orTwo (windowGatesR eu C) (windowOutR eu C)

@[simp] theorem windowR_apply (i : ι) :
    windowR eu C i = windowN (eu i).length Gc (tplsOf Gc chk) (C.ev i) := by
  simp [windowR, windowN]

end WindowPred

/-! ## The whole tableau -/

/-- `tableauF`. -/
noncomputable def tableauR (eu : PolyTimeFun ι Unary) (C : CandR ι)
    (tabs : PolyTimeFun ι (List (ℕ × Fml))) (frees : PolyTimeFun ι (List ℕ)) :
    PolyTimeFun ι Fml :=
  orTwo (mainR eu C tabs frees) (windowR eu C)

@[simp] theorem tableauR_apply (eu : PolyTimeFun ι Unary) (C : CandR ι)
    (tabs : PolyTimeFun ι (List (ℕ × Fml))) (frees : PolyTimeFun ι (List ℕ)) (i : ι) :
    tableauR eu C tabs frees i =
      tableauF (eu i).length Gc (tabs i) (frees i) (tplsOf Gc chk) (C.ev i) := by
  simp [tableauR, tableauF]

/-! ## The answer-end clauses -/

/-- `ansEndF`. -/
noncomputable def ansEndR (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (C : CandR ι) :
    PolyTimeFun ι Fml :=
  andR [unitCellR eu C, sameSignsR C, tZeroR eu C.A₁,
    orTwo (eqC C.A₁.d (numC fourU 5)) (eqC C.A₁.d (numC fourU 6)),
    eqC C.A₁.p (numR (WU eu) (ap₁ (incN 3) TR)), eqC C.A₁.v (numC threeU 5), C.σ₁]

@[simp] theorem ansEndR_apply (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (C : CandR ι)
    (i : ι) : ansEndR eu TR C i = ansEndF (eu i).length (TR i) (C.ev i) := by
  simp [ansEndR, ansEndF, CandR.ev, FieldsR.ev]

/-- `tableauPlusF`. -/
noncomputable def tableauPlusR (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (C : CandR ι)
    (tabs : PolyTimeFun ι (List (ℕ × Fml))) (frees : PolyTimeFun ι (List ℕ)) :
    PolyTimeFun ι Fml :=
  orTwo (tableauR eu C tabs frees) (ansEndR eu TR C)

@[simp] theorem tableauPlusR_apply (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ)
    (C : CandR ι) (tabs : PolyTimeFun ι (List (ℕ × Fml))) (frees : PolyTimeFun ι (List ℕ))
    (i : ι) : tableauPlusR eu TR C tabs frees i =
      tableauPlusF (eu i).length Gc (TR i) (tabs i) (frees i) (tplsOf Gc chk) (C.ev i) := by
  simp [tableauPlusR, tableauPlusF]

end MIPRE.TM.CookLevin.Desc


