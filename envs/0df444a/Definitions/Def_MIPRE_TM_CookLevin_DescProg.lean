-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_DescProg
-- name    : MIPRE_TM_CookLevin_DescProg
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:31:32.456594+00:00
-- url     : https://prove2.me/theorems/2d7b2e73-d0a8-49fc-b18f-64bfe06d5889
-- title:
--   Definitions of DescProg: The describer as a program `descCircP` is the describer circuit as a polynomial-time function of `((e in unary, T), (𝒟,…
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.DescProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The describer as a program. `descCircP` is the describer circuit as a polynomial-time function of `((e in unary, T), (𝒟, n), (x, y))`, and `descCircP_apply` says it is `descCirc`. This is item 4 of `thm:succinct-sat`; item 3, the gate bound, follows from it, because `PolyTimeFun.esize_apply_le` bounds the size of the output of a program by its time bound (`planning/succinct-cook-levin.md`, S3).
--
--   **Definitions** (15): `MIPRE.TM.CookLevin.Desc.DI`; `MIPRE.TM.CookLevin.Desc.DInp` (The input of the describer: `e` in unary and the time bound, the decider and the index, the two questions.); `MIPRE.TM.CookLevin.Desc.PInp` (The input of the theorem's algorithm: the time bound and the size bound, the decider and the index, the two questions.); `MIPRE.TM.CookLevin.Desc.TI`; `MIPRE.TM.CookLevin.Desc.bitsData` (A bit string as its encoding.); `MIPRE.TM.CookLevin.Desc.codesP` (The symbol codes of the serialization of a value.); `MIPRE.TM.CookLevin.Desc.describeM` (The index width, in the theorem's own parameters.); `MIPRE.TM.CookLevin.Desc.eP` (`eOf`, in unary: it is affine in `Nat.size T` and `Nat.size σ`.); `MIPRE.TM.CookLevin.Desc.euI`; `MIPRE.TM.CookLevin.Desc.mP` (The index width `m`, as a program: it is affine in `e`, so it is an `append` in unary.); `MIPRE.TM.CookLevin.Desc.nI`; `MIPRE.TM.CookLevin.Desc.sizeU` (`Nat.size`, in unary: one unit per bit.); `MIPRE.TM.CookLevin.Desc.tabsR` (`tabsOf`: the value formulas of the five fixed tapes.); `MIPRE.TM.CookLevin.Desc.xI`; `MIPRE.TM.CookLevin.Desc.yI`.
--
--   **Embedded lemmas** (13): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `DI_apply`, `TI_apply`, `bitsData_apply`, `codesOf_S`, `codesP_apply`, `describeM_apply`, `euI_apply`, `length_eP`, `length_sizeU`, `mP_apply`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.DescProg` (`MIPRE/TM/CookLevin/DescProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 61 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/DescProg.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/DescProg.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
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
import Definitions.Def_MIPRE_TM_CookLevin_FamilyProg

/-!
# The describer as a program

`descCircP` is the describer circuit as a polynomial-time function of
`((e in unary, T), (𝒟, n), (x, y))`, and `descCircP_apply` says it is `descCirc`. This is
item 4 of `thm:succinct-sat`; item 3, the gate bound, follows from it, because
`PolyTimeFun.esize_apply_le` bounds the size of the output of a program by its time bound
(`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Cost.PolyTimeFun

/-! ## The candidate of the describer -/

variable {ι : Type*} [SizedEncoding ι]

/-! ## The fixed tapes -/

/-- The symbol codes of the serialization of a value. -/
noncomputable def codesP : PolyTimeFun Data (List ℕ) :=
  (map (PolyTimeFun.ite (PolyTimeFun.id Bool) (const (symCode (.sym Sym.one)))
    (const (symCode (.sym Sym.zero))))).comp PolyTimeFun.toBits

theorem codesOf_S (d : Data) : codesOf (S d) =
    d.toBits.map fun b => if b then symCode (.sym Sym.one) else symCode (.sym Sym.zero) := by
  rw [codesOf, S, bits, List.map_map]
  congr 1
  funext b
  cases b <;> rfl

@[simp] theorem codesP_apply (d : Data) : codesP d = codesOf (S d) := by
  rw [codesOf_S, codesP, comp_apply, map_apply, PolyTimeFun.toBits_apply]
  congr 1

/-- A bit string as its encoding. -/
noncomputable def bitsData : PolyTimeFun BitStr Data :=
  PolyTimeFun.ofEncodeEq (fun l => encode l) fun _ => rfl

@[simp] theorem bitsData_apply (l : BitStr) : bitsData l = encode l := rfl

/-- `tabsOf`: the value formulas of the five fixed tapes. -/
noncomputable def tabsR (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ)
    (b : PolyTimeFun ι Unary) (DR : PolyTimeFun ι Prog) (nR : PolyTimeFun ι ℕ)
    (xR yR : PolyTimeFun ι BitStr) : PolyTimeFun ι (List (ℕ × Fml)) :=
  let A := litFieldsR eu TR b
  listOf [
    (const 0).pair (cellValR eu A (ap₁ codesP (ap₁ PolyTimeFun.progData DR))),
    (const 1).pair (cellValR eu A (ap₁ codesP (ap₁ PolyTimeFun.natData nR))),
    (const 2).pair (unaryValR eu A TR),
    (const 3).pair (cellValR eu A (ap₁ codesP (ap₁ bitsData xR))),
    (const 4).pair (cellValR eu A (ap₁ codesP (ap₁ bitsData yR)))]

/-! ## The describer -/

/-- The input of the describer: `e` in unary and the time bound, the decider and the index,
the two questions. -/
abbrev DInp := (Unary × ℕ) × (Prog × ℕ) × (BitStr × BitStr)

noncomputable def euI : PolyTimeFun DInp Unary := ap₁ fst fst
noncomputable def TI : PolyTimeFun DInp ℕ := ap₁ snd fst
noncomputable def DI : PolyTimeFun DInp Prog := ap₁ fst (ap₁ fst snd)
noncomputable def nI : PolyTimeFun DInp ℕ := ap₁ snd (ap₁ fst snd)
noncomputable def xI : PolyTimeFun DInp BitStr := ap₁ fst (ap₁ snd snd)
noncomputable def yI : PolyTimeFun DInp BitStr := ap₁ snd (ap₁ snd snd)

@[simp] theorem euI_apply (p : DInp) : euI p = p.1.1 := rfl
@[simp] theorem TI_apply (p : DInp) : TI p = p.1.2 := rfl
@[simp] theorem DI_apply (p : DInp) : DI p = p.2.1.1 := rfl
@[simp] theorem nI_apply (p : DInp) : nI p = p.2.1.2 := rfl
@[simp] theorem xI_apply (p : DInp) : xI p = p.2.2.1 := rfl
@[simp] theorem yI_apply (p : DInp) : yI p = p.2.2.2 := rfl

/-! ## The gate bound (item 3)

Item 3 needs no separate induction over the builders: a program's output is no larger than
its running time (`PolyTimeFun.esize_apply_le`), and a circuit's gate count is at most the
size of its encoding, so the gate bound of the describer *is* the time bound of the program
that writes it, which is an explicit polynomial. -/

/-! ## The width `e` and the index width (item 5) -/

/-- `Nat.size`, in unary: one unit per bit. -/
noncomputable def sizeU : PolyTimeFun ℕ Unary :=
  (map (const ())).comp PolyTimeFun.natBits

@[simp] theorem length_sizeU (k : ℕ) : (sizeU k).length = Nat.size k := by
  rw [sizeU, comp_apply, map_apply, PolyTimeFun.natBits_apply, List.length_map,
    Nat.size_eq_bits_len]

/-- `eOf`, in unary: it is affine in `Nat.size T` and `Nat.size σ`. -/
noncomputable def eP : PolyTimeFun (ℕ × ℕ) Unary :=
  ap₂ addU (ap₂ addU (ap₁ (nsmulU 5) (ap₁ sizeU fst)) (ap₁ (nsmulU 5) (ap₁ sizeU snd)))
    (const (unary 24))

@[simp] theorem length_eP (p : ℕ × ℕ) : (eP p).length = eOf p.1 p.2 := by
  rw [eP, ap₂_apply, length_addU, ap₂_apply, length_addU, ap₁_apply, length_nsmulU, ap₁_apply,
    length_sizeU, ap₁_apply, length_nsmulU, ap₁_apply, length_sizeU, const_apply, length_unary,
    fst_apply, snd_apply, eOf]

/-- The index width `m`, as a program: it is affine in `e`, so it is an `append` in unary. -/
noncomputable def mP : PolyTimeFun Unary ℕ := ap₁ unaryToBin (mU (PolyTimeFun.id _))

@[simp] theorem mP_apply (u : Unary) : mP u = mOf u.length Gc := by
  rw [mP, ap₁_apply, unaryToBin_apply, length_mU, PolyTimeFun.id_apply]

/-! ## The describer in the theorem's own parameters -/

/-- The input of the theorem's algorithm: the time bound and the size bound, the decider and
the index, the two questions. `e` is computed from `T` and `σ`. -/
abbrev PInp := (ℕ × ℕ) × (Prog × ℕ) × (BitStr × BitStr)

/-- The index width, in the theorem's own parameters. -/
noncomputable def describeM : PolyTimeFun (ℕ × ℕ) ℕ := mP.comp eP

@[simp] theorem describeM_apply (p : ℕ × ℕ) : describeM p = mOf (eOf p.1 p.2) Gc := by
  rw [describeM, comp_apply, mP_apply, length_eP]

end MIPRE.TM.CookLevin.Desc


