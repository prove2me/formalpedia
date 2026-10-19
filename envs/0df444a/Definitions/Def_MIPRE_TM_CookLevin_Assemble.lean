-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_Assemble
-- name    : MIPRE_TM_CookLevin_Assemble
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:33:12.144234+00:00
-- url     : https://prove2.me/theorems/e091ce03-9e77-4086-ac6f-6256cffa2719
-- title:
--   Definitions of Assemble: Assembling the succinct Cook–Levin theorem `MIPRE.SAT.succinctCookLevin` inhabits `SuccinctCookLevin`, which is…
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.Assemble` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Assembling the succinct Cook–Levin theorem. `MIPRE.SAT.succinctCookLevin` inhabits `SuccinctCookLevin`, which is blueprint `thm:succinct-sat`. Everything mathematical is already proved; what is left is to discharge, from the validity hypotheses, the side conditions the describer's theorems carry at `e = eOf T σ`, and to name the two parameter functions. * `T ≤ Sof (eOf T σ)`, `T + 3 < 2 ^ W (eOf T σ)` and `FixedLen`: the five fixed tapes are shorter than the tableau, since `|𝒟| ≤ σ < 2 ^ ⌈log σ⌉` and `2 ⌈log n⌉ ≤ T`, `|x|, |y| ≤ Q ≤ T`, and `eOf` has `5 ⌈log T⌉ + 5 ⌈log σ⌉ + 24` in the…
--
--   **Definitions** (12): `MIPRE.TM.CookLevin.Desc.LOf` (The parameter the gate bound is a polynomial in.); `MIPRE.TM.CookLevin.Desc.mParam` (The variable-count exponent `m(T, σ)`.); `MIPRE.TM.CookLevin.Desc.rParam` (The bit lengths of the parameters: the exponent of the gate bound is a multiple of this, which is why the bound is computable without any…); `MIPRE.TM.CookLevin.Desc.rProg` (`rParam`, in unary.); `MIPRE.TM.CookLevin.Desc.roundA` (The coefficient sum of a polynomial bound.); `MIPRE.TM.CookLevin.Desc.roundC` (The additive constant of the rounded bound.); `MIPRE.TM.CookLevin.Desc.roundK` (The degree of a polynomial bound.); `MIPRE.TM.CookLevin.Desc.roundPoly` (The polynomial the rounded bound stays inside.); `MIPRE.TM.CookLevin.Desc.roundUp` (**A polynomial bound, rounded up to a power of two** whose exponent is a multiple of the bit lengths of the parameters.); `MIPRE.TM.CookLevin.Desc.roundUpProg` (**A rounded bound, as a program**: a power of two whose exponent is unary, so no arithmetic on numbers is needed.); `MIPRE.TM.CookLevin.Desc.sizeN` (`Nat.size`.); `MIPRE.TM.CookLevin.Desc.toPInp` (`((𝒟, n, T, Q, σ), x, y)` reordered to `((T, σ), (𝒟, n), (x, y))`.).
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `length_rProg`, `sizeN_apply`, `toPInp_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.Assemble` (`MIPRE/TM/CookLevin/Assemble.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 67 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Assemble.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Assemble.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# Assembling the succinct Cook–Levin theorem

`MIPRE.SAT.succinctCookLevin` inhabits `SuccinctCookLevin`, which is blueprint
`thm:succinct-sat`. Everything mathematical is already proved; what is left is to discharge,
from the validity hypotheses, the side conditions the describer's theorems carry at
`e = eOf T σ`, and to name the two parameter functions.

* `T ≤ Sof (eOf T σ)`, `T + 3 < 2 ^ W (eOf T σ)` and `FixedLen`: the five fixed tapes are
  shorter than the tableau, since `|𝒟| ≤ σ < 2 ^ ⌈log σ⌉` and `2 ⌈log n⌉ ≤ T`, `|x|, |y| ≤ Q
  ≤ T`, and `eOf` has `5 ⌈log T⌉ + 5 ⌈log σ⌉ + 24` in the exponent.
* `4 T ≤ 2 ^ m`: an answer index is below `2 ^ flagOff`, and `flagOff < m`.
* The gate bound: the time bound of the program, evaluated at a linear majorant of the size of
  its input. To make it *computable from the parameters in time polynomial in their bit
  lengths* (item 5) it is rounded up to a power of two, `s = 2 ^ (k · r + c)` with
  `r = ⌈log ⌈log n⌉⌉ + ⌈log ⌈log T⌉⌉ + ⌈log Q⌉ + ⌈log σ⌉`: that needs no arithmetic on
  numbers, only `pow2P` on a unary exponent, and it is squeezed between the true gate count
  and a polynomial in `⌈log n⌉ + ⌈log T⌉ + Q + σ` (`planning/succinct-cook-levin.md`, S4).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Cost.PolyTimeFun

/-! ## Sizes of encodings -/

/-! ## The tableau is long enough -/

/-! ## The describer in the order the structure asks for -/

/-- `((𝒟, n, T, Q, σ), x, y)` reordered to `((T, σ), (𝒟, n), (x, y))`. -/
noncomputable def toPInp : PolyTimeFun DescInput PInp :=
  let pR : PolyTimeFun DescInput (Prog × ℕ × ℕ × ℕ × ℕ) := fst
  let DR : PolyTimeFun DescInput Prog := ap₁ fst pR
  let nR : PolyTimeFun DescInput ℕ := ap₁ fst (ap₁ snd pR)
  let TR : PolyTimeFun DescInput ℕ := ap₁ fst (ap₁ snd (ap₁ snd pR))
  let σR : PolyTimeFun DescInput ℕ := ap₁ snd (ap₁ snd (ap₁ snd (ap₁ snd pR)))
  (TR.pair σR).pair ((DR.pair nR).pair ((ap₁ fst snd).pair (ap₁ snd snd)))

@[simp] theorem toPInp_apply (inp : DescInput) :
    toPInp inp = ((inp.1.2.2.1, inp.1.2.2.2.2), (inp.1.1, inp.1.2.1), inp.2.1, inp.2.2) := rfl

/-! ## The size of the describer's input -/

/-- The parameter the gate bound is a polynomial in. -/
def LOf (n T Q σ : ℕ) : ℕ := Nat.size n + Nat.size T + Q + σ

/-! ## The two parameter functions -/

/-- The variable-count exponent `m(T, σ)`. -/
noncomputable def mParam (T σ : ℕ) : ℕ := mOf (eOf T σ) Gc

/-- The bit lengths of the parameters: the exponent of the gate bound is a multiple of this,
which is why the bound is computable without any arithmetic on numbers. -/
def rParam (n T Q σ : ℕ) : ℕ :=
  Nat.size (Nat.size n) + Nat.size (Nat.size T) + Nat.size Q + Nat.size σ

/-! ### Rounding a polynomial bound up to a power of two

Item 5 asks for the gate bound to be computable in time polynomial in the *bit lengths* of
the parameters, while item 3 lets it grow polynomially in `Q` and `σ` themselves. So the
bound is a number of about `log Q + log σ` bits that depends polynomially on `Q`, and
computing it looks as though it needs binary multiplication, which the ambient model does not
have. `roundUp P` is the way out: a power of two whose exponent is a multiple of `rParam`, so
that the exponent is unary and the value is `pow2P` on it. It is squeezed between `P` and a
polynomial, which is `le_roundUp` and `roundUp_le`. -/

/-- The degree of a polynomial bound. -/
noncomputable def roundK (P : Polynomial ℕ) : ℕ := P.natDegree

/-- The coefficient sum of a polynomial bound. -/
noncomputable def roundA (P : Polynomial ℕ) : ℕ :=
  ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i

/-- The additive constant of the rounded bound. -/
noncomputable def roundC (P : Polynomial ℕ) : ℕ := Nat.size (roundA P * 5 ^ roundK P)

/-- **A polynomial bound, rounded up to a power of two** whose exponent is a multiple of the
bit lengths of the parameters. -/
noncomputable def roundUp (P : Polynomial ℕ) (n T Q σ : ℕ) : ℕ :=
  2 ^ (roundK P * rParam n T Q σ + roundC P)

/-- The polynomial the rounded bound stays inside. -/
noncomputable def roundPoly (P : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (2 ^ roundC P) *
    (Polynomial.C 2 * Polynomial.X + Polynomial.C 1) ^ (4 * roundK P)

/-! ### The gate bound of the describer -/

/-! ## The parameters as programs (item 5) -/

/-- `Nat.size`. -/
noncomputable def sizeN : PolyTimeFun ℕ ℕ := ap₁ unaryToBin sizeU

@[simp] theorem sizeN_apply (k : ℕ) : sizeN k = Nat.size k := by
  rw [sizeN, ap₁_apply, unaryToBin_apply, length_sizeU]

/-- `rParam`, in unary. -/
noncomputable def rProg : PolyTimeFun (ℕ × ℕ × ℕ × ℕ) Unary :=
  ap₂ addU (ap₂ addU (ap₂ addU (ap₁ sizeU (ap₁ sizeN fst)) (ap₁ sizeU (ap₁ sizeN (ap₁ fst snd))))
    (ap₁ sizeU (ap₁ fst (ap₁ snd snd)))) (ap₁ sizeU (ap₁ snd (ap₁ snd snd)))

@[simp] theorem length_rProg (p : ℕ × ℕ × ℕ × ℕ) :
    (rProg p).length = rParam p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  simp [rProg, rParam]
  omega

/-- **A rounded bound, as a program**: a power of two whose exponent is unary, so no
arithmetic on numbers is needed. -/
noncomputable def roundUpProg (P : Polynomial ℕ) : PolyTimeFun (ℕ × ℕ × ℕ × ℕ) ℕ :=
  ap₁ pow2P (ap₂ addU (ap₁ (nsmulU (roundK P)) rProg) (const (unary (roundC P))))

end MIPRE.TM.CookLevin.Desc

namespace MIPRE.SAT

open Cost TM.CookLevin.Desc

end MIPRE.SAT


