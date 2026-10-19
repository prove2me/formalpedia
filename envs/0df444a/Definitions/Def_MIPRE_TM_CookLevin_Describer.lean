-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_Describer
-- name    : MIPRE_TM_CookLevin_Describer
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:58:02.996307+00:00
-- url     : https://prove2.me/theorems/f63cf6d3-35a1-4b33-9775-1c039803cbc6
-- title:
--   Definitions of Describer: The describer circuit and the clauses it describes `descCirc e T D n x y` is the circuit of the describer: the…
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.Describer` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The describer circuit and the clauses it describes. `descCirc e T D n x y` is the circuit of the describer: the flattening of the formula `tableauPlusF` on the candidate that reads the three `m`-bit indices and the three signs off its `3m + 3` inputs (`candOf`). `mem_formula3_iff` is what it describes: a clause of `Fin (2 ^ m)` is accepted iff its three indices decode to the literals of a clause of `tableauPlus` — the tableau of `U` on the input tapes `fixedOf` together with the two answer-end clauses (`planning/succinct-cook-levin.md`, S3).
--
--   **Definitions** (7): `MIPRE.TM.CookLevin.Desc.FixedLen` (The tapes are short enough for the tableau.); `MIPRE.TM.CookLevin.Desc.candOf` (The candidate the describer reads off its inputs: the three `m`-bit indices at bases `0`, `m`, `2m` and the three signs at `3m`, `3m + 1`,…); `MIPRE.TM.CookLevin.Desc.candOfClause` (The candidate of a clause: the fields of its three indices and its three signs.); `MIPRE.TM.CookLevin.Desc.descCirc` (**The describer circuit**: the flattening of `descFml` on `3 m + 3` inputs.); `MIPRE.TM.CookLevin.Desc.descFml` (The formula of the describer.); `MIPRE.TM.CookLevin.Desc.fixedOf` (The input tapes of the interpreter machine: the program, the index, the time bound in unary and the two questions are fixed; the two answer…); `MIPRE.TM.CookLevin.Desc.tabsOf` (The value formulas of the fixed tapes.).
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.Describer` (`MIPRE/TM/CookLevin/Describer.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 53 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Describer.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Describer.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# The describer circuit and the clauses it describes

`descCirc e T D n x y` is the circuit of the describer: the flattening of the formula
`tableauPlusF` on the candidate that reads the three `m`-bit indices and the three signs off
its `3m + 3` inputs (`candOf`). `mem_formula3_iff` is what it describes: a clause of
`Fin (2 ^ m)` is accepted iff its three indices decode to the literals of a clause of
`tableauPlus` — the tableau of `U` on the input tapes `fixedOf` together with the two
answer-end clauses (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Fml

/-! ## Reading the input bits of a clause -/

/-! ## The input tapes -/

/-- The input tapes of the interpreter machine: the program, the index, the time bound in
unary and the two questions are fixed; the two answer tapes are free. -/
def fixedOf (D : Prog) (n T : ℕ) (x y : BitStr) : Fin 7 → Option (List Sym) :=
  ![some (S D.toData), some (S (encode n)), some (List.replicate T .one), some (S (encode x)),
    some (S (encode y)), none, none]

/-- The tapes are short enough for the tableau. -/
def FixedLen (e : ℕ) (D : Prog) (n T : ℕ) (x y : BitStr) : Prop :=
  ∀ (j : Fin 7) (s : List Sym), fixedOf D n T x y j = some s → s.length ≤ Sof e

/-- The value formulas of the fixed tapes. -/
noncomputable def tabsOf (e T : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) (A : FieldsF) :
    List (ℕ × Fml) :=
  [(0, cellValF e A (codesOf (S D.toData))), (1, cellValF e A (codesOf (S (encode n)))),
    (2, unaryValF e T A), (3, cellValF e A (codesOf (S (encode x)))),
    (4, cellValF e A (codesOf (S (encode y))))]

/-! ## The candidate of formulas -/

/-- The candidate the describer reads off its inputs: the three `m`-bit indices at bases `0`,
`m`, `2m` and the three signs at `3m`, `3m + 1`, `3m + 2`. -/
noncomputable def candOf (e G T : ℕ) : CandF :=
  ⟨litFields e G T 0, inp (3 * mOf e G), litFields e G T (mOf e G), inp (3 * mOf e G + 1),
    litFields e G T (2 * mOf e G), inp (3 * mOf e G + 2)⟩

/-! ## The circuit -/

/-- The formula of the describer. -/
noncomputable def descFml (e T : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) : Fml :=
  tableauPlusF e Gc T (tabsOf e T D n x y (litFields e Gc T 0)) [5, 6] (tplsOf Gc chk)
    (candOf e Gc T)

/-- **The describer circuit**: the flattening of `descFml` on `3 m + 3` inputs. -/
noncomputable def descCirc (e T : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) : Circuit :=
  (descFml e T D n x y).toCircuit (3 * mOf e Gc + 3)

/-! ## What the circuit describes -/

/-- The candidate of a clause: the fields of its three indices and its three signs. -/
noncomputable def candOfClause (e T : ℕ) (c : Clause3 (Fin (2 ^ mOf e Gc))) : Cand :=
  ⟨fieldsOf e Gc T (bitsOfNat (mOf e Gc) c.l₁.var), c.l₁.pos,
    fieldsOf e Gc T (bitsOfNat (mOf e Gc) c.l₂.var), c.l₂.pos,
    fieldsOf e Gc T (bitsOfNat (mOf e Gc) c.l₃.var), c.l₃.pos⟩

section Eval

variable (e T : ℕ) (c : Clause3 (Fin (2 ^ mOf e Gc)))

end Eval

end MIPRE.TM.CookLevin.Desc


