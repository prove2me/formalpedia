-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_Decoupled
-- name    : MIPRE_TM_CookLevin_Decoupled
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:36:37.342045+00:00
-- url     : https://prove2.me/theorems/554b21af-746c-413d-a42f-e35b78cb318a
-- title:
--   Definitions of Decoupled: The decoupled describer, and the clauses it describes The describer of `lem:decoupled-5sat`: the 3SAT describer of…
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.Decoupled` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The decoupled describer, and the clauses it describes. The describer of `lem:decoupled-5sat`: the 3SAT describer of `thm:succinct-sat`, its inputs renamed into the five-block layout, in disjunction with the link formula of `Link.lean`, all flattened once to a circuit. `mem_formula5_iff` is the bridge — a clause is accepted exactly when the 3-clause of its last three literals is accepted by the 3SAT describer, or the clause satisfies one of the eight link conditions (`planning/decoupled-5sat.md`, A1c).
--
--   **Definitions** (10): `MIPRE.TM.CookLevin.Desc.LinkSat` (The link half: what rows 2 to 9 force.); `MIPRE.TM.CookLevin.Desc.Tri` (The three-block half: the described 3SAT formula on the three auxiliary blocks.); `MIPRE.TM.CookLevin.Desc.candOf5` (The candidate of the decoupled describer: the three field records at the shifted bases and the three auxiliary signs.); `MIPRE.TM.CookLevin.Desc.descBody5` (The tableau half of the describer's formula, on the shifted candidate.); `MIPRE.TM.CookLevin.Desc.descCirc5` (**The decoupled describer circuit**: the flattening of `descFml5` on `2ℓ + 3r + 5` inputs.); `MIPRE.TM.CookLevin.Desc.descFml5` (The formula of the decoupled describer.); `MIPRE.TM.CookLevin.Desc.lastThree` (The 3-clause of the last three literals of a decoupled clause.); `MIPRE.TM.CookLevin.Desc.offLit` (A literal of a block that the given assignment falsifies.); `MIPRE.TM.CookLevin.Desc.rho` (The renaming: the `3r` index bits of the 3SAT describer sit after the two answer indices, and its three signs after the two answer signs.); `MIPRE.TM.CookLevin.Desc.zeroIdx` (The index `0` of a block.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `offLit_eval`.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.Decoupled` (`MIPRE/TM/CookLevin/Decoupled.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 70 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Decoupled.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Decoupled.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# The decoupled describer, and the clauses it describes

The describer of `lem:decoupled-5sat`: the 3SAT describer of `thm:succinct-sat`, its inputs
renamed into the five-block layout, in disjunction with the link formula of `Link.lean`, all
flattened once to a circuit. `mem_formula5_iff` is the bridge — a clause is accepted exactly
when the 3-clause of its last three literals is accepted by the 3SAT describer, or the clause
satisfies one of the eight link conditions (`planning/decoupled-5sat.md`, A1c).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Fml

/-! ## Where the 3SAT describer's inputs go -/

/-- The renaming: the `3r` index bits of the 3SAT describer sit after the two answer
indices, and its three signs after the two answer signs. -/
def rho (ℓ r : ℕ) (k : ℕ) : ℕ := if k < 3 * r then k + 2 * ℓ else k + 2 * ℓ + 2

/-- The 3-clause of the last three literals of a decoupled clause. -/
def lastThree {ℓ r : ℕ}
    (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r))) :
    Clause3 (Fin (2 ^ r)) := ⟨c.l₃, c.l₄, c.l₅⟩

/-! ## The renaming reads the right bits -/

/-! ## The shifted candidate

The 3SAT describer's inputs cannot be *renamed* into the five-block layout by a program: the
renaming is `k ↦ k + 2ℓ` below `3r` and `k ↦ k + 2ℓ + 2` above, and deciding which needs a
comparison of two binary numbers, which the ambient model does not have. So the describer is
rebuilt on the shifted layout instead — the candidate reads its three field records at the
bases `2ℓ`, `2ℓ + r`, `2ℓ + 2r` and its three signs at `2ℓ + 3r + 2, 3, 4`. That is cheaper
in both directions: every offset is unary, so the program is the one S3 already has, and the
correctness goes straight through `eval_tableauPlusF` instead of through the renaming. -/

/-- The candidate of the decoupled describer: the three field records at the shifted bases and
the three auxiliary signs. -/
noncomputable def candOf5 (ℓ e T : ℕ) : CandF :=
  ⟨litFields e Gc T (2 * ℓ), inp (2 * ℓ + 3 * mOf e Gc + 2),
    litFields e Gc T (2 * ℓ + mOf e Gc), inp (2 * ℓ + 3 * mOf e Gc + 3),
    litFields e Gc T (2 * ℓ + 2 * mOf e Gc), inp (2 * ℓ + 3 * mOf e Gc + 4)⟩

/-! ## The describer -/

/-- The tableau half of the describer's formula, on the shifted candidate. -/
noncomputable def descBody5 (ℓ T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) : Fml :=
  tableauPlusF e Gc T (tabsOf e T D n x y (litFields e Gc T (2 * ℓ))) [5, 6]
    (tplsOf Gc chk) (candOf5 ℓ e T)

/-- The formula of the decoupled describer. -/
noncomputable def descFml5 (ℓ T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) : Fml :=
  or (descBody5 ℓ T e D n x y) (linkFml ℓ (mOf e Gc) T)

/-- **The decoupled describer circuit**: the flattening of `descFml5` on `2ℓ + 3r + 5`
inputs. -/
noncomputable def descCirc5 (ℓ T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) : Circuit :=
  (descFml5 ℓ T e D n x y).toCircuit (2 * ℓ + 3 * mOf e Gc + 5)

/-! ## What a satisfying five-tuple is

Following the paper: for a fixed triple of indices the three signs of the *other* blocks
range over all of `{0,1}³`, so a decoupled clause is satisfied exactly when the literals of
the blocks the condition constrains are. Rows 8 and 9 therefore read as equalities of whole
blocks, and rows 2 and 3 as equalities of single bits. -/

/-- The index `0` of a block. -/
def zeroIdx (k : ℕ) : Fin (2 ^ k) := ⟨0, Nat.two_pow_pos k⟩

/-- A literal of a block that the given assignment falsifies. -/
def offLit {k : ℕ} (w : Fin (2 ^ k) → Bool) : Lit (Fin (2 ^ k)) :=
  ⟨zeroIdx k, !w (zeroIdx k)⟩

@[simp] theorem offLit_eval {k : ℕ} (w : Fin (2 ^ k) → Bool) : (offLit w).eval w = false := by
  cases hw : w (zeroIdx k) <;> simp [offLit, Lit.eval, hw]

/-- The three-block half: the described 3SAT formula on the three auxiliary blocks. -/
def Tri {r : ℕ} (φ : Cnf3 (Fin (2 ^ r))) (w₁ w₂ w₃ : Fin (2 ^ r) → Bool) : Prop :=
  ∀ c ∈ φ, (c.l₁.eval w₁ || c.l₂.eval w₂ || c.l₃.eval w₃) = true

/-- The link half: what rows 2 to 9 force. -/
structure LinkSat (ℓ r T : ℕ) (a b : Fin (2 ^ ℓ) → Bool) (w₁ w₂ w₃ : Fin (2 ^ r) → Bool) :
    Prop where
  aLow : ∀ (i : Fin (2 ^ ℓ)) (j : Fin (2 ^ r)), (i : ℕ) < 2 * T → (i : ℕ) = (j : ℕ) →
    a i = w₁ j
  bLow : ∀ (i : Fin (2 ^ ℓ)) (j : Fin (2 ^ r)), (i : ℕ) < 2 * T → (j : ℕ) = (i : ℕ) + 2 * T →
    b i = w₁ j
  aPad : ∀ i : Fin (2 ^ ℓ), ¬ (i : ℕ) < 2 * T → a i = decide ((i : ℕ) % 2 = 0)
  bPad : ∀ i : Fin (2 ^ ℓ), ¬ (i : ℕ) < 2 * T → b i = decide ((i : ℕ) % 2 = 0)
  w12 : ∀ i j : Fin (2 ^ r), (i : ℕ) = (j : ℕ) → w₁ i = w₂ j
  w23 : ∀ i j : Fin (2 ^ r), (i : ℕ) = (j : ℕ) → w₂ i = w₃ j

/-! ## The padding of an answer block -/

/-! ## The describer describes the decider -/

end MIPRE.TM.CookLevin.Desc


