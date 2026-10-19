-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_Link
-- name    : MIPRE_TM_CookLevin_Link
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:35:08.141276+00:00
-- url     : https://prove2.me/theorems/3f6eeeee-1d57-4a68-98c0-075f949b716a
-- title:
--   Definitions of Link: The link clauses of the decoupled describer Rows 2 to 9 of the paper's circuit (`prop:explicit-succinct-deciders`): the…
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.Link` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The link clauses of the decoupled describer. Rows 2 to 9 of the paper's circuit (`prop:explicit-succinct-deciders`): the clause families that tie the two answer blocks `a, b` of a decoupled 5SAT instance to the first `4T` variables of the three auxiliary blocks, pin the padding of `a` and `b` above `2T`, and force the three auxiliary blocks to agree. `Link` is the disjunction of the eight conditions on a decoded clause and `linkFml` the formula that decides it on the `2ℓ + 3r + 5` input bits, with `eval_linkFml` their equivalence. Every comparison is made at width `r`, with the two `ℓ`-bit…
--
--   **Definitions** (14): `MIPRE.TM.CookLevin.Desc.Link` (**The link conditions** on a decoupled clause: rows 2 to 9 of the paper's circuit.); `MIPRE.TM.CookLevin.Desc.j₁F` (The two answer indices, zero-padded to `r` bits, and the three auxiliary indices.); `MIPRE.TM.CookLevin.Desc.j₂F`; `MIPRE.TM.CookLevin.Desc.j₃F`; `MIPRE.TM.CookLevin.Desc.j₄F`; `MIPRE.TM.CookLevin.Desc.j₅F`; `MIPRE.TM.CookLevin.Desc.linkFml` (The formula deciding `Link` on the `2ℓ + 3r + 5` input bits.); `MIPRE.TM.CookLevin.Desc.sgList` (The five signs, as a list.); `MIPRE.TM.CookLevin.Desc.sgOff` (The offset of the five signs.); `MIPRE.TM.CookLevin.Desc.s₁F` (The five signs.); `MIPRE.TM.CookLevin.Desc.s₂F`; `MIPRE.TM.CookLevin.Desc.s₃F`; `MIPRE.TM.CookLevin.Desc.s₄F`; `MIPRE.TM.CookLevin.Desc.s₅F`.
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `length_j₃F`, `length_j₄F`, `length_j₅F`.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.Link` (`MIPRE/TM/CookLevin/Link.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 69 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Link.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Link.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# The link clauses of the decoupled describer

Rows 2 to 9 of the paper's circuit (`prop:explicit-succinct-deciders`): the clause families
that tie the two answer blocks `a, b` of a decoupled 5SAT instance to the first `4T`
variables of the three auxiliary blocks, pin the padding of `a` and `b` above `2T`, and force
the three auxiliary blocks to agree.

`Link` is the disjunction of the eight conditions on a decoded clause and `linkFml` the
formula that decides it on the `2ℓ + 3r + 5` input bits, with `eval_linkFml` their
equivalence. Every comparison is made at width `r`, with the two `ℓ`-bit answer indices
zero-padded: at width `ℓ` the constant `2T` is not representable when `T` is a power of two,
since then `2T = 2 ^ ℓ` exactly (`planning/decoupled-5sat.md`, A1b).

**The parities of rows 4 to 7 are a repair of the verification campaign.** Blocks are
`0`-indexed and the blank encodes as `10`, so the honest padding starts at the even index
`2T` and puts `1` at even indices and `0` at odd ones. The pre-repair text had it the other
way round, which is violated by the honest assignment and breaks completeness. Our
`tapeBits` past the end of a string is the blank cell, hence `true` at even and `false` at
odd positions, so it agrees with the repaired parity.
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Fml

/-! ## The input layout -/

section Layout

variable (ℓ r : ℕ)

/-- The offset of the five signs. -/
def sgOff : ℕ := 2 * ℓ + 3 * r

/-- The two answer indices, zero-padded to `r` bits, and the three auxiliary indices. -/
def j₁F : List Fml := padTo r (field 0 ℓ)
def j₂F : List Fml := padTo r (field ℓ ℓ)
def j₃F : List Fml := field (2 * ℓ) r
def j₄F : List Fml := field (2 * ℓ + r) r
def j₅F : List Fml := field (2 * ℓ + 2 * r) r

/-- The five signs. -/
def s₁F : Fml := inp (sgOff ℓ r)
def s₂F : Fml := inp (sgOff ℓ r + 1)
def s₃F : Fml := inp (sgOff ℓ r + 2)
def s₄F : Fml := inp (sgOff ℓ r + 3)
def s₅F : Fml := inp (sgOff ℓ r + 4)

@[simp] theorem length_j₃F : (j₃F ℓ r).length = r := length_field _ _
@[simp] theorem length_j₄F : (j₄F ℓ r).length = r := length_field _ _
@[simp] theorem length_j₅F : (j₅F ℓ r).length = r := length_field _ _

end Layout

/-! ## The eight conditions -/

variable (ℓ r T : ℕ)

/-- **The link conditions** on a decoupled clause: rows 2 to 9 of the paper's circuit. -/
def Link (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r))) :
    Prop :=
  ((c.l₁.var : ℕ) < 2 * T ∧ (c.l₁.var : ℕ) = (c.l₃.var : ℕ) ∧ c.l₁.pos ≠ c.l₃.pos) ∨
  ((c.l₂.var : ℕ) < 2 * T ∧ (c.l₃.var : ℕ) = (c.l₂.var : ℕ) + 2 * T ∧ c.l₂.pos ≠ c.l₃.pos) ∨
  (¬ (c.l₁.var : ℕ) < 2 * T ∧ (c.l₁.var : ℕ) % 2 = 0 ∧ c.l₁.pos = true) ∨
  (¬ (c.l₁.var : ℕ) < 2 * T ∧ ¬ (c.l₁.var : ℕ) % 2 = 0 ∧ c.l₁.pos = false) ∨
  (¬ (c.l₂.var : ℕ) < 2 * T ∧ (c.l₂.var : ℕ) % 2 = 0 ∧ c.l₂.pos = true) ∨
  (¬ (c.l₂.var : ℕ) < 2 * T ∧ ¬ (c.l₂.var : ℕ) % 2 = 0 ∧ c.l₂.pos = false) ∨
  ((c.l₃.var : ℕ) = (c.l₄.var : ℕ) ∧ c.l₃.pos ≠ c.l₄.pos) ∨
  ((c.l₄.var : ℕ) = (c.l₅.var : ℕ) ∧ c.l₄.pos ≠ c.l₅.pos)

/-- The formula deciding `Link` on the `2ℓ + 3r + 5` input bits. -/
def linkFml : Fml :=
  orList [
    andList [ltConst (j₁F ℓ r) (nbits r (2 * T)), eqFields (j₁F ℓ r) (j₃F ℓ r),
      xor (s₁F ℓ r) (s₃F ℓ r)],
    andList [ltConst (j₂F ℓ r) (nbits r (2 * T)),
      addConstRel (j₂F ℓ r) (j₃F ℓ r) (nbits r (2 * T)), xor (s₂F ℓ r) (s₃F ℓ r)],
    andList [not (ltConst (j₁F ℓ r) (nbits r (2 * T))),
      not ((j₁F ℓ r).headD (const false)), s₁F ℓ r],
    andList [not (ltConst (j₁F ℓ r) (nbits r (2 * T))),
      (j₁F ℓ r).headD (const false), not (s₁F ℓ r)],
    andList [not (ltConst (j₂F ℓ r) (nbits r (2 * T))),
      not ((j₂F ℓ r).headD (const false)), s₂F ℓ r],
    andList [not (ltConst (j₂F ℓ r) (nbits r (2 * T))),
      (j₂F ℓ r).headD (const false), not (s₂F ℓ r)],
    andList [eqFields (j₃F ℓ r) (j₄F ℓ r), xor (s₃F ℓ r) (s₄F ℓ r)],
    andList [eqFields (j₄F ℓ r) (j₅F ℓ r), xor (s₄F ℓ r) (s₅F ℓ r)]]

/-! ## The slices of a clause's input -/

section Slices

variable {ℓ r : ℕ}
  (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)))

/-- The five signs, as a list. -/
def sgList : BitStr := [c.l₁.pos, c.l₂.pos, c.l₃.pos, c.l₄.pos, c.l₅.pos]

end Slices

/-! ## The formula decides the conditions -/

end MIPRE.TM.CookLevin.Desc


