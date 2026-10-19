-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_PcpBlocks
-- name    : MIPRE_Foundations_SAT_PcpBlocks
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:14:40.185543+00:00
-- url     : https://prove2.me/theorems/d32937be-8b1f-458f-a27b-e8e333c18481
-- title:
--   Definitions of PcpBlocks: The five disjoint answer blocks of the classical PCP The answer polynomials have `m` variables; the formula and…
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.PcpBlocks` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The five disjoint answer blocks of the classical PCP. The answer polynomials have `m` variables; the formula and certificates have `5*m + 5 + s` variables. This file transports the former into the latter without losing the individual-degree bound. In particular, the honest constraint has degree at most seven, rather than the soundness proof's coarse bound of 41.
--
--   **Definitions** (4): `MIPRE.SAT.PcpAlgebra.TypedAccepts` (The two tests on the point and its claimed field-valued evaluations.); `MIPRE.SAT.PcpAlgebra.liftAnswer` (An answer polynomial, viewed as a polynomial on the complete PCP point.); `MIPRE.SAT.PcpParams.blockIndex` (The coordinate of an answer bit within the complete PCP point.); `MIPRE.SAT.PcpParams.signIndex` (The sign coordinates immediately follow the five answer blocks.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `eval_liftAnswer`, `factor_degree_pos`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.PcpBlocks` (`MIPRE/Foundations/SAT/PcpBlocks.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 24 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/PcpBlocks.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/PcpBlocks.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
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
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_ZeroBasis
import Definitions.Def_MIPRE_Foundations_SAT_PcpAlgebra

/-!
# The five disjoint answer blocks of the classical PCP

The answer polynomials have `m` variables; the formula and certificates have
`5*m + 5 + s` variables. This file transports the former into the latter without
losing the individual-degree bound. In particular, the honest constraint has
degree at most seven, rather than the soundness proof's coarse bound of 41.
-/

noncomputable section

namespace MIPRE.SAT

open Finset MvPolynomial LowDegree

namespace PcpParams

/-- The coordinate of an answer bit within the complete PCP point. -/
def blockIndex (P : PcpParams) (i : Fin 5) (j : Fin P.m) : Fin P.m' :=
  ⟨i * P.m + j, by
    have hi := Nat.mul_le_mul_right P.m (Nat.lt_succ_iff.mp i.isLt)
    have hj := j.isLt
    simp only [m']
    omega⟩

/-- The sign coordinates immediately follow the five answer blocks. -/
def signIndex (P : PcpParams) (i : Fin 5) : Fin P.m' :=
  ⟨5 * P.m + i, by have := i.isLt; simp only [m']; omega⟩

end PcpParams

namespace PcpAlgebra

variable {P : PcpParams} {F : Type*} [Field F]

/-- An answer polynomial, viewed as a polynomial on the complete PCP point. -/
def liftAnswer (i : Fin 5) (g : MvPolynomial (Fin P.m) F) :
    MvPolynomial (Fin P.m') F := rename (P.blockIndex i) g

@[simp] theorem eval_liftAnswer (i : Fin 5) (g : MvPolynomial (Fin P.m) F)
    (z : Fin P.m' → F) : eval z (liftAnswer i g) = eval (P.block i z) g := by
  simp only [liftAnswer, eval_rename]
  rfl

theorem factor_degree_pos (i : Fin 5) (g : MvPolynomial (Fin P.m) F)
    (j : Fin P.m') (h : 0 < (liftAnswer i g - X (P.signIndex i)).degreeOf j) :
    (∃ k, P.blockIndex i k = j) ∨ P.signIndex i = j := by
  by_contra hn
  push Not at hn
  have hz : (liftAnswer i g).degreeOf j = 0 := by
    by_contra hp
    obtain ⟨k, _, hk⟩ := mem_vars_rename _ g (mem_vars_iff_degreeOf_ne_zero.mpr hp)
    exact hn.1 k hk
  have hx : (X (P.signIndex i) : MvPolynomial (Fin P.m') F).degreeOf j = 0 :=
    degreeOf_X_of_ne (Ne.symm hn.2)
  have hb := degreeOf_sub_le j (liftAnswer i g) (X (P.signIndex i))
  rw [hz, hx] at hb
  omega

/-- The two tests on the point and its claimed field-valued evaluations. -/
def TypedAccepts (φ : MvPolynomial (Fin P.m') F) (z : Fin P.m' → F)
    (ev : (Fin 5 → F) × (Fin (P.m' + 1) → F)) : Prop :=
  ev.2 0 = eval z φ * ∏ i, (ev.1 i - z (P.signIndex i)) ∧
    ev.2 0 = ∑ j, ev.2 j.succ * (z j * (1 - z j))

end PcpAlgebra

end MIPRE.SAT

end


