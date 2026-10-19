-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_PcpCircuit
-- name    : MIPRE_TM_CookLevin_PcpCircuit
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:04:54.666494+00:00
-- url     : https://prove2.me/theorems/d2fbf2c0-9860-4ffe-ae4e-257845541e24
-- title:
--   Definitions of PcpCircuit: The circuit polynomial in the PCP clause coordinates
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.PcpCircuit` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # The circuit polynomial in the PCP clause coordinates
--
--   **Definitions** (2): `MIPRE.SAT.PcpParams.circuitArith` (The exact finite circuit polynomial transported to the advertised PCP dimension.); `MIPRE.SAT.PcpParams.decodedAssignment` (The Boolean assignment read from one low-degree answer polynomial.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `inputSlice_getD`, `ofBool_injective`.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.PcpCircuit` (`MIPRE/TM/CookLevin/PcpCircuit.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 42 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/PcpCircuit.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/PcpCircuit.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Computability.Language
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
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Relation
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
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_CookLevin_Layout
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_CircuitArithmetization
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteVariables
import Definitions.Def_MIPRE_Foundations_SAT_FiniteCircuitArithmetization
import Definitions.Def_MIPRE_Foundations_LowDegree_ZeroBasis
import Definitions.Def_MIPRE_Foundations_SAT_PcpAlgebra
import Definitions.Def_MIPRE_Foundations_SAT_PcpBlocks
import Definitions.Def_MIPRE_TM_CookLevin_PcpClauses

/-!
# The circuit polynomial in the PCP clause coordinates
-/

noncomputable section

namespace MIPRE.SAT.PcpParams

open LowDegree MvPolynomial

variable {F : Type*} [Field F] [CharP F 2]

/-- The exact finite circuit polynomial transported to the advertised PCP dimension. -/
def circuitArith (P : PcpParams) (C : Circuit) (h : C.inputs + C.size = P.m') :
    MvPolynomial (Fin P.m') F := rename (Fin.cast h) C.finiteArith

theorem inputSlice_getD (P : PcpParams) (y : Fin P.m' → Bool)
    (j : ℕ) (hj : j < 5 * P.m + 5) :
    (P.inputSlice y).getD j false = y ⟨j, by unfold m'; omega⟩ := by
  simp only [inputSlice, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hj,
    Option.getD_some]

/-- The Boolean assignment read from one low-degree answer polynomial. -/
def decodedAssignment [DecidableEq F] {P : PcpParams} (pf : PcpProof P F)
    (i : Fin 5) (j : Fin (2 ^ P.m)) : Bool := decide (coded (pf.g i) (indexCube j) = 1)

theorem ofBool_injective : Function.Injective (ofBool : Bool → F) := by
  intro a b h
  cases a <;> cases b <;> simp_all [ofBool]

end MIPRE.SAT.PcpParams

end


