-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_PcpClauses
-- name    : MIPRE_TM_CookLevin_PcpClauses
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:03:45.835727+00:00
-- url     : https://prove2.me/theorems/72d751d3-17c0-422a-b992-f6b6ca36080c
-- title:
--   Definitions of PcpClauses: Clause indices and the five Boolean PCP blocks The describer reads five little-endian indices followed by their signs
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.PcpClauses` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Clause indices and the five Boolean PCP blocks. The describer reads five little-endian indices followed by their signs. This module identifies that input format with the Boolean coordinates used by the low-degree PCP, including both directions of the index encoding.
--
--   **Definitions** (7): `MIPRE.SAT.Clause5.literals` (Uniformly indexed literals of a clause with equally sized variable blocks.); `MIPRE.SAT.Clause5.ofLiterals`; `MIPRE.SAT.PcpParams.inputSlice` (The circuit-input slice of a Boolean PCP point.); `MIPRE.SAT.PcpParams.pointClause` (The clause described by the first five blocks and sign coordinates of a point.); `MIPRE.SAT.PcpParams.pointFromClause` (Extend a described clause to a PCP point, initially setting all gate coordinates to false.); `MIPRE.SAT.cubeIndex` (A Boolean cube point as a little-endian index.); `MIPRE.SAT.indexCube` (The Boolean cube point named by a little-endian index.).
--
--   **Embedded lemmas** (14): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `literals_ofLiterals`, `ofLiterals_literals`, `clauseInput5_pointClause`, `inputSlice_pointFromClause`, `length_inputSlice`, `pointClause_literals`, `pointClause_pointFromClause`, `sign_pointFromClause`, `bitsOfNat_cubeIndex`, `bitsOfNat_injective_fin`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.PcpClauses` (`MIPRE/TM/CookLevin/PcpClauses.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 37 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/PcpClauses.lean; blueprint lem:pcp-circuit-semantics

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/PcpClauses.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
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
import Definitions.Def_MIPRE_Foundations_LowDegree_ZeroBasis
import Definitions.Def_MIPRE_Foundations_SAT_PcpAlgebra
import Definitions.Def_MIPRE_Foundations_SAT_PcpBlocks
import Theorems.Thm_MIPRE_SAT_bitsVal_lt
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_bitsOfNat_bitsVal
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_bitsVal_bitsOfNat

/-!
# Clause indices and the five Boolean PCP blocks

The describer reads five little-endian indices followed by their signs. This
module identifies that input format with the Boolean coordinates used by the
low-degree PCP, including both directions of the index encoding.
-/

namespace MIPRE.SAT

open Cost LowDegree MvPolynomial

/-- A Boolean cube point as a little-endian index. -/
def cubeIndex {m : ℕ} (y : Fin m → Bool) : Fin (2 ^ m) :=
  ⟨bitsVal (List.ofFn y), by simpa using bitsVal_lt (List.ofFn y)⟩

/-- The Boolean cube point named by a little-endian index. -/
def indexCube {m : ℕ} (i : Fin (2 ^ m)) : Fin m → Bool := fun j => i.val.testBit j

@[simp] theorem bitsOfNat_cubeIndex {m : ℕ} (y : Fin m → Bool) :
    bitsOfNat m (cubeIndex y) = List.ofFn y := by
  simpa [cubeIndex] using TM.CookLevin.Desc.bitsOfNat_bitsVal (List.ofFn y)

@[simp] theorem cubeIndex_indexCube {m : ℕ} (i : Fin (2 ^ m)) : cubeIndex (indexCube i) = i := by
  apply Fin.ext
  change bitsVal (bitsOfNat m i) = i
  rw [TM.CookLevin.Desc.bitsVal_bitsOfNat, Nat.mod_eq_of_lt i.isLt]

@[simp] theorem indexCube_cubeIndex {m : ℕ} (y : Fin m → Bool) : indexCube (cubeIndex y) = y := by
  apply List.ofFn_injective
  exact bitsOfNat_cubeIndex y

theorem bitsOfNat_injective_fin (m : ℕ) :
    Function.Injective (fun i : Fin (2 ^ m) => bitsOfNat m i) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg bitsVal h
  simpa only [TM.CookLevin.Desc.bitsVal_bitsOfNat, Nat.mod_eq_of_lt i.isLt,
    Nat.mod_eq_of_lt j.isLt] using hv

/-- Equal-width clause encodings lose neither an index nor a sign. -/
theorem clauseInput5_injective (m : ℕ) : Function.Injective (clauseInput5 m m) := by
  rintro ⟨⟨a, sa⟩, ⟨b, sb⟩, ⟨c, sc⟩, ⟨d, sd⟩, ⟨e, se⟩⟩
    ⟨⟨a', sa'⟩, ⟨b', sb'⟩, ⟨c', sc'⟩, ⟨d', sd'⟩, ⟨e', se'⟩⟩ h
  simp only [clauseInput5, List.append_assoc] at h
  obtain ⟨ha, h⟩ := List.append_inj h (by simp)
  obtain ⟨hb, h⟩ := List.append_inj h (by simp)
  obtain ⟨hc, h⟩ := List.append_inj h (by simp)
  obtain ⟨hd, h⟩ := List.append_inj h (by simp)
  obtain ⟨he, h⟩ := List.append_inj h (by simp)
  have ha' := bitsOfNat_injective_fin m ha
  have hb' := bitsOfNat_injective_fin m hb
  have hc' := bitsOfNat_injective_fin m hc
  have hd' := bitsOfNat_injective_fin m hd
  have he' := bitsOfNat_injective_fin m he
  simp only [List.cons.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, _⟩ := h
  subst a'; subst b'; subst c'; subst d'; subst e'
  rfl

namespace Clause5

variable {V : Type*}

/-- Uniformly indexed literals of a clause with equally sized variable blocks. -/
def literals (c : Clause5 V V V V V) : Fin 5 → Lit V :=
  ![c.l₁, c.l₂, c.l₃, c.l₄, c.l₅]

def ofLiterals (l : Fin 5 → Lit V) : Clause5 V V V V V :=
  ⟨l 0, l 1, l 2, l 3, l 4⟩

@[simp] theorem literals_ofLiterals (l : Fin 5 → Lit V) : (ofLiterals l).literals = l := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem ofLiterals_literals (c : Clause5 V V V V V) : ofLiterals c.literals = c := by
  cases c
  rfl

theorem lit_true_iff (l : Lit V) (a : V → Bool) : l.eval a = true ↔ a l.var = l.pos := by
  cases h : l.pos <;> cases ha : a l.var <;> simp [Lit.eval, h, ha]

end Clause5

namespace PcpParams

/-- The clause described by the first five blocks and sign coordinates of a point. -/
def pointClause (P : PcpParams) (y : Fin P.m' → Bool) :
    Clause5 (Fin (2 ^ P.m)) (Fin (2 ^ P.m)) (Fin (2 ^ P.m))
      (Fin (2 ^ P.m)) (Fin (2 ^ P.m)) :=
  Clause5.ofLiterals (fun i => ⟨cubeIndex (P.block i y), y (P.signIndex i)⟩)

@[simp] theorem pointClause_literals (P : PcpParams) (y : Fin P.m' → Bool) (i : Fin 5) :
    (P.pointClause y).literals i = ⟨cubeIndex (P.block i y), y (P.signIndex i)⟩ := by
  simp [pointClause]

/-- The circuit-input slice of a Boolean PCP point. -/
def inputSlice (P : PcpParams) (y : Fin P.m' → Bool) : List Bool :=
  List.ofFn (fun j : Fin (5 * P.m + 5) => y ⟨j, by have := j.isLt; unfold m'; omega⟩)

@[simp] theorem length_inputSlice (P : PcpParams) (y : Fin P.m' → Bool) :
    (P.inputSlice y).length = 5 * P.m + 5 := List.length_ofFn

/-- The describer's actual input order agrees with the five PCP blocks and signs. -/
theorem clauseInput5_pointClause (P : PcpParams) (y : Fin P.m' → Bool) :
    clauseInput5 P.m P.m (P.pointClause y) = P.inputSlice y := by
  have hb (i : Fin 5) : P.block i y = fun j => y (P.blockIndex i j) := rfl
  simp only [pointClause, Clause5.ofLiterals, clauseInput5, bitsOfNat_cubeIndex]
  unfold inputSlice
  rw [List.ofFn_add, List.ofFn_mul]
  simp only [List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]
  simp [hb, PcpParams.blockIndex, PcpParams.signIndex]

/-- Extend a described clause to a PCP point, initially setting all gate
coordinates to false. Those coordinates may subsequently be replaced by a witness. -/
def pointFromClause (P : PcpParams)
    (c : Clause5 (Fin (2 ^ P.m)) (Fin (2 ^ P.m)) (Fin (2 ^ P.m))
      (Fin (2 ^ P.m)) (Fin (2 ^ P.m))) : Fin P.m' → Bool :=
  fun j => (clauseInput5 P.m P.m c).getD j false

theorem inputSlice_pointFromClause (P : PcpParams)
    (c : Clause5 (Fin (2 ^ P.m)) (Fin (2 ^ P.m)) (Fin (2 ^ P.m))
      (Fin (2 ^ P.m)) (Fin (2 ^ P.m))) :
    P.inputSlice (P.pointFromClause c) = clauseInput5 P.m P.m c := by
  apply List.ext_getElem
  · simp only [length_inputSlice, length_clauseInput5]
    omega
  · intro i hi hj
    simp only [inputSlice, List.getElem_ofFn, pointFromClause,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

@[simp] theorem pointClause_pointFromClause (P : PcpParams)
    (c : Clause5 (Fin (2 ^ P.m)) (Fin (2 ^ P.m)) (Fin (2 ^ P.m))
      (Fin (2 ^ P.m)) (Fin (2 ^ P.m))) : P.pointClause (P.pointFromClause c) = c := by
  apply clauseInput5_injective P.m
  rw [clauseInput5_pointClause, inputSlice_pointFromClause]

@[simp] theorem sign_pointFromClause (P : PcpParams)
    (c : Clause5 (Fin (2 ^ P.m)) (Fin (2 ^ P.m)) (Fin (2 ^ P.m))
      (Fin (2 ^ P.m)) (Fin (2 ^ P.m))) (i : Fin 5) :
    P.pointFromClause c (P.signIndex i) = (c.literals i).pos := by
  have h := congrArg (fun d => (d.literals i).pos) (P.pointClause_pointFromClause c)
  simpa only [pointClause_literals] using h

end PcpParams

end MIPRE.SAT


