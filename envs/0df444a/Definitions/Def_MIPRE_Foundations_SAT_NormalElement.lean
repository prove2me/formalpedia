-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_NormalElement
-- name    : MIPRE_Foundations_SAT_NormalElement
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T06:11:58.45004+00:00
-- url     : https://prove2.me/theorems/97f07293-c6ac-4f6f-8a98-34367da5f27b
-- title:
--   Definitions of NormalElement: A normal element from primitive Frobenius projections
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.NormalElement` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # A normal element from primitive Frobenius projections
--
--   **Definitions** (5): `MIPRE.SAT.firstNonzero` (Deterministically select the first nonzero element, with zero as the empty default.); `MIPRE.SAT.shoupNormalBasis` (The explicitly constructed Frobenius orbit as a basis.); `MIPRE.SAT.shoupNormalElement` (Sum the selected nonzero projected vectors, in the computed component order.); `MIPRE.SAT.shoupNormalOrbitMap` (Evaluation at the constructed element is a linear map from the cyclic algebra.); `MIPRE.SAT.shoupProjectedVector` (Scan the polynomial basis for the first nonzero image of a cyclic operator.).
--
--   **Embedded lemmas** (9): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `firstNonzero_eq_zero_iff`, `firstNonzero_property`, `instFactPrimeOfNatNat_mIPRE_5`, `shoupNormalBasis_apply`, `shoupNormalElement_linearIndependent`, `shoupNormalElement_projection`, `shoupNormalOrbitMap_injective`, `shoupProjectedVector_ne_zero`, `shoupProjectedVector_supported`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.NormalElement` (`MIPRE/Foundations/SAT/NormalElement.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 104 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/NormalElement.lean; blueprint lem:effective-normal-element

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/NormalElement.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Trace.Basic
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTrace
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixInverse
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySquareRoot
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculant
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra_B
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGCD
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFactorization
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCyclotomicSeed
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySubstitution
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueCorrectness
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTraceBits
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientTranslation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOddPrimeProgram
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerTrace
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreier
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierTower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimality
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimePower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeDecomposition
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerDispatch
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleAssembly
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleConstructor
import Definitions.Def_MIPRE_Foundations_LowDegree_Shoup
import Definitions.Def_MIPRE_Foundations_LowDegree_ShoupCoefficients
import Definitions.Def_MIPRE_Foundations_SAT_QuotientField
import Definitions.Def_MIPRE_Foundations_SAT_FieldTrace
import Definitions.Def_MIPRE_Foundations_SAT_FieldTrace_B
import Definitions.Def_MIPRE_Foundations_SAT_FieldCoordinates
import Definitions.Def_MIPRE_Foundations_SAT_TraceGram
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDual
import Definitions.Def_MIPRE_Foundations_LowDegree_NormalBasis
import Definitions.Def_MIPRE_Foundations_SAT_NormalGram
import Definitions.Def_MIPRE_Foundations_SAT_FrobeniusAction
import Theorems.Thm_MIPRE_LowDegree_PrimitiveBinaryComponent_exists_mul_eq
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_groupComponents_family
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_groupComponents_primitive
import Theorems.Thm_MIPRE_LowDegree_mul_self_bijective
import Theorems.Thm_MIPRE_SAT_shoupBinField_finrank
import Theorems.Thm_MIPRE_SAT_shoupFrobeniusAction_apply
import Theorems.Thm_MIPRE_SAT_shoupFrobeniusAction_exists_basis_image

/-! # A normal element from primitive Frobenius projections -/

noncomputable section

namespace MIPRE.SAT

open Cost LowDegree LowDegree.BinaryLinear

local instance instFactPrimeOfNatNat_mIPRE_5 : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Deterministically select the first nonzero element, with zero as the empty default. -/
def firstNonzero {E : Type*} [Zero E] [DecidableEq E] : List E → E
  | [] => 0
  | a :: l => if a = 0 then firstNonzero l else a

theorem firstNonzero_eq_zero_iff {E : Type*} [Zero E] [DecidableEq E] (l : List E) :
    firstNonzero l = 0 ↔ ∀ a ∈ l, a = 0 := by
  induction l with
  | nil => simp [firstNonzero]
  | cons a l ih => by_cases h : a = 0 <;> simp [firstNonzero, h, ih]

theorem firstNonzero_property {E : Type*} [Zero E] [DecidableEq E]
    (P : E → Prop) (hzero : P 0) (l : List E) (hl : ∀ a ∈ l, P a) : P (firstNonzero l) := by
  induction l with
  | nil => exact hzero
  | cons a l ih =>
    unfold firstNonzero
    split
    · exact ih (fun b hb => hl b (by simp [hb]))
    · exact hl a (by simp)

/-- Scan the polynomial basis for the first nonzero image of a cyclic operator. -/
def shoupProjectedVector (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (e : AddMonoidAlgebra (ZMod 2) (Fin k)) : (shoupBinField k hk).carrier :=
  firstNonzero (List.ofFn (fun j => shoupFrobeniusAction k hk e (shoupPowerBasis k hk j)))

theorem shoupProjectedVector_ne_zero (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (e : AddMonoidAlgebra (ZMod 2) (Fin k)) (he : e ≠ 0) :
    shoupProjectedVector k hk e ≠ 0 := by
  intro hz
  obtain ⟨j, hj⟩ := shoupFrobeniusAction_exists_basis_image k hk e he
  exact hj ((firstNonzero_eq_zero_iff _).mp hz _ (List.mem_ofFn.mpr ⟨j, rfl⟩))

theorem shoupProjectedVector_supported (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (e : AddMonoidAlgebra (ZMod 2) (Fin k)) (he : e * e = e) :
    shoupFrobeniusAction k hk e (shoupProjectedVector k hk e) = shoupProjectedVector k hk e := by
  apply firstNonzero_property (fun a => shoupFrobeniusAction k hk e a = a) (map_zero _) _
  intro a ha
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
  change (shoupFrobeniusAction k hk e * shoupFrobeniusAction k hk e) _ = _
  rw [← map_mul, he]

/-- Sum the selected nonzero projected vectors, in the computed component order. -/
def shoupNormalElement (k : ℕ) (hk : 1 ≤ k) [NeZero k] : (shoupBinField k hk).carrier :=
  ∑ i : Fin (groupComponents k).length, shoupProjectedVector k hk ((groupComponents k).get i)

theorem shoupNormalElement_projection (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (j : Fin (groupComponents k).length) :
    shoupFrobeniusAction k hk ((groupComponents k).get j) (shoupNormalElement k hk) =
      shoupProjectedVector k hk ((groupComponents k).get j) := by
  let l := groupComponents k
  have hl := groupComponents_family k
  have ho (i : Fin l.length) (hij : i ≠ j) : l.get j * l.get i = 0 := by
    rcases lt_or_gt_of_ne hij with h | h
    · rw [mul_comm]
      exact hl.orthogonal.rel_get_of_lt h
    · exact hl.orthogonal.rel_get_of_lt h
  have hx (i : Fin l.length) :
      shoupFrobeniusAction k hk (l.get j) (shoupProjectedVector k hk (l.get i)) =
        if i = j then shoupProjectedVector k hk (l.get j) else 0 := by
    by_cases hij : i = j
    · subst i
      rw [if_pos rfl]
      exact shoupProjectedVector_supported k hk _ (hl.idempotent _ (List.get_mem _ _))
    · rw [if_neg hij, ← shoupProjectedVector_supported k hk (l.get i)
        (hl.idempotent _ (List.get_mem _ _))]
      change (shoupFrobeniusAction k hk (l.get j) * shoupFrobeniusAction k hk (l.get i)) _ = 0
      rw [← map_mul, ho i hij, map_zero, LinearMap.zero_apply]
  change shoupFrobeniusAction k hk (l.get j) (∑ i, shoupProjectedVector k hk (l.get i)) = _
  rw [map_sum]
  simp only [hx, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

/-- Evaluation at the constructed element is a linear map from the cyclic algebra. -/
def shoupNormalOrbitMap (k : ℕ) (hk : 1 ≤ k) [NeZero k] :
    AddMonoidAlgebra (ZMod 2) (Fin k) →ₗ[ZMod 2] (shoupBinField k hk).carrier where
  toFun r := shoupFrobeniusAction k hk r (shoupNormalElement k hk)
  map_add' r s := by simp
  map_smul' c r := by simp

/-- No nonzero cyclic operator kills the sum: each primitive component has its own nonzero image. -/
theorem shoupNormalOrbitMap_injective (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) :
    Function.Injective (shoupNormalOrbitMap k hk) := by
  haveI : Finite (AddMonoidAlgebra (ZMod 2) (Fin k)) :=
    Finite.of_injective _ (groupCoordinates k).injective
  apply (injective_iff_map_eq_zero (shoupNormalOrbitMap k hk)).mpr
  intro r hr
  have hsq : Function.Bijective (fun x : AddMonoidAlgebra (ZMod 2) (Fin k) => x * x) :=
    mul_self_bijective (ZMod.charP 2) (by simpa using hodd)
  have he (i : Fin (groupComponents k).length) : (groupComponents k).get i * r = 0 := by
    let e := (groupComponents k).get i
    have hem := List.get_mem (groupComponents k) i
    have hep := groupComponents_primitive k e hem
    by_contra hne
    obtain ⟨y, hy⟩ := hep.exists_mul_eq hsq (e * r) hne (by rw [← mul_assoc, hep.2.1])
    have h : shoupFrobeniusAction k hk e (shoupNormalElement k hk) = 0 := by
      calc
        shoupFrobeniusAction k hk e (shoupNormalElement k hk) =
            shoupFrobeniusAction k hk ((e * r) * y) (shoupNormalElement k hk) := by rw [hy]
        _ = shoupFrobeniusAction k hk (e * y)
            (shoupFrobeniusAction k hk r (shoupNormalElement k hk)) := by
          rw [show (e * r) * y = (e * y) * r by ring, map_mul]
          rfl
        _ = 0 := by change shoupFrobeniusAction k hk (e * y) (shoupNormalOrbitMap k hk r) = 0
                    rw [hr, map_zero]
    rw [shoupNormalElement_projection] at h
    exact shoupProjectedVector_ne_zero k hk e hep.1 h
  have hs : (∑ i : Fin (groupComponents k).length, (groupComponents k).get i) = 1 := by
    simpa using (groupComponents_family k).sum_eq_one
  calc
    r = (∑ i : Fin (groupComponents k).length, (groupComponents k).get i) * r := by rw [hs, one_mul]
    _ = 0 := by rw [Finset.sum_mul]; simp only [he, Finset.sum_const_zero]

/-- The orbit of the computed normal element is linearly independent. -/
theorem shoupNormalElement_linearIndependent (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) :
    LinearIndependent (ZMod 2) (fun i : Fin k => shoupNormalElement k hk ^ (2 ^ i.val)) := by
  have h := (Module.Basis.ofEquivFun (groupCoordinates k)).linearIndependent.map'
    (shoupNormalOrbitMap k hk) (LinearMap.ker_eq_bot.mpr (shoupNormalOrbitMap_injective k hk hodd))
  suffices he : (fun i : Fin k => shoupNormalElement k hk ^ (2 ^ i.val)) =
      (shoupNormalOrbitMap k hk) ∘ (Module.Basis.ofEquivFun (groupCoordinates k)) by
    rw [he]
    exact h
  funext i
  simp only [Function.comp_apply, Module.Basis.coe_ofEquivFun]
  change _ = shoupFrobeniusAction k hk ((groupCoordinates k).symm (Pi.single i 1)) _
  rw [shoupFrobeniusAction_apply]
  simp [groupCoordinates_symm_apply]

/-- The explicitly constructed Frobenius orbit as a basis. -/
def shoupNormalBasis (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) :
    Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier :=
  basisOfLinearIndependentOfCardEqFinrank (shoupNormalElement_linearIndependent k hk hodd)
    (by simp [shoupBinField_finrank k hk])

@[simp] theorem shoupNormalBasis_apply (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (i : Fin k) : shoupNormalBasis k hk hodd i = shoupNormalElement k hk ^ (2 ^ i.val) := by
  rw [shoupNormalBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

end MIPRE.SAT

end


