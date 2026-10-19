-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_FieldCoordinates
-- name    : MIPRE_Foundations_SAT_FieldCoordinates
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T05:29:05.813361+00:00
-- url     : https://prove2.me/theorems/088a8dca-4f75-4484-9d22-c2de084fac40
-- title:
--   Definitions of FieldCoordinates: Canonical binary linear coordinates for the effective field
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.FieldCoordinates` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Canonical binary linear coordinates for the effective field
--
--   **Definitions** (2): `MIPRE.SAT.shoupCoordinateEquiv` (The canonical bit representation is also a binary linear equivalence.); `MIPRE.SAT.shoupPowerBasis` (The basis associated to the actual polynomial-time field representation.).
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `vectorBits_vectorValue`, `instFactPrimeOfNatNat_mIPRE_1`, `shoupBinField_ofBits`, `shoupCoordinateEquiv_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.FieldCoordinates` (`MIPRE/Foundations/SAT/FieldCoordinates.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 86 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/FieldCoordinates.lean; blueprint lem:effective-field-matrices

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/FieldCoordinates.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPower
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
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
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_binary_eq_zero_or_one
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_xorBits_vectorBits
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_xor
import Theorems.Thm_MIPRE_LowDegree_shoupIrreducible_irreducible
import Theorems.Thm_MIPRE_LowDegree_shoupIrreducible_monic
import Theorems.Thm_MIPRE_LowDegree_shoupIrreducible_natDegree
import Theorems.Thm_MIPRE_SAT_quotientBinField_ofBits
import Theorems.Thm_MIPRE_SAT_shoupBinField_charP
import Theorems.Thm_MIPRE_SAT_shoupBinField_toBits_ofBits

attribute [instance] MIPRE.SAT.shoupBinField_charP

/-! # Canonical binary linear coordinates for the effective field -/

noncomputable section

namespace MIPRE.LowDegree.BinaryLinear

/-- Decoding and re-encoding a vector of the prescribed width is exact. -/
theorem vectorBits_vectorValue (n : ℕ) (v : Cost.BitStr) (hv : v.length = n) :
    vectorBits (vectorValue n v) = v := by
  apply List.ext_getElem
  · simp [vectorBits, hv]
  · intro i hi hj
    simp [vectorBits, vectorValue, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj]

end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.SAT

open Cost LowDegree LowDegree.BinaryPolynomial LowDegree.BinaryLinear

local instance instFactPrimeOfNatNat_mIPRE_1 : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Correct-width decoding in the Shoup model is evaluation at its root. -/
theorem shoupBinField_ofBits (k : ℕ) (hk : 1 ≤ k) (v : BitStr) (hv : v.length = k) :
    (shoupBinField k hk).ofBits v = evalBits (shoupRoot k hk) v := by
  letI : Fact (Irreducible (polyOfBits (shoupIrreducible (unary k)))) :=
    ⟨shoupIrreducible_irreducible k hk⟩
  exact quotientBinField_ofBits _ (shoupIrreducible_monic k hk) v
    (hv.trans (shoupIrreducible_natDegree k hk).symm)

/-- The canonical bit representation is also a binary linear equivalence. -/
def shoupCoordinateEquiv (k : ℕ) (hk : 1 ≤ k) :
    (shoupBinField k hk).carrier ≃ₗ[ZMod 2] (Fin k → ZMod 2) :=
  (show (Fin k → ZMod 2) ≃ₗ[ZMod 2] (shoupBinField k hk).carrier from
    { toFun := fun v => (shoupBinField k hk).ofBits (vectorBits v)
      invFun := fun a => vectorValue k ((shoupBinField k hk).toBits a)
      left_inv := fun v => by
        dsimp only
        rw [shoupBinField_toBits_ofBits k hk (vectorBits v) (by simp [vectorBits]),
          vectorValue_vectorBits]
      right_inv := fun a => by
        dsimp only
        rw [vectorBits_vectorValue k _ ((shoupBinField k hk).length_toBits a)]
        exact (shoupBinField k hk).ofBits_toBits a
      map_add' := fun v w => by
        rw [← xorBits_vectorBits]
        rw [shoupBinField_ofBits k hk _ (by simp [length_xorBits, vectorBits]),
          shoupBinField_ofBits k hk (vectorBits v) (by simp [vectorBits]),
          shoupBinField_ofBits k hk (vectorBits w) (by simp [vectorBits])]
        exact evalBits_xor _ _ _ (by simp [vectorBits])
      map_smul' := fun c v => by
        rcases binary_eq_zero_or_one c with rfl | rfl
        · simp only [zero_smul, RingHom.id_apply]
          rw [shoupBinField_ofBits k hk (vectorBits 0) (by simp [vectorBits])]
          have he : vectorBits (0 : Fin k → ZMod 2) = BinaryPolynomial.zeroBits (vectorBits v) := by
            apply List.ext_getElem
            · simp [vectorBits, BinaryPolynomial.length_zeroBits]
            · intro i hi hj
              simp [vectorBits, bit, BinaryPolynomial.zeroBits]
          rw [he, BinaryPolynomial.evalBits_zeroBits]
        · simp }).symm

@[simp] theorem shoupCoordinateEquiv_apply (k : ℕ) (hk : 1 ≤ k)
    (a : (shoupBinField k hk).carrier) :
    shoupCoordinateEquiv k hk a = vectorValue k ((shoupBinField k hk).toBits a) := rfl

/-- The basis associated to the actual polynomial-time field representation. -/
def shoupPowerBasis (k : ℕ) (hk : 1 ≤ k) :
    Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier :=
  Module.Basis.ofEquivFun (shoupCoordinateEquiv k hk)

end MIPRE.SAT

end


