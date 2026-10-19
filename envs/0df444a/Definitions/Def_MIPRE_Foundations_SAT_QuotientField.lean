-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_QuotientField
-- name    : MIPRE_Foundations_SAT_QuotientField
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T04:55:20.591014+00:00
-- url     : https://prove2.me/theorems/2a904df4-bfdc-4200-ad35-7995ea043d3b
-- title:
--   Definitions of QuotientField: Binary fields represented in the polynomial power basis Unlike an arbitrary basis of a Galois field, the power basis of…
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.QuotientField` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Binary fields represented in the polynomial power basis. Unlike an arbitrary basis of a Galois field, the power basis of `F₂[X]/(f)` connects directly to the uniform coefficient-list programs. This is the field representation needed for the classical PCP's arithmetic. A self-dual normal representation and its change-of-basis algorithm remain separate constructions.
--
--   **Definitions** (7): `MIPRE.SAT.quotientBinField` (A binary field with coefficient bits in the power basis of a monic irreducible polynomial.); `MIPRE.SAT.shoupAdmissibleField` (The admissible field family with exactly the domain required by `PcpDecider.fld`.); `MIPRE.SAT.shoupBinField` (A field of size `2^k` in the polynomial basis supplied by Shoup's algorithm.); `MIPRE.SAT.shoupFieldModel` (Shoup's concrete quotient model, before transporting the degree equality.); `MIPRE.SAT.shoupMulProg` (Compute the modulus from unary `k`, then multiply the two coefficient vectors.); `MIPRE.SAT.shoupRoot` (The distinguished root in the explicit Shoup field carrier.); `_private.MIPRE.Foundations.SAT.QuotientField.0.MIPRE.SAT.bitOfCoeff`.
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `instFactPrimeOfNatNat_mIPRE`, `bitOfCoeff_ofBool`, `ofBool_bitOfCoeff`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.QuotientField` (`MIPRE/Foundations/SAT/QuotientField.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 83 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/QuotientField.lean; blueprint lem:effective-binary-field-arithmetic

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/QuotientField.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPRE_LowDegree_shoupIrreducible_irreducible
import Theorems.Thm_MIPRE_LowDegree_shoupIrreducible_monic
import Theorems.Thm_MIPRE_LowDegree_shoupIrreducible_natDegree

/-!
# Binary fields represented in the polynomial power basis

Unlike an arbitrary basis of a Galois field, the power basis of `F₂[X]/(f)`
connects directly to the uniform coefficient-list programs. This is the field
representation needed for the classical PCP's arithmetic. A self-dual normal
representation and its change-of-basis algorithm remain separate constructions.
-/

noncomputable section

namespace MIPRE.SAT

open Finset LowDegree LowDegree.BinaryPolynomial Cost

local instance instFactPrimeOfNatNat_mIPRE : Fact (Nat.Prime 2) := ⟨by decide⟩

def bitOfCoeff (z : ZMod 2) : Bool := decide (z = 1)

theorem ofBool_bitOfCoeff (z : ZMod 2) : ofBool (bitOfCoeff z) = z := by
  revert z
  decide

theorem bitOfCoeff_ofBool (b : Bool) : bitOfCoeff (ofBool b) = b := by
  cases b <;> decide

section Quotient

variable (f : Polynomial (ZMod 2)) (hf : f.Monic) [Fact (Irreducible f)]

/-- A binary field with coefficient bits in the power basis of a monic irreducible
polynomial. The basis is specified, rather than chosen by abstract finite-field existence. -/
def quotientBinField : BinField f.natDegree :=
  let b : Module.Basis (Fin f.natDegree) (ZMod 2) (AdjoinRoot f) :=
    AdjoinRoot.powerBasisAux' hf
  letI : Fintype (AdjoinRoot f) :=
    Fintype.ofEquiv (Fin f.natDegree → ZMod 2) b.equivFun.symm.toEquiv
  { carrier := AdjoinRoot f
    instField := inferInstance
    instFintype := inferInstance
    instDecidableEq := inferInstance
    card_carrier := by
      rw [Fintype.card_congr b.equivFun.toEquiv]
      simp
    toBits := fun x => List.ofFn fun i => bitOfCoeff (b.repr x i)
    ofBits := fun l => ∑ i : Fin f.natDegree, (ofBool (l.getD i false) : ZMod 2) • b i
    length_toBits := fun _ => List.length_ofFn
    ofBits_toBits := fun x => by
      refine (Finset.sum_congr rfl fun i _ => ?_).trans (b.sum_repr x)
      congr 1
      rw [show (List.ofFn fun i => bitOfCoeff (b.repr x i)).getD (i : ℕ) false =
          bitOfCoeff (b.repr x i) from by simp, ofBool_bitOfCoeff] }

end Quotient

/-- Shoup's concrete quotient model, before transporting the degree equality. -/
def shoupFieldModel (k : ℕ) (hk : 1 ≤ k) :
    BinField (polyOfBits (shoupIrreducible (unary k))).natDegree :=
  letI : Fact (Irreducible (polyOfBits (shoupIrreducible (unary k)))) :=
    ⟨shoupIrreducible_irreducible k hk⟩
  quotientBinField _ (shoupIrreducible_monic k hk)

/-- A field of size `2^k` in the polynomial basis supplied by Shoup's algorithm. -/
def shoupBinField (k : ℕ) (hk : 1 ≤ k) : BinField k :=
  let E := shoupFieldModel k hk
  { carrier := E.carrier
    instField := E.instField
    instFintype := E.instFintype
    instDecidableEq := E.instDecidableEq
    card_carrier := by rw [E.card_carrier, shoupIrreducible_natDegree k hk]
    toBits := E.toBits
    ofBits := E.ofBits
    length_toBits := fun a => (E.length_toBits a).trans (shoupIrreducible_natDegree k hk)
    ofBits_toBits := E.ofBits_toBits }

/-- The admissible field family with exactly the domain required by `PcpDecider.fld`. -/
def shoupAdmissibleField (k : ℕ) (hk : Odd k) : BinField k :=
  shoupBinField k (by obtain ⟨r, hr⟩ := hk; omega)

/-- The distinguished root in the explicit Shoup field carrier. -/
def shoupRoot (k : ℕ) (hk : 1 ≤ k) : (shoupBinField k hk).carrier :=
  AdjoinRoot.root (polyOfBits (shoupIrreducible (unary k)))

/-- Compute the modulus from unary `k`, then multiply the two coefficient vectors.
This is one uniform ambient program, with a polynomial bound in its input size. -/
def shoupMulProg : PolyTimeFun (Unary × BitStr × BitStr) BitStr :=
  mulReduceProg.comp ((shoupLowerCoeffs.comp PolyTimeFun.fst).pair PolyTimeFun.snd)

end MIPRE.SAT

end


