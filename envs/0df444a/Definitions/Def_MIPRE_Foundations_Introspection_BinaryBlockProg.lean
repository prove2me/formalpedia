-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_BinaryBlockProg
-- name    : MIPRE_Foundations_Introspection_BinaryBlockProg
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T05:31:39.911007+00:00
-- url     : https://prove2.me/theorems/648f4ec3-47f3-48b6-aa8b-ccc8bb7a02e4
-- title:
--   Definitions of BinaryBlockProg: Executable binary field blocks A bounded scan splits an explicitly supplied number of fixed-width blocks
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.BinaryBlockProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Executable binary field blocks. A bounded scan splits an explicitly supplied number of fixed-width blocks. Short inputs produce short or empty final blocks and long suffixes are ignored; the program is total on all inputs. Canonical-width inputs split and flatten exactly. Combined conversion interprets the flat CL vector in the constructed self-dual basis and returns the field arithmetic's canonical Shoup rows.
--
--   **Definitions** (4): `MIPRE.Introspection.BinaryBlock.flattenProg` (Concatenation is an actual ambient program with a polynomial bound.); `MIPRE.Introspection.BinaryBlock.splitBlocks`; `MIPRE.Introspection.BinaryBlock.splitBlocksProg` (Inputs are number of blocks, block width, and flat bits, in that order.); `_private.MIPRE.Foundations.Introspection.BinaryBlockProg.0.MIPRE.Introspection.BinaryBlock.splitStep`.
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `splitStep_apply`, `splitStep_fold`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.BinaryBlockProg` (`MIPRE/Foundations/Introspection/BinaryBlockProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 89 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/BinaryBlockProg.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/BinaryBlockProg.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_SAT_FieldCoordinates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFold
import Definitions.Def_MIPRE_Foundations_SAT_NormalElementProg

/-! # Executable binary field blocks

A bounded scan splits an explicitly supplied number of fixed-width blocks.
Short inputs produce short or empty final blocks and long suffixes are ignored;
the program is total on all inputs. Canonical-width inputs split and flatten
exactly. Combined conversion interprets the flat CL vector in the constructed
self-dual basis and returns the field arithmetic's canonical Shoup rows.
-/

noncomputable section
namespace MIPRE.Introspection.BinaryBlock
open Cost Cost.PolyTimeFun Polynomial SAT LowDegree.BinaryLinear

def splitBlocks : ℕ → ℕ → BitStr → List BitStr
  | 0, _, _ => []
  | n + 1, k, v => v.take k :: splitBlocks n k (v.drop k)

def splitStep : PolyTimeFun ((BitStr × List BitStr) × Unary) (BitStr × List BitStr) :=
  (drop.comp ((fst.comp fst).pair snd)).pair
    (cons (take.comp ((fst.comp fst).pair snd)) (snd.comp fst))

theorem splitStep_apply (v : BitStr) (vs : List BitStr) (k : Unary) :
    splitStep ((v, vs), k) = (v.drop k.length, v.take k.length :: vs) := rfl

theorem splitStep_fold (n : ℕ) (k : Unary) (v : BitStr) (vs : List BitStr) :
    ((List.replicate n k).foldl splitStep.step (v, vs)).2 =
      (splitBlocks n k.length v).reverse ++ vs := by
  induction n generalizing v vs with
  | zero => simp [splitBlocks]
  | succ n ih =>
    change ((List.replicate n k).foldl splitStep.step
      (v.drop k.length, v.take k.length :: vs)).2 = _
    rw [ih]
    simp [splitBlocks, List.append_assoc]

/-- Inputs are number of blocks, block width, and flat bits, in that order. -/
def splitBlocksProg : PolyTimeFun (Unary × Unary × BitStr) (List BitStr) :=
  let scan := foldlAdd splitStep 2 (by
    rintro ⟨v, vs⟩ k
    have he := esize_list_append (v.take k.length) (v.drop k.length)
    rw [List.take_append_drop] at he
    simp only [splitStep_apply, esize_prod, esize_list_cons, eval_ofNat]
    omega)
  congr ((PolyTimeFun.reverse.comp snd).comp (scan.comp
    ((replicate.comp (fst.pair (fst.comp snd))).pair ((snd.comp snd).pair (const [])))))
    (fun p => splitBlocks p.1.length p.2.1.length p.2.2) (by
      rintro ⟨n, k, v⟩
      change (((List.replicate n.length k).foldl splitStep.step (v, [])).2).reverse = _
      rw [splitStep_fold, List.append_nil, List.reverse_reverse])

/-- Concatenation is an actual ambient program with a polynomial bound. -/
def flattenProg : PolyTimeFun (List BitStr) BitStr :=
  congr ((foldlAdd append X (by
    intro l r
    have h := esize_list_append l r
    simp only [append_apply, eval_X]
    omega)).comp ((PolyTimeFun.id _).pair (const []))) List.flatten (by
      intro l
      change l.foldl (fun a b => a ++ b) [] = l.flatten
      simpa using (List.foldl_append_eq_append (l := l) (l' := []) (f := fun b => b)))

end MIPRE.Introspection.BinaryBlock
end


