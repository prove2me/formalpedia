-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleAssembly
-- name    : MIPRE_Foundations_LowDegree_BinaryIrreducibleAssembly
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:17:31.722459+00:00
-- url     : https://prove2.me/theorems/2fed37c8-c29b-4269-8c5e-c44fbda4d510
-- title:
--   Definitions of BinaryIrreducibleAssembly: A globally bounded assembly of coprime prime-power irreducibles
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryIrreducibleAssembly` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # A globally bounded assembly of coprime prime-power irreducibles
--
--   **Definitions** (5): `MIPRE.LowDegree.BinaryPolynomial.AssemblyState` (The unary target-degree cap and the current monic lower coefficients.); `MIPRE.LowDegree.BinaryPolynomial.assembleBitsProg` (One uniform program assembles the supplied polynomial list with a global width cap.); `MIPRE.LowDegree.BinaryPolynomial.assemblyStep` (Every step clips its new modulus to the original unary target-degree cap.); `MIPRE.LowDegree.BinaryPolynomial.composedLowerBits` (Lower coefficients of the normalized composed-sum polynomial.); `_private.MIPRE.Foundations.LowDegree.BinaryIrreducibleAssembly.0.MIPRE.LowDegree.BinaryPolynomial.assemblyStepProg`.
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `fold_assemblyStep_shape`, `assemblyStepProg_apply`, `assemblyStep_bounded`, `degree_prod_pos`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryIrreducibleAssembly` (`MIPRE/Foundations/LowDegree/BinaryIrreducibleAssembly.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 68 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryIrreducibleAssembly.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryIrreducibleAssembly.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Fin
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
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
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

/-! # A globally bounded assembly of coprime prime-power irreducibles -/

noncomputable section

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial BinaryQuotient DegreeArithmetic

/-- Lower coefficients of the normalized composed-sum polynomial. -/
def composedLowerBits (p g : BitStr) : BitStr :=
  (normalizeBits (composedSumBits p g)).dropLast

/-- The unary target-degree cap and the current monic lower coefficients. -/
abbrev AssemblyState := Unary × BitStr

/-- Every step clips its new modulus to the original unary target-degree cap. -/
def assemblyStep (s : AssemblyState) (g : BitStr) : AssemblyState :=
  (s.1, (composedLowerBits s.2 g).take s.1.length)

/-- No raw fold state can exceed its initial width or the supplied cap. -/
theorem fold_assemblyStep_shape (l : List BitStr) (s : AssemblyState) :
    (l.foldl assemblyStep s).1 = s.1 ∧
    (l.foldl assemblyStep s).2.length ≤ max s.2.length s.1.length := by
  induction l generalizing s with
  | nil => exact ⟨rfl, le_max_left _ _⟩
  | cons g l ih =>
    have h := ih (assemblyStep s g)
    refine ⟨h.1, h.2.trans ?_⟩
    change max ((composedLowerBits s.2 g).take s.1.length).length s.1.length ≤ _
    exact max_le ((List.length_take_le _ _).trans (le_max_right _ _)) (le_max_right _ _)

theorem degree_prod_pos (l : List BitStr)
    (h : ∀ g ∈ l, Irreducible (polyOfBits g)) :
    0 < (l.map (fun g => (polyOfBits g).natDegree)).prod := by
  induction l with
  | nil => simp
  | cons g l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact Nat.mul_pos (h g (by simp)).natDegree_pos (ih (fun a ha => h a (by simp [ha])))

def assemblyStepProg : PolyTimeFun (AssemblyState × BitStr) AssemblyState :=
  let cap := fst.comp fst
  let p := snd.comp fst
  cap.pair (take.comp ((dropLastBitsProg.comp (normalizeBitsProg.comp
    (composedSumBitsProg.comp (p.pair snd)))).pair cap))

theorem assemblyStepProg_apply (s : AssemblyState) (g : BitStr) :
    assemblyStepProg (s, g) = assemblyStep s g := by
  simp only [assemblyStepProg, comp_apply, pair_apply, fst_apply, snd_apply, take_apply,
    dropLastBitsProg_apply, normalizeBitsProg_apply, composedSumBitsProg_apply]
  rfl

theorem assemblyStep_bounded : FoldBounded assemblyStepProg (5 * X + 5) := by
  intro l s pre post _
  have hstep : assemblyStepProg.step = assemblyStep := by
    funext a g
    exact assemblyStepProg_apply a g
  change esize (pre.foldl assemblyStepProg.step s) ≤ _
  rw [hstep]
  obtain ⟨hu, hp⟩ := fold_assemblyStep_shape pre s
  have he := esize_bitStr_le (pre.foldl assemblyStep s).2
  have hp0 := length_le_esize_bitStr s.2
  have hu0 := length_le_esize_list s.1
  have hs : esize s = esize s.1 + esize s.2 + 1 := rfl
  rw [esize_prod, hu]
  simp only [esize_prod, eval_add, eval_mul, eval_ofNat, eval_X]
  omega

/-- One uniform program assembles the supplied polynomial list with a global width cap. -/
def assembleBitsProg : PolyTimeFun (List BitStr × Unary × BitStr) BitStr :=
  snd.comp (foldl assemblyStepProg (5 * X + 5) assemblyStep_bounded)

end MIPRE.LowDegree.BinaryPolynomial

end


