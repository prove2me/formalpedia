-- Prove2me | Definitions.Def_MIPRE_Background_AnswerReduction_TypedComplete
-- name    : MIPRE_Background_AnswerReduction_TypedComplete
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T05:35:41.166854+00:00
-- url     : https://prove2.me/theorems/e27f3055-3547-4af3-a927-7087fc460a88
-- title:
--   Definitions of TypedComplete: Completeness of the typed answer-reduced game Piece AR-4 of `planning/answer-reduction.md`: a value-`1` PCC strategy of…
-- statement:
--   The definitions of the module `MIPRE.Background.AnswerReduction.TypedComplete` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Completeness of the typed answer-reduced game. Piece AR-4 of `planning/answer-reduction.md`: a value-`1` PCC strategy of the input verifier gives one of the (doubled) typed answer-reduced game (`exists_typedGame_perfectPCC`), for any PCP proofs of the accepted answer pairs — the paper's completeness argument for `thm:ar` (`ld_compiler.tex`), with the PCP's completeness left as a hypothesis (`ProofGood`), discharged in `MIPRE/Background/AnswerReduction/Complete`. The strategy is the oracularized game's honest strategy (`SeededGame.oracleStrategy`, the oracularization's completeness), read…
--
--   **Definitions** (6): `MIPRE.AnswerReduction.ProofGood` (A PCP proof is good for the pair `(a, b)` at seed `x`: its first two answer polynomials encode `a` and `b`, and every point's evaluations…); `MIPRE.AnswerReduction.blockEmb` (The embedding of the `i`-th block of `m` coordinates into the `m'` of the sixth copy.); `MIPRE.AnswerReduction.hdata` (**A player's data**, from its role, the oracle half of its question and the oracularized strategy's outcome.); `MIPRE.AnswerReduction.honestQ` (**The honest answer** to a typed question, from the oracularized strategy's outcome.); `MIPRE.AnswerReduction.ofAnswer` (**An isolated player's data**: the low-degree encoding of its answer at its own copy `v`.); `MIPRE.AnswerReduction.ofProof` (**An oracle's data**, from a PCP proof: the answer polynomials, and for the sixth copy the answer polynomials read on their blocks followed…).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.AnswerReduction.TypedComplete` (`MIPRE/Background/AnswerReduction/TypedComplete.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 137 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/AnswerReduction/TypedComplete.lean; blueprint lem:ar-completeness

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/TypedComplete.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
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
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
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
import Definitions.Def_MIPRE_Background_AnswerReduction_PcpPresentation
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Background_AnswerReduction_Predicate
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularSound
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_OracularTensor
import Definitions.Def_MIPRE_Foundations_OracularComplete
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_OracularTyped
import Definitions.Def_MIPRE_Background_AnswerReduction_AnswerFormat
import Definitions.Def_MIPRE_Foundations_CL_Product
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_CL_ProductSampler
import Definitions.Def_MIPRE_Background_LIDT_PresentationQueries
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
import Definitions.Def_MIPRE_Background_AnswerReduction_Layout
import Definitions.Def_MIPRE_Background_AnswerReduction_Family
import Definitions.Def_MIPRE_Background_AnswerReduction_TypedGame
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Background_LIDT_CLHonest
import Definitions.Def_MIPRE_Background_AnswerReduction_Honest
import Definitions.Def_MIPRE_Foundations_SyncPushQ

/-!
# Completeness of the typed answer-reduced game

Piece AR-4 of `planning/answer-reduction.md`: a value-`1` PCC strategy of the input verifier gives
one of the (doubled) typed answer-reduced game (`exists_typedGame_perfectPCC`), for any PCP proofs
of the accepted answer pairs — the paper's completeness argument for `thm:ar`
(`ld_compiler.tex`), with the PCP's completeness left as a hypothesis (`ProofGood`), discharged in
`MIPRE/Background/AnswerReduction/Complete`.

The strategy is the oracularized game's honest strategy (`SeededGame.oracleStrategy`, the
oracularization's completeness), read through the question map that keeps a question's role and
its oracle half (`SyncStrategy.pushQ`), and answered honestly (`honestAns`) from data computed from
the role, the oracle half and the outcome (`hdata`):

* an oracle answering the pair `(a, b)` at seed `x` holds the PCP proof `pfOf x a b` (`ofProof`);
* an isolated player answering `a` holds the low-degree encoding of `a` at its own copy
  (`ofAnswer`), and zero elsewhere.

Two questions of positive weight are read off one seed; their oracle halves are then an
oracularized question pair of positive weight, and their PCP halves questions of one PCP vector.
There the oracularized predicate's checks are exactly the consistency `accepts_honestAns` needs.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL MIPRE.LIDT MIPRE.LowDegree SAT Pcp Cost

/-! ## The oracularized question distribution -/

/-! ## The players' data -/

variable {P : PcpParams} (hk : 1 ≤ P.k)

/-- The embedding of the `i`-th block of `m` coordinates into the `m'` of the sixth copy. -/
def blockEmb (i : Fin 5) : Fin P.m → Fin P.m' := fun j => ⟨i * P.m + j, by
  have h1 : (i : ℕ) * P.m ≤ 4 * P.m := Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp i.isLt)
  have h2 : (j : ℕ) < P.m := j.isLt
  simp only [PcpParams.m']
  omega⟩

/-- **An oracle's data**, from a PCP proof: the answer polynomials, and for the sixth copy the
answer polynomials read on their blocks followed by the constraint polynomials. -/
def ofProof (pf : PcpProof P (Fq P hk)) : HPolys P (Fq P hk) where
  g := pf.g
  c j := if h : (j : ℕ) < 5 then MvPolynomial.rename (blockEmb ⟨j, h⟩) (pf.g ⟨j, h⟩)
    else pf.c ⟨j - 5, by have := j.isLt; omega⟩

/-- **An isolated player's data**: the low-degree encoding of its answer at its own copy `v`. -/
def ofAnswer (v : Fin 5) (a : BitStr) : HPolys P (Fq P hk) where
  g j := if j = v then ldEnc (answerVec (Fq P hk) P.m a) else 0
  c _ := 0

/-- A PCP proof is good for the pair `(a, b)` at seed `x`: its first two answer polynomials encode
`a` and `b`, and every point's evaluations pass the check. -/
def ProofGood {X : Type*} (check : X → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) → Bool)
    (x : X) (a b : BitStr) (pf : PcpProof P (Fq P hk)) : Prop :=
  pf.g 0 = ldEnc (answerVec (Fq P hk) P.m a) ∧ pf.g 1 = ldEnc (answerVec (Fq P hk) P.m b) ∧
    ∀ z, check x z (fun j => MvPolynomial.eval z ((ofProof hk pf).c j)) = true

/-! ## The answer length -/

/-! ## The players' data, from the oracularized strategy's outcomes -/

section Game

variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k) {B : ℕ}
  (pfOf : (Fin (V.sampler.dim n) → 𝔽₂) → BitStr → BitStr → PcpProof P (Fq P hk))

/-- **A player's data**, from its role, the oracle half of its question and the oracularized
strategy's outcome. -/
def hdata : Role → (Fin (V.sampler.dim n) → 𝔽₂) → OAns (Verifier.Answers B) → HPolys P (Fq P hk)
  | .oracle, x, .pair a b => ofProof hk (pfOf x a.1 b.1)
  | .alice, _, .single a => ofAnswer hk 0 a.1
  | .bob, _, .single b => ofAnswer hk 1 b.1
  | _, _, _ => ⟨0, 0⟩

variable {check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) →
  (Fin (P.m' + 6) → Fq P hk) → Bool}

end Game

section Strategy

variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k) {B : ℕ}
  (pfOf : (Fin (V.sampler.dim n) → 𝔽₂) → BitStr → BitStr → PcpProof P (Fq P hk))
  [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')

/-- **The honest answer** to a typed question, from the oracularized strategy's outcome. -/
def honestQ (p : Detyping.Question ArTy (Fin (dim V n P))) (u : OAns (Verifier.Answers B)) :
    Ans P (Fq P hk) :=
  honestAns S S' (hdata V n P hk pfOf p.1.1 (oraclePart V n P p.2) u) p.1.2 (pcpPart V n P hk p.2)

end Strategy

end MIPRE.AnswerReduction

end


