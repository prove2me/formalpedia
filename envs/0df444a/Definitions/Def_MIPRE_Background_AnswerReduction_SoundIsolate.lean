-- Prove2me | Definitions.Def_MIPRE_Background_AnswerReduction_SoundIsolate
-- name    : MIPRE_Background_AnswerReduction_SoundIsolate
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T05:35:48.740329+00:00
-- url     : https://prove2.me/theorems/ce60c5c3-15d6-4ae4-af17-7201b89c0317
-- title:
--   Definitions of SoundIsolate: Soundness of answer reduction: the per-seed low-degree games Piece AR-5b of `planning/answer-reduction.md`…
-- statement:
--   The definitions of the module `MIPRE.Background.AnswerReduction.SoundIsolate` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Soundness of answer reduction: the per-seed low-degree games. Piece AR-5b of `planning/answer-reduction.md` (`claim:ar-3`, `claim:ar-4`, `def:ar-seed-index`). A strategy for the typed answer-reduced game, restricted to one copy of the low-degree test at a role pair where that copy is tested and to one seed of the input sampler, is a strategy for the seeded CL test of the copy's parameters (`copyStrategy`): its question maps a CL question to the typed question whose PCP half the copy's presentation computes (`Regs.embedQ`) and whose oracle half the seed's role family gives, and its answers are…
--
--   **Definitions** (11): `MIPRE.AnswerReduction.arQ1` (**The typed question of a CL question** of copy `i ≤ 5`, at role `r` and oracle half `x`.); `MIPRE.AnswerReduction.arQ6` (**The typed question of a CL question** of the sixth copy, at role `r` and oracle half `x`.); `MIPRE.AnswerReduction.copyFail` (`T`'s failure at the typed question pair of sample `sm` at oracle half `y`.); `MIPRE.AnswerReduction.copyFail6` (`T`'s failure at the typed question pair of sample `sm` of the sixth copy at oracle half `y`.); `MIPRE.AnswerReduction.copyStrategy` (**The per-seed low-degree strategy** of copy `i ≤ 5` at role `r` and oracle half `y`: the typed strategy played through `arQ1` and…); `MIPRE.AnswerReduction.copyStrategy6` (**The per-seed simultaneous low-degree strategy** of the sixth copy at oracle half `y`: the typed strategy played through `arQ6` and…); `MIPRE.AnswerReduction.edgeFail` (`T`'s failure at the typed question pair of the type pair `uv`, on the vector whose oracle half is `x` and whose PCP half is `w`.); `MIPRE.AnswerReduction.pcpBits` (The bits of a vector of `V^pcp`, in the numbering of a question's PCP half.); `MIPRE.AnswerReduction.pcpBitsEquiv` (The bits of a vector of `V^pcp`, as an equivalence.); `MIPRE.AnswerReduction.readAns1` (**An answer read as an answer of copy `i`'s test**: parsed at the question's type, then read by `ans1`; a failed parse reads as the zero…); and -24 more.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.AnswerReduction.SoundIsolate` (`MIPRE/Background/AnswerReduction/SoundIsolate.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 138 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/AnswerReduction/SoundIsolate.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/SoundIsolate.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Background_LIDT_PresentationEmbed
import Definitions.Def_MIPRE_Background_AnswerReduction_SoundCopy

/-!
# Soundness of answer reduction: the per-seed low-degree games

Piece AR-5b of `planning/answer-reduction.md` (`claim:ar-3`, `claim:ar-4`, `def:ar-seed-index`).
A strategy for the typed answer-reduced game, restricted to one copy of the low-degree test at a
role pair where that copy is tested and to one seed of the input sampler, is a strategy for the
seeded CL test of the copy's parameters (`copyStrategy`): its question maps a CL question to the
typed question whose PCP half the copy's presentation computes (`Regs.embedQ`) and whose oracle
half the seed's role family gives, and its answers are parsed and read as answers of the copy's
test. The seeds are indexed by the full seed of the input sampler, as the blueprint's
`def:ar-seed-index` asks.

The per-seed failures average to at most a constant times the typed failure
(`sum_one_sub_value_copyStrategy_le`): the copy's nine type pairs are a fixed fraction of the
typed game's, and the copy's registers of a uniform PCP vector carry a uniform sample
(`Regs.sum_sampleOf`).
-/

noncomputable section

namespace MIPRE.LIDT.CL

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
  (hm : m ∣ Fintype.card F)

end MIPRE.LIDT.CL

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL MIPRE.CL.CLFun MIPRE.LIDT SAT Pcp Cost

variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)

/-- The bits of a vector of `V^pcp`, in the numbering of a question's PCP half. -/
def pcpBits (w : Coord P → Fq P hk) : Fin (Pcp.pcpDim P * P.k) → 𝔽₂ :=
  reindexEquiv (Pcp.bitIndex P P.k) (downsizeEquiv (basis P hk) w)

variable [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
  (check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) →
    Bool) (B : ℕ)

/-- **The typed question of a CL question** of copy `i ≤ 5`, at role `r` and oracle half `x`. -/
def arQ1 (r : Role) (i : Fin 5) (x : Fin (V.sampler.dim n) → 𝔽₂)
    (q : LIDT.CL.Question (Fq P hk) P.m) : Detyping.Question ArTy (Fin (dim V n P)) :=
  ((r, (i.castSucc, q.ty)), Fin.append x (pcpBits P hk ((regs P i).embedQ S q)))

/-- **An answer read as an answer of copy `i`'s test**: parsed at the question's type, then read by
`ans1`; a failed parse reads as the zero point answer. -/
def readAns1 (i : Fin 5) (q : LIDT.CL.Question (Fq P hk) P.m) (a : Verifier.Answers B) :
    LIDT.CL.Answer (Fq P hk) P.m dPcp 1 :=
  ans1 ((parse (fld P hk) (i.castSucc, q.ty) a.1).getD (.inl (.values 0)))

/-- **The per-seed low-degree strategy** of copy `i ≤ 5` at role `r` and oracle half `y`: the
typed strategy played through `arQ1` and `readAns1`, both players at role `r`. At the seed `x₀` of
the input sampler the oracle half is `(roleFamily L r).eval x₀`: the seed itself for an oracle,
the original player's question for an isolated player, whose measurements see nothing else. -/
def copyStrategy (T : TensorProductStrategy (typedGame V n P hk S S' check B)) (r : Role)
    (i : Fin 5) (y : Fin (V.sampler.dim n) → 𝔽₂) :
    TensorProductStrategy (LIDT.CL.clGame (d := dPcp) (ldc := 1) hm) :=
  T.adapt _ (arQ1 V n P hk S r i y) (arQ1 V n P hk S r i y) (readAns1 P hk B i)
    (readAns1 P hk B i)

/-- `T`'s failure at the typed question pair of sample `sm` at oracle half `y`. -/
def copyFail (T : TensorProductStrategy (typedGame V n P hk S S' check B)) (r : Role) (i : Fin 5)
    (y : Fin (V.sampler.dim n) → 𝔽₂) (sm : LIDT.CL.Sample (Fq P hk) P.m) : ℝ :=
  T.failAt (arQ1 V n P hk S r i y (sm.question hm sm.tyA))
    (arQ1 V n P hk S r i y (sm.question hm sm.tyB))

omit [NeZero P.m] in
/-- The bits of a vector of `V^pcp`, as an equivalence. -/
def pcpBitsEquiv : (Coord P → Fq P hk) ≃ (Fin (Pcp.pcpDim P * P.k) → 𝔽₂) :=
  ((downsizeEquiv (basis P hk)).trans (reindexEquiv (Pcp.bitIndex P P.k))).toEquiv

/-- `T`'s failure at the typed question pair of the type pair `uv`, on the vector whose oracle half
is `x` and whose PCP half is `w`. -/
def edgeFail (T : TensorProductStrategy (typedGame V n P hk S S' check B)) (uv : ArTy × ArTy)
    (x : Fin (V.sampler.dim n) → 𝔽₂) (w : Coord P → Fq P hk) : ℝ :=
  T.failAt (uv.1, (cl V n P hk S S' uv.1).eval (Fin.append x (pcpBits P hk w)))
    (uv.2, (cl V n P hk S S' uv.2).eval (Fin.append x (pcpBits P hk w)))

/-! ## The sixth copy -/

/-- **The typed question of a CL question** of the sixth copy, at role `r` and oracle half `x`. -/
def arQ6 (r : Role) (x : Fin (V.sampler.dim n) → 𝔽₂) (q : LIDT.CL.Question (Fq P hk) P.m') :
    Detyping.Question ArTy (Fin (dim V n P)) :=
  ((r, ((5 : Fin 6), q.ty)), Fin.append x (pcpBits P hk ((regs6 P).embedQ S' q)))

/-- **An answer read as an answer of the sixth copy's test**: parsed at the question's type, then
read by `ans6`. -/
def readAns6 (q : LIDT.CL.Question (Fq P hk) P.m') (a : Verifier.Answers B) :
    LIDT.CL.Answer (Fq P hk) P.m' dPcp (P.m' + 6) :=
  ans6 ((parse (fld P hk) ((5 : Fin 6), q.ty) a.1).getD (.inr (.values 0)))

/-- **The per-seed simultaneous low-degree strategy** of the sixth copy at oracle half `y`: the
typed strategy played through `arQ6` and `readAns6`, both players oracles. -/
def copyStrategy6 (T : TensorProductStrategy (typedGame V n P hk S S' check B))
    (y : Fin (V.sampler.dim n) → 𝔽₂) :
    TensorProductStrategy (LIDT.CL.clGame (d := dPcp) (ldc := P.m' + 6) hm') :=
  T.adapt _ (arQ6 V n P hk S' .oracle y) (arQ6 V n P hk S' .oracle y) (readAns6 P hk B)
    (readAns6 P hk B)

/-- `T`'s failure at the typed question pair of sample `sm` of the sixth copy at oracle half `y`. -/
def copyFail6 (T : TensorProductStrategy (typedGame V n P hk S S' check B))
    (y : Fin (V.sampler.dim n) → 𝔽₂) (sm : LIDT.CL.Sample (Fq P hk) P.m') : ℝ :=
  T.failAt (arQ6 V n P hk S' .oracle y (sm.question hm' sm.tyA))
    (arQ6 V n P hk S' .oracle y (sm.question hm' sm.tyB))

end MIPRE.AnswerReduction

end


