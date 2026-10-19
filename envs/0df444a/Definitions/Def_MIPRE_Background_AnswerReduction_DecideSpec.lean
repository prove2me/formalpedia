-- Prove2me | Definitions.Def_MIPRE_Background_AnswerReduction_DecideSpec
-- name    : MIPRE_Background_AnswerReduction_DecideSpec
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T06:14:07.62752+00:00
-- url     : https://prove2.me/theorems/8ebb3bd4-1fbb-4ac7-9716-e74ec974ca17
-- title:
--   Definitions of DecideSpec: The answer-reduced decision, on blocks of bits Piece AR-3e of `planning/answer-reduction.md`: the decision predicate…
-- statement:
--   The definitions of the module `MIPRE.Background.AnswerReduction.DecideSpec` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The answer-reduced decision, on blocks of bits. Piece AR-3e of `planning/answer-reduction.md`: the decision predicate `accepts` of `MIPRE/Background/AnswerReduction/Predicate`, rewritten as a function of the `k`-bit blocks a program reads (`verdictB`), with the field arithmetic done by the introspection stage programs: the line-versus-point check (`FieldLineCheck.lineCheckProg`), the seed selector, and the line representatives the sampler's third stage already uses. * **The low-degree subtests** (`ldB`): of the seeded test's decision, only a point question against a line question of the same…
--
--   **Definitions** (15): `MIPRE.AnswerReduction.acceptsB` (**The answer-reduced predicate on blocks**: the equal-type check and both sides.); `MIPRE.AnswerReduction.ansB` (The blocks of an answer: its elements' bits.); `MIPRE.AnswerReduction.blocksV` (The three runs of blocks of a vector of `V^pcp`.); `MIPRE.AnswerReduction.chkPlan` (Whether a type asks for the game check: an oracle's `Point_6`.); `MIPRE.AnswerReduction.chunks` (A list cut into `n` consecutive runs of `w` elements.); `MIPRE.AnswerReduction.cntB` (The number of field elements of an answer of the type `t`, from `m` and `m'` (`cnt`).); `MIPRE.AnswerReduction.dirB` (The direction of the line a question of test type `τ` describes, from its seed and its blocks: the selected axis, or the selected diagonal…); `MIPRE.AnswerReduction.eqPlan` (The comparison of two answer blocks a type pair asks for: step 2, an oracle's `Point_6` component against an isolated player's `Point_v`,…); `MIPRE.AnswerReduction.ldB` (**The low-degree subtest of a copy** `d`: the point the question with blocks `X` carries, against the line of test type `τ` the question…); `MIPRE.AnswerReduction.ldPlan` (The low-degree subtest a type pair asks for: the copy, and whether the line answers carry `m' + 6` codewords (the sixth copy).); `MIPRE.AnswerReduction.lvpB` (**The line-versus-point check on blocks**: every codeword's polynomial, evaluated at the point's parameter on the line, gives the point's…); and -11 more.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.AnswerReduction.DecideSpec` (`MIPRE/Background/AnswerReduction/DecideSpec.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 167 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/AnswerReduction/DecideSpec.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/DecideSpec.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
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
import Mathlib.FieldTheory.Galois.NormalBasis
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
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
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
import Definitions.Def_MIPRE_Background_AnswerReduction_Stages
import Definitions.Def_MIPRE_Background_AnswerReduction_StageLists
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_SeedSelectorProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFold
import Definitions.Def_MIPRE_Foundations_SAT_NormalElementProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryInverse
import Definitions.Def_MIPRE_Foundations_Introspection_LineRepresentativeProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Introspection_SeededLineProg
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_Introspection_BinaryBlockProg
import Definitions.Def_MIPRE_Background_AnswerReduction_StageProg
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_AnswerReduction_StageCorrect
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_CL_ProductSamplerProg
import Definitions.Def_MIPRE_Foundations_Cost_FiniteEncoding
import Definitions.Def_MIPRE_Background_AnswerReduction_PcpSampler
import Definitions.Def_MIPRE_Foundations_Introspection_FieldPolynomialProg
import Definitions.Def_MIPRE_Foundations_Introspection_FieldLineCheckProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg
import Definitions.Def_MIPRE_Foundations_Introspection_FieldQuestionProg

/-!
# The answer-reduced decision, on blocks of bits

Piece AR-3e of `planning/answer-reduction.md`: the decision predicate `accepts` of
`MIPRE/Background/AnswerReduction/Predicate`, rewritten as a function of the `k`-bit blocks a
program reads (`verdictB`), with the field arithmetic done by the introspection stage programs:
the line-versus-point check (`FieldLineCheck.lineCheckProg`), the seed selector, and the line
representatives the sampler's third stage already uses.

* **The low-degree subtests** (`ldB`): of the seeded test's decision, only a point question
  against a line question of the same copy is ever checked, and there it is the line-versus-point
  check on the line the question describes (`ldB_aline`, `ldB_dline`).
* **The five steps** (`sideB`) are organised by what each type pair asks for: at most one
  comparison of two answer blocks (`eqPlan`), one low-degree subtest (`ldPlan`) and one game check
  (`chkPlan`), which are functions of the types alone. `sideB_eq` is `side`.
* **The predicate** (`verdictB_eq`) is the typed predicate `typedPred`, the answers parsed into
  blocks (`parseB`) and the questions' PCP halves split into their three runs.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL

/-! ## Lists of blocks -/

/-- A list cut into `n` consecutive runs of `w` elements. -/
def chunks {α : Type*} (w : ℕ) : ℕ → List α → List (List α)
  | 0, _ => []
  | n + 1, l => l.take w :: chunks w n (l.drop w)

/-! ## The line-versus-point check -/

section Line

variable {k : ℕ} (hk : 1 ≤ k)

/-- **The line-versus-point check on blocks**: every codeword's polynomial, evaluated at the
point's parameter on the line, gives the point's value. -/
def lvpB (kU : Unary) (base dir pt : List BitStr) (polys : List (List BitStr))
    (vals : List BitStr) : Bool :=
  (polys.zip vals).all fun fa => lineCheckProg ((kU, base, dir, pt), fa.1, fa.2)

end Line

/-! ## The low-degree subtests of a copy -/

/-- The direction of the line a question of test type `τ` describes, from its seed and its
blocks: the selected axis, or the selected diagonal direction. -/
def dirB (kU : Unary) (d : Desc) (τ : ℕ) (s : BitStr) (Y : Blocks) : List BitStr :=
  if τ = 1 then axisDirectionProg ((kU, d.2.2.1, d.2.1), s)
  else selDirL kU d s (sliceL d.1.length d.2.1.length Y.2.1)

/-- **The low-degree subtest of a copy** `d`: the point the question with blocks `X` carries,
against the line of test type `τ` the question with blocks `Y` carries. -/
def ldB (kU : Unary) (d : Desc) (τ : ℕ) (X Y : Blocks) (polys : List (List BitStr))
    (vals : List BitStr) : Bool :=
  let s := seedOf d Y.2.2
  let dir := dirB kU d τ s Y
  lvpB kU (ptMapL kU d τ s dir (sliceL d.1.length d.2.1.length Y.1)) dir
    (sliceL d.1.length d.2.1.length X.1) polys vals

section Copy

variable {k : ℕ} (hk : 1 ≤ k)

variable (P : PcpParams)

/-- The three runs of blocks of a vector of `V^pcp`. -/
def blocksV (x : Coord P → ((shoupBinField k hk)).carrier) : Blocks :=
  (((shoupBinField k hk)).vecBits (ptOf6 P x), ((shoupBinField k hk)).vecBits (dirOf6 P x), ((shoupBinField k hk)).vecBits (seedsOf P x))

variable (o sz jw : ℕ) (c : Fin 6) (h : o + sz ≤ P.m') (hjw : jw ≤ k) (hsz2 : sz = 2 ^ jw)
  [NeZero sz] {hsz : sz ∣ Fintype.card (shoupBinField k hk).carrier}
  (S : Sel (shoupBinField k hk).carrier sz hsz)
  (hχ : ∀ a, (S.χ a : ℕ) = (selector (shoupBinField k hk) jw hjw a : ℕ))

end Copy

/-! ## Answers as blocks -/

section Answers

variable {k : ℕ} (hk : 1 ≤ k) {P : PcpParams}

/-- The blocks of an answer: its elements' bits. -/
def ansB (u : Ans P (shoupBinField k hk).carrier) : List BitStr := (elems ((shoupBinField k hk)) u).map ((shoupBinField k hk)).toBits

end Answers

/-! ## The atoms of the five steps, for a family -/

section Atoms

variable (F : PcpFamily) (n : ℕ)

/-- The number of coefficients of a polynomial of the sixth copy's line answers. -/
def width (m' : ℕ) (τ : LIDT.CL.Ty) : ℕ := if τ = .aline then dPcp + 1 else m' * dPcp + 1

end Atoms

/-! ## The five steps, planned by the types -/

/-- The comparison of two answer blocks a type pair asks for: step 2, an oracle's `Point_6`
component against an isolated player's `Point_v`, or step 4, a copy's point against the
oracle's `Point_6` component. -/
def eqPlan (p q : ArTy) : Option (ℕ × ℕ) :=
  match p.1, q.1 with
  | .oracle, .alice =>
    if (p.2.1 : ℕ) = 5 ∧ p.2.2 = .point ∧ (q.2.1 : ℕ) = 0 ∧ q.2.2 = .point then some (0, 0)
    else none
  | .oracle, .bob =>
    if (p.2.1 : ℕ) = 5 ∧ p.2.2 = .point ∧ (q.2.1 : ℕ) = 1 ∧ q.2.2 = .point then some (1, 0)
    else none
  | .oracle, .oracle =>
    if 2 ≤ (p.2.1 : ℕ) ∧ (p.2.1 : ℕ) < 5 ∧ p.2.2 = .point ∧ (q.2.1 : ℕ) = 5 ∧ q.2.2 = .point then
      some (0, p.2.1)
    else none
  | _, _ => none

/-- The low-degree subtest a type pair asks for: the copy, and whether the line answers carry
`m' + 6` codewords (the sixth copy). -/
def ldPlan (p q : ArTy) : Option (ℕ × Bool) :=
  match p.1, q.1 with
  | .alice, .alice =>
    if (p.2.1 : ℕ) = 0 ∧ (q.2.1 : ℕ) = 0 ∧ p.2.2 = .point ∧ q.2.2 ≠ .point then some (0, false)
    else none
  | .bob, .bob =>
    if (p.2.1 : ℕ) = 1 ∧ (q.2.1 : ℕ) = 1 ∧ p.2.2 = .point ∧ q.2.2 ≠ .point then some (1, false)
    else none
  | .oracle, .oracle =>
    if 2 ≤ (p.2.1 : ℕ) ∧ (p.2.1 : ℕ) < 5 ∧ q.2.1 = p.2.1 ∧ p.2.2 = .point ∧ q.2.2 ≠ .point then
      some (p.2.1, false)
    else if (p.2.1 : ℕ) = 5 ∧ (q.2.1 : ℕ) = 5 ∧ p.2.2 = .point ∧ q.2.2 ≠ .point then
      some (5, true)
    else none
  | _, _ => none

/-- Whether a type asks for the game check: an oracle's `Point_6`. -/
def chkPlan (p : ArTy) : Bool := decide (p.1 = .oracle ∧ (p.2.1 : ℕ) = 5 ∧ p.2.2 = .point)

/-- **One side of the five steps, on blocks**, as its type pair plans it. `chk` is the game
check's verdict. -/
def sideB (kU m'U : Unary) (descs : List Desc) (chk : Bool) (p q : ArTy) (X Y : Blocks)
    (A B : List BitStr) : Bool :=
  (match eqPlan p q with
    | some (α, β) => decide (A.getD α [] = B.getD β [])
    | none => true) &&
  (match ldPlan p q with
    | some (c, ch) => ldB kU (descs.getD c default) (tyNat q.2.2) X Y
        (if ch then chunks (width m'U.length q.2.2) (m'U.length + 6) B else [B]) A
    | none => true) &&
  (!chkPlan p || chk)

section SideEq

variable (F : PcpFamily) (n : ℕ) {X : Type*}
  (check : X → (Fin (F.par n).m' → Fq (F.par n) (F.hk n)) →
    (Fin ((F.par n).m' + 6) → Fq (F.par n) (F.hk n)) → Bool)

end SideEq

/-! ## Parsing, and the predicate -/

/-- The number of field elements of an answer of the type `t`, from `m` and `m'` (`cnt`). -/
def cntB (m m' : ℕ) (t : PcpTy) : ℕ :=
  if (t.1 : ℕ) < 5 then
    match t.2 with
    | .point => 1
    | .aline => dPcp + 1
    | .dline => m * dPcp + 1
  else
    match t.2 with
    | .point => m' + 6
    | .aline => (m' + 6) * (dPcp + 1)
    | .dline => (m' + 6) * (m' * dPcp + 1)

/-- **The bounded parse into blocks**: a serialized list of `c` blocks of `k` bits. -/
def parseB (k c : ℕ) (s : BitStr) : Option (List BitStr) :=
  match (decode (Data.parse s) : Option (List BitStr)) with
  | some bs => if bs.length = c ∧ ∀ b ∈ bs, b.length = k then some bs else none
  | none => none

/-- **The answer-reduced predicate on blocks**: the equal-type check and both sides. -/
def acceptsB (kU m'U : Unary) (descs : List Desc) (chkP chkQ : Bool) (p q : ArTy)
    (X Y : Blocks) (A B : List BitStr) : Bool :=
  (if p = q then decide (A = B) else true) &&
  sideB kU m'U descs chkP p q X Y A B && sideB kU m'U descs chkQ q p Y X B A

/-- **The typed predicate on bits**: parse both answers into blocks, then decide. -/
def verdictB (kU m'U : Unary) (descs : List Desc) (chkP chkQ : Bool) (p q : ArTy)
    (X Y : Blocks) (a b : BitStr) : Bool :=
  match parseB kU.length (cntB (descs.getD 0 default).2.1.length m'U.length p.2) a,
      parseB kU.length (cntB (descs.getD 0 default).2.1.length m'U.length q.2) b with
  | some A, some B => acceptsB kU m'U descs chkP chkQ p q X Y A B
  | _, _ => false

section VerdictEq

variable (F : PcpFamily) (n : ℕ) {X : Type*}
  (check : X → (Fin (F.par n).m' → Fq (F.par n) (F.hk n)) →
    (Fin ((F.par n).m' + 6) → Fq (F.par n) (F.hk n)) → Bool)

end VerdictEq

end MIPRE.AnswerReduction

end


