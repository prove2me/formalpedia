-- Prove2me | Definitions.Def_MIPRE_Background_AnswerReduction_Params
-- name    : MIPRE_Background_AnswerReduction_Params
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T06:14:41.464518+00:00
-- url     : https://prove2.me/theorems/c4fd9fa4-f8cd-4c6c-92ff-89626e4773a8
-- title:
--   Definitions of Params: The PCP parameters of answer reduction, and the routine computing them Pieces AR-3d and AR-3f of…
-- statement:
--   The definitions of the module `MIPRE.Background.AnswerReduction.Params` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The PCP parameters of answer reduction, and the routine computing them. Pieces AR-3d and AR-3f of `planning/answer-reduction.md`. At index `n`, with the parameters `(λ, μ, σ)`, answer reduction runs the PCP of a `PcpDecider` at `pcpparams(n, T, Q, σ)` with `Q = (λn + 1)^μ` the input sampler's budget and `T = 2^{(Q + 5)(μ + 1)}` (`tPcp`): an input decider within its budget `2^Q (|d| + 1)^μ` accepts honest answers, of length at most `2^Q`, within `T` steps, which is what the PCP's completeness asks. `m` and `m'` are powers of two, so this is a `PcpFamily` (`family`). The routine `parProg`…
--
--   **Definitions** (23): `MIPRE.AnswerReduction.ParRoutine.budCore` (**The budgets' routine**, on `((λ, μ, σ), n)`: `(Q, T)` in binary.); `MIPRE.AnswerReduction.ParRoutine.core` (**The routine's core**, on `((λ, μ, σ), n)`: the budgets, the PCP's parameters, then `k`, `m`, `s` in unary.); `MIPRE.AnswerReduction.ParRoutine.hD` (The hardcoded `(λ, μ, σ)`.); `MIPRE.AnswerReduction.ParRoutine.logU` (`log₂` of a power of two, from its binary encoding, in unary.); `MIPRE.AnswerReduction.ParRoutine.paramsP` (The PCP's parameters `(k, m, s)`, from `((Q, T), (λ, μ, σ), n)`.); `MIPRE.AnswerReduction.ParRoutine.post1`; `MIPRE.AnswerReduction.ParRoutine.post2`; `MIPRE.AnswerReduction.ParRoutine.post6` (Stage 6's post-processing: the parameters `pd n`.); `MIPRE.AnswerReduction.ParRoutine.postBud`; `MIPRE.AnswerReduction.ParRoutine.postKeep`; `MIPRE.AnswerReduction.ParRoutine.pre1` (Stage 1: `λ` in unary, or `0` at the index `0`, where `λ` is not needed and may be arbitrarily large.); `MIPRE.AnswerReduction.ParRoutine.pre2` (Stage 2: `n` in unary; then the base `λn + 1` and the exponent `μ`.); `MIPRE.AnswerReduction.ParRoutine.pre3` (Stage 3: `Q = (λn + 1)^μ` in unary, kept in front of the input.); `MIPRE.AnswerReduction.ParRoutine.pre4` (Stages 4, 5, 6: `k`, `m`, `s` in unary.); `MIPRE.AnswerReduction.ParRoutine.pre5`; `MIPRE.AnswerReduction.ParRoutine.pre6`; `MIPRE.AnswerReduction.ParRoutine.preMu` (Stage 4: `μ` in unary; then `(Q, T)` in binary, `T = 2^{(Q + 5)(μ + 1)}`.); and -19 more.
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `arPar_hk`, `pow_size_sub_one`, `size_sub_one_le`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.AnswerReduction.Params` (`MIPRE/Background/AnswerReduction/Params.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 165 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/AnswerReduction/Params.lean; blueprint lem:ar-typed-sampler

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/Params.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Cost_While
import Definitions.Def_MIPRE_Foundations_Pipeline_UnaryArith
import Definitions.Def_MIPRE_Foundations_Pipeline_AnswerReduction
import Theorems.Thm_MIPRE_Cost_encode_injective
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_Cost_hardcode_wellScoped

/-!
# The PCP parameters of answer reduction, and the routine computing them

Pieces AR-3d and AR-3f of `planning/answer-reduction.md`. At index `n`, with the parameters
`(λ, μ, σ)`, answer reduction runs the PCP of a `PcpDecider` at `pcpparams(n, T, Q, σ)` with
`Q = (λn + 1)^μ` the input sampler's budget and `T = 2^{(Q + 5)(μ + 1)}` (`tPcp`): an input
decider within its budget `2^Q (|d| + 1)^μ` accepts honest answers, of length at most `2^Q`,
within `T` steps, which is what the PCP's completeness asks. `m` and `m'` are powers of two, so
this is a `PcpFamily` (`family`).

The routine `parProg` computes the family's parameters `pd n` from `n`, with `(λ, μ, σ)`
hardcoded. Its budgets' routine `budCore` computes `(Q, T)`: `λ` and `n` in unary (`λ` replaced
by `0` at the index `0`, where it is not needed, so that no step is longer than `Q`), `Q` by a
power loop, `μ` in unary and `T` from both. Then the PCP's parameter program gives `(k, m, s)`,
and `k, m, s` are written in unary. `parProg_runs` is its correctness.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline SAT StageProg

variable (PD : PcpDecider) (lam mu sigma : ℕ)

/-- The input sampler's budget `Q = (λn + 1)^μ`. -/
abbrev arQ (n : ℕ) : ℕ := (lam * n + 1) ^ mu

/-- The PCP's time bound `T = 2^{(Q + 5)(μ + 1)}`: an input decider running within
`2^Q (|d| + 1)^μ` on inputs of answers at most `2^Q` long accepts within `T`. -/
abbrev tPcp (n : ℕ) : ℕ := 2 ^ ((arQ lam mu n + 5) * (mu + 1))

/-- **The PCP parameters at index `n`**: `pcpparams(n, T, Q, σ)`. -/
def arPar (n : ℕ) : PcpParams := PD.params n (tPcp lam mu n) (arQ lam mu n) sigma

theorem arPar_hk (n : ℕ) : 1 ≤ (arPar PD lam mu sigma n).k :=
  (PD.odd_k _ _ _ _).pos

theorem pow_size_sub_one {m : ℕ} (h : ∃ j, m = 2 ^ j) : m = 2 ^ (m.size - 1) := by
  obtain ⟨j, rfl⟩ := h
  rw [Nat.size_pow, Nat.add_sub_cancel]

theorem size_sub_one_le {m k : ℕ} (h : ∃ j, m = 2 ^ j) (hd : m ∣ 2 ^ k) : m.size - 1 ≤ k := by
  rw [pow_size_sub_one h] at hd
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hd

/-- **The family of PCP parameters** of answer reduction. -/
def family : PcpFamily where
  par := arPar PD lam mu sigma
  hk := arPar_hk PD lam mu sigma
  jm n := (arPar PD lam mu sigma n).m.size - 1
  jm' n := (arPar PD lam mu sigma n).m'.size - 1
  m_eq n := pow_size_sub_one (PD.m_isPow _ _ _ _)
  m'_eq n := pow_size_sub_one (PD.m'_isPow _ _ _ _)
  jm_le n := size_sub_one_le (PD.m_isPow _ _ _ _) (PD.m_dvd_q _ _ _ _)
  jm'_le n := size_sub_one_le (PD.m'_isPow _ _ _ _) (PD.m'_dvd_q _ _ _ _)

/-! ## The routine -/

namespace ParRoutine

/-- The hardcoded `(λ, μ, σ)`. -/
def hD : PolyTimeFun Data Data := treeHead

/-- Stage 1: `λ` in unary, or `0` at the index `0`, where `λ` is not needed and may be
arbitrarily large. The input is `X₀ = (λ, μ, σ), n`. -/
def pre1 : PolyTimeFun Data Data :=
  ap₂ treePair (ite (ap₂ treeEq treeTail (const Data.nil)) (const (encode (0 : ℕ)))
    (treeHead.comp hD)) (PolyTimeFun.id Data)
def post1 : PolyTimeFun (Data × Data) Data := ap₂ treePair snd fst

/-- Stage 2: `n` in unary; then the base `λn + 1` and the exponent `μ`. -/
def pre2 : PolyTimeFun Data Data := ap₂ treePair (treeTail.comp treeTail) (PolyTimeFun.id Data)
def post2 : PolyTimeFun (Data × Data) Data :=
  ap₂ treePair (ap₂ treePair (encoded.comp ((const ()).cons
      (LowDegree.DegreeArithmetic.mulUnaryProg.comp ((readUnary.comp (treeHead.comp fst)).pair
        (readUnary.comp snd)))))
      (treeHead.comp (treeTail.comp (treeHead.comp (treeTail.comp fst)))))
    (treeTail.comp fst)

/-- Stage 3: `Q = (λn + 1)^μ` in unary, kept in front of the input. -/
def pre3 : PolyTimeFun Data Data := PolyTimeFun.id Data

/-- Stage 4: `μ` in unary; then `(Q, T)` in binary, `T = 2^{(Q + 5)(μ + 1)}`. -/
def preMu : PolyTimeFun Data Data :=
  ap₂ treePair (treeHead.comp (treeTail.comp (treeHead.comp (treeTail.comp (PolyTimeFun.id Data)))))
    (PolyTimeFun.id Data)
def postBud : PolyTimeFun (Data × Data) Data :=
  let Q := readUnary.comp (treeHead.comp fst)
  let E := LowDegree.DegreeArithmetic.mulUnaryProg.comp
    ((ap₂ append Q (const (unary 5))).pair ((const ()).cons (readUnary.comp snd)))
  encoded.comp ((addUnary.comp ((const 0).pair Q)).pair
    (bitsValue.comp (ap₂ append ((map (const false)).comp E) (const [true]))))

/-- Stages 4, 5, 6: `k`, `m`, `s` in unary. -/
def pre4 : PolyTimeFun Data Data := ap₂ treePair treeHead (PolyTimeFun.id Data)
def pre5 : PolyTimeFun Data Data :=
  ap₂ treePair (treeHead.comp (treeTail.comp treeTail)) (PolyTimeFun.id Data)
def pre6 : PolyTimeFun Data Data :=
  ap₂ treePair (treeTail.comp (treeTail.comp (treeTail.comp treeTail))) (PolyTimeFun.id Data)
def postKeep : PolyTimeFun (Data × Data) Data := ap₂ treePair snd fst

/-- **The budgets' routine**, on `((λ, μ, σ), n)`: `(Q, T)` in binary. -/
def budCore : Prog :=
  seqProg (stageProg pre1 toUnaryProg post1) <|
  seqProg (stageProg pre2 toUnaryProg post2) <|
  seqProg (stageProg pre3 powProg postKeep) (stageProg preMu toUnaryProg postBud)

/-- The PCP's parameters `(k, m, s)`, from `((Q, T), (λ, μ, σ), n)`. -/
def paramsP : PolyTimeFun Data Data :=
  let n := readNat.comp (treeTail.comp treeTail)
  let Q := readNat.comp (treeHead.comp treeHead)
  let T := readNat.comp (treeTail.comp treeHead)
  let σ := readNat.comp (treeTail.comp (treeTail.comp (treeHead.comp treeTail)))
  encoded.comp (PD.paramsProg.comp (n.pair (T.pair (Q.pair σ))))

/-- `log₂` of a power of two, from its binary encoding, in unary. -/
def logU : PolyTimeFun ℕ Unary := tail.comp ((map (const ())).comp (readBits.comp encoded))

/-- `c` copies of a unary numeral. -/
def timesU : ℕ → PolyTimeFun Unary Unary
  | 0 => const []
  | c + 1 => ap₂ append (timesU c) (PolyTimeFun.id Unary)

/-- Stage 6's post-processing: the parameters `pd n`. The context is `(m, k, (k, m, s))` in unary
and binary, the answer `s` in unary. -/
def post6 : PolyTimeFun (Data × Data) Data :=
  let us := readUnary.comp snd
  let um := readUnary.comp (treeHead.comp fst)
  let uk := readUnary.comp (treeHead.comp (treeTail.comp fst))
  let m := readNat.comp (treeHead.comp (treeTail.comp (treeTail.comp (treeTail.comp fst))))
  let um' := ap₂ append (ap₂ append ((timesU 5).comp um) (const (unary 5))) us
  let jm := logU.comp m
  let jm' := logU.comp (addUnary.comp ((const 0).pair um'))
  let d (c : ℕ) : PolyTimeFun (Data × Data) Desc :=
    if c < 5 then ((timesU c).comp um).pair (um.pair (jm.pair (const (unary c))))
    else (const []).pair (um'.pair (jm'.pair (const (unary c))))
  encoded.comp (uk.pair (um'.pair (listOf ((List.range 6).map d))))

/-- **The routine's core**, on `((λ, μ, σ), n)`: the budgets, the PCP's parameters, then `k`,
`m`, `s` in unary. -/
def core : Prog :=
  seqProg (stageProg (ap₂ treePair (PolyTimeFun.id Data) (PolyTimeFun.id Data)) budCore postKeep) <|
  seqProg (paramsP PD).code <|
  seqProg (stageProg pre4 toUnaryProg postKeep) <|
  seqProg (stageProg pre5 toUnaryProg postKeep) (stageProg pre6 toUnaryProg post6)

end ParRoutine

open ParRoutine in
/-- **The parameter routine** of answer reduction, with `(λ, μ, σ)` hardcoded. -/
def parProg : Prog := hardcode (core PD) (encode (lam, mu, sigma))

end MIPRE.AnswerReduction

end


