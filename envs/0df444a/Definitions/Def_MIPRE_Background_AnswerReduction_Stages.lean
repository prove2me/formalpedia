-- Prove2me | Definitions.Def_MIPRE_Background_AnswerReduction_Stages
-- name    : MIPRE_Background_AnswerReduction_Stages
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T05:32:04.247888+00:00
-- url     : https://prove2.me/theorems/390ff219-2ca9-4d7f-9c1b-c3f833738517
-- title:
--   Definitions of Stages: The queries of a copy of the PCP sampler, run by run Piece AR-3d of `planning/answer-reduction.md`
-- statement:
--   The definitions of the module `MIPRE.Background.AnswerReduction.Stages` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The queries of a copy of the PCP sampler, run by run. Piece AR-3d of `planning/answer-reduction.md`. A copy of the seeded test in the PCP sampler is a run `[o, o + sz)` of the concatenated registers with a seed `c` (`regsAt`). This file writes what its presentation's queries return in the three runs of `MIPRE/Background/AnswerReduction/ Layout` (`ptOf6`, `dirOf6`, `seedsOf`), which is the form a program computes: * the marginals (`comps_marginal`): the seed on the seed run, the cut-down direction placed at `o` on the direction run for a diagonal line, the line's base point placed at `o` on…
--
--   **Definitions** (5): `MIPRE.AnswerReduction.Pcp.comps` (The three runs of a vector.); `MIPRE.AnswerReduction.Pcp.dirPart` (The direction a diagonal line type's second stage writes, before placing.); `MIPRE.AnswerReduction.Pcp.placeV` (A vector of length `sz` placed at offset `o` of `Fin N`, zero elsewhere.); `MIPRE.AnswerReduction.Pcp.seedPart` (The seed run of a line type's first stage.); `MIPRE.AnswerReduction.Pcp.sliceV` (The run `[o, o + sz)` of a vector of length `N`.).
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `dirOf6_add`, `dirOf6_zero`, `ptOf6_add`, `ptOf6_zero`, `seedsOf_add`, `seedsOf_zero`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.AnswerReduction.Stages` (`MIPRE/Background/AnswerReduction/Stages.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 100 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/AnswerReduction/Stages.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/Stages.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
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
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.DeriveFintype
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
import Definitions.Def_MIPRE_Foundations_CL_Embedding
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

/-!
# The queries of a copy of the PCP sampler, run by run

Piece AR-3d of `planning/answer-reduction.md`. A copy of the seeded test in the PCP sampler is a
run `[o, o + sz)` of the concatenated registers with a seed `c` (`regsAt`). This file writes
what its presentation's queries return in the three runs of `MIPRE/Background/AnswerReduction/
Layout` (`ptOf6`, `dirOf6`, `seedsOf`), which is the form a program computes:

* the marginals (`comps_marginal`): the seed on the seed run, the cut-down direction placed at
  `o` on the direction run for a diagonal line, the line's base point placed at `o` on the point
  run;
* the stage maps from a prefix (`comps_map_zero`, `comps_map_one`, `comps_map_two`);
* the factor spaces, run by run (`mem_coordSet_*`, `mem_dirSet_*`, `mem_finalSet_*`).
-/

noncomputable section

namespace MIPRE.AnswerReduction.Pcp

open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL

/-! ## Placing and slicing vectors -/

section Vec

variable {F : Type*} [Zero F]

/-- A vector of length `sz` placed at offset `o` of `Fin N`, zero elsewhere. -/
def placeV {N sz : ℕ} (o : ℕ) (w : Fin sz → F) : Fin N → F :=
  fun r => if h : o ≤ r ∧ (r : ℕ) < o + sz then w ⟨r - o, by omega⟩ else 0

/-- The run `[o, o + sz)` of a vector of length `N`. -/
def sliceV {N : ℕ} (o sz : ℕ) (h : o + sz ≤ N) (v : Fin N → F) : Fin sz → F :=
  fun j => v ⟨o + j, by omega⟩

end Vec

variable (P : PcpParams) {F : Type*} [Field F]

/-! ## The runs of the three kinds of vectors a copy writes -/

@[simp] theorem ptOf6_add (x y : Coord P → F) : ptOf6 P (x + y) = ptOf6 P x + ptOf6 P y := rfl
@[simp] theorem dirOf6_add (x y : Coord P → F) : dirOf6 P (x + y) = dirOf6 P x + dirOf6 P y :=
  rfl
@[simp] theorem seedsOf_add (x y : Coord P → F) : seedsOf P (x + y) = seedsOf P x + seedsOf P y :=
  rfl
@[simp] theorem ptOf6_zero : ptOf6 P (0 : Coord P → F) = 0 := rfl
@[simp] theorem dirOf6_zero : dirOf6 P (0 : Coord P → F) = 0 := rfl
@[simp] theorem seedsOf_zero : seedsOf P (0 : Coord P → F) = 0 := rfl

variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')

/-! ## The queries, run by run -/

/-- The three runs of a vector. -/
def comps (x : Coord P → F) : (Fin P.m' → F) × (Fin P.m' → F) × (Fin 6 → F) :=
  (ptOf6 P x, dirOf6 P x, seedsOf P x)

variable [Fintype F] [DecidableEq F] [NeZero sz] {hsz : sz ∣ Fintype.card F} (S : Sel F sz hsz)

/-- The seed run of a line type's first stage. -/
def seedPart (t : Ty) (s : F) : Fin 6 → F := if t = .point then 0 else Pi.single c s

/-- The direction a diagonal line type's second stage writes, before placing. -/
def dirPart (t : Ty) (s : F) (d : Fin sz → F) : Fin sz → F :=
  if t = .dline then zeroBelow (S.χ s) d else 0

end MIPRE.AnswerReduction.Pcp

end


