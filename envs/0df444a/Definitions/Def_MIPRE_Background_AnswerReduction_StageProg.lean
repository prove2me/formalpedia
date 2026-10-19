-- Prove2me | Definitions.Def_MIPRE_Background_AnswerReduction_StageProg
-- name    : MIPRE_Background_AnswerReduction_StageProg
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T05:35:24.14172+00:00
-- url     : https://prove2.me/theorems/a9ce3ca1-f1f1-4a5b-b749-93a88ee4667a
-- title:
--   Definitions of StageProg: The stage programs of a copy of the PCP sampler Piece AR-3d of `planning/answer-reduction.md`: polynomial-time…
-- statement:
--   The definitions of the module `MIPRE.Background.AnswerReduction.StageProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The stage programs of a copy of the PCP sampler. Piece AR-3d of `planning/answer-reduction.md`: polynomial-time functions answering the queries of one copy of the seeded test, on the three runs of `k`-bit blocks (`MIPRE/Background/ AnswerReduction/Layout`). A copy is described by its offset `o`, length `sz = 2^jw`, selector width `jw` and seed index `c`, all in unary (`Desc`), and a test type numbered `0, 1, 2`. The answers are first written as plain functions of the blocks (`margL`, `linL`, `facL`), with the field arithmetic done by the introspection stage programs (`selectedDirectionProg`,…
--
--   **Definitions** (52): `MIPRE.AnswerReduction.StageProg.Blocks` (The three runs of blocks: point, direction, seeds.); `MIPRE.AnswerReduction.StageProg.Desc` (A copy: offset, length, selector width and seed index, in unary.); `MIPRE.AnswerReduction.StageProg.Input` (The input of a copy's program: `(k, d, τ, m', kind, j, u, y)`.); `MIPRE.AnswerReduction.StageProg.bitsOf` (The bits of three runs.); `MIPRE.AnswerReduction.StageProg.bitsP`; `MIPRE.AnswerReduction.StageProg.blk` (The block of `k` copies of a bit.); `MIPRE.AnswerReduction.StageProg.blkP`; `MIPRE.AnswerReduction.StageProg.blocksOf` (The runs of a bit string of `2m' + 6` blocks of `k` bits.); `MIPRE.AnswerReduction.StageProg.blocksP`; `MIPRE.AnswerReduction.StageProg.cI`; `MIPRE.AnswerReduction.StageProg.constBlk`; `MIPRE.AnswerReduction.StageProg.copyAnswer` (**The answer of a copy** to a query of kind `kind` at level `j` with vectors `u`, `y`.); `MIPRE.AnswerReduction.StageProg.copyProg` (**The program of a copy.**); `MIPRE.AnswerReduction.StageProg.dI`; `MIPRE.AnswerReduction.StageProg.dirOut` (The direction run of the second stage.); `MIPRE.AnswerReduction.StageProg.dirOutP`; `MIPRE.AnswerReduction.StageProg.facL` (**The factor space** at level `j`, as blocks of indicator bits.); `MIPRE.AnswerReduction.StageProg.facP`; `MIPRE.AnswerReduction.StageProg.isJ`; `MIPRE.AnswerReduction.StageProg.isKind`; `MIPRE.AnswerReduction.StageProg.isτ`; `MIPRE.AnswerReduction.StageProg.jI`; `MIPRE.AnswerReduction.StageProg.jwI`; and 20 more.
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `placeP_apply`, `sliceP_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.AnswerReduction.StageProg` (`MIPRE/Background/AnswerReduction/StageProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 114 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/AnswerReduction/StageProg.lean; blueprint lem:ar-typed-sampler

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/StageProg.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Trace.Basic
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

/-!
# The stage programs of a copy of the PCP sampler

Piece AR-3d of `planning/answer-reduction.md`: polynomial-time functions answering the queries
of one copy of the seeded test, on the three runs of `k`-bit blocks (`MIPRE/Background/
AnswerReduction/Layout`). A copy is described by its offset `o`, length `sz = 2^jw`, selector
width `jw` and seed index `c`, all in unary (`Desc`), and a test type numbered `0, 1, 2`.

The answers are first written as plain functions of the blocks (`margL`, `linL`, `facL`),
with the field arithmetic done by the introspection stage programs (`selectedDirectionProg`,
`axisRepresentativeProg`, `lineRepresentativeProg`); `copyProg` computes them.
-/

noncomputable section

namespace MIPRE.AnswerReduction.StageProg

open Cost Cost.PolyTimeFun Pcp Introspection.SeededLineProgram Introspection.LineProgram

/-- A copy: offset, length, selector width and seed index, in unary. -/
abbrev Desc := Unary × Unary × Unary × Unary

/-- The three runs of blocks: point, direction, seeds. -/
abbrev Blocks := List BitStr × List BitStr × List BitStr

/-! ## The answers, as functions of the blocks -/

section Spec

variable (k : Unary) (d : Desc) (τ : ℕ)

/-- The zero field element. -/
def zb : BitStr := k.map fun _ => false

/-- Every block replaced by zero. -/
def zeroed (l : List BitStr) : List BitStr := l.map fun _ => zb k

/-- The copy's seed. -/
def seedOf (seeds : List BitStr) : BitStr := (seeds.drop d.2.2.2.length).headD []

/-- The selected direction of a diagonal line. -/
def selDirL (s : BitStr) (w : List BitStr) : List BitStr :=
  selectedDirectionProg ((k, d.2.2.1, s), w)

/-- The third stage's map of the point register. -/
def ptMapL (s : BitStr) (dir w : List BitStr) : List BitStr :=
  if τ = 1 then axisRepresentativeProg ((k, d.2.2.1, s), w)
  else if τ = 2 then lineRepresentativeProg (k, w, dir) else w

/-- The seed run of the first stage. -/
def seedOut (s : BitStr) (seeds : List BitStr) : List BitStr :=
  if τ = 0 then zeroed k seeds else placeL (zb k) d.2.2.2.length [s] seeds

/-- The direction run of the second stage. -/
def dirOut (s : BitStr) (dirs : List BitStr) : List BitStr :=
  if τ = 2 then placeL (zb k) d.1.length (selDirL k d s (sliceL d.1.length d.2.1.length dirs)) dirs
  else zeroed k dirs

/-- The point run of the third stage. -/
def ptOut (s : BitStr) (dir pts : List BitStr) : List BitStr :=
  placeL (zb k) d.1.length (ptMapL k d τ s dir (sliceL d.1.length d.2.1.length pts)) pts

/-- **The marginal** at level `j`. -/
def margL (j : ℕ) (x : Blocks) : Blocks :=
  let s := seedOf d x.2.2
  (if 3 ≤ j then ptOut k d τ s (selDirL k d s (sliceL d.1.length d.2.1.length x.2.1)) x.1
    else zeroed k x.1,
   if 2 ≤ j then dirOut k d τ s x.2.1 else zeroed k x.2.1,
   seedOut k d τ s x.2.2)

/-- **The stage map** at level `j`, from the prefix `u`, applied to `y`. -/
def linL (j : ℕ) (u y : Blocks) : Blocks :=
  if j = 1 then (zeroed k y.1, zeroed k y.2.1, seedOut k d τ (seedOf d y.2.2) y.2.2)
  else if j = 2 then (zeroed k y.1, dirOut k d τ (seedOf d u.2.2) y.2.1, zeroed k y.2.2)
  else if j = 3 then
    (ptOut k d τ (seedOf d u.2.2) (sliceL d.1.length d.2.1.length u.2.1) y.1, zeroed k y.2.1,
      zeroed k y.2.2)
  else (zeroed k y.1, zeroed k y.2.1, zeroed k y.2.2)

/-- The block of `k` copies of a bit. -/
def blk (b : Bool) : BitStr := k.map fun _ => b

/-- **The factor space** at level `j`, as blocks of indicator bits. -/
def facL (j : ℕ) (u : Blocks) : Blocks :=
  if j = 1 then (u.1.map fun _ => blk k false, u.2.1.map fun _ => blk k false,
    placeL (blk k false) d.2.2.2.length [blk k true] u.2.2)
  else if j = 2 then (u.1.map fun _ => blk k false,
    placeL (blk k false) d.1.length (List.replicate d.2.1.length (blk k true)) u.2.1,
    u.2.2.map fun _ => blk k false)
  else if j = 3 then (u.1.map fun _ => blk k true,
    placeL (blk k true) d.1.length (List.replicate d.2.1.length (blk k false)) u.2.1,
    placeL (blk k true) d.2.2.2.length [blk k false] u.2.2)
  else (u.1.map fun _ => blk k false, u.2.1.map fun _ => blk k false,
    u.2.2.map fun _ => blk k false)

/-- The runs of a bit string of `2m' + 6` blocks of `k` bits. -/
def blocksOf (m' : Unary) (z : BitStr) : Blocks :=
  let l := Introspection.BinaryBlock.splitBlocks (m'.length + (m'.length + 6)) k.length z
  (l.take m'.length, (l.drop m'.length).take m'.length, (l.drop m'.length).drop m'.length)

/-- The bits of three runs. -/
def bitsOf (x : Blocks) : BitStr := (x.1 ++ x.2.1 ++ x.2.2).flatten

/-- **The answer of a copy** to a query of kind `kind` at level `j` with vectors `u`, `y`. -/
def copyAnswer (m' : Unary) (kind j : ℕ) (u y : BitStr) : BitStr :=
  if kind = 1 then bitsOf (margL k d τ j (blocksOf k m' u))
  else if kind = 2 then bitsOf (linL k d τ j (blocksOf k m' u) (blocksOf k m' y))
  else if kind = 3 then bitsOf (facL k d j (blocksOf k m' u))
  else []

end Spec

/-! ## The programs -/

/-- Placing, as a program: `(fill, o, w, l) ↦ placeL fill o w l`. -/
def placeP : PolyTimeFun (BitStr × Unary × List BitStr × List BitStr) (List BitStr) :=
  let fill := fst
  let o := fst.comp snd
  let w := fst.comp (snd.comp snd)
  let l := snd.comp (snd.comp snd)
  ap₂ append (ap₂ append ((mapWith snd).comp ((take.comp (l.pair o)).pair fill)) w)
    ((mapWith snd).comp ((drop.comp (l.pair (ap₂ append o (length.comp w)))).pair fill))

@[simp] theorem placeP_apply (fill : BitStr) (o : Unary) (w l : List BitStr) :
    placeP (fill, o, w, l) = placeL fill o.length w l := by
  simp only [placeP, ap₂_apply, append_apply, comp_apply, mapWith_apply, pair_apply, take_apply,
    fst_apply, snd_apply, drop_apply, length_apply, List.length_append, length_unary, placeL]

/-- Slicing, as a program: `(o, sz, l) ↦ sliceL o sz l`. -/
def sliceP : PolyTimeFun (Unary × Unary × List BitStr) (List BitStr) :=
  take.comp ((drop.comp ((snd.comp snd).pair fst)).pair (fst.comp snd))

@[simp] theorem sliceP_apply (o sz : Unary) (l : List BitStr) :
    sliceP (o, sz, l) = sliceL o.length sz.length l := rfl

/-- The input of a copy's program: `(k, d, τ, m', kind, j, u, y)`. -/
abbrev Input := Unary × Desc × ℕ × Unary × ℕ × ℕ × BitStr × BitStr

section Prog

def kI : PolyTimeFun Input Unary := fst
def dI : PolyTimeFun Input Desc := fst.comp snd
def τI : PolyTimeFun Input ℕ := fst.comp (snd.comp snd)
def mI : PolyTimeFun Input Unary := fst.comp (snd.comp (snd.comp snd))
def kindI : PolyTimeFun Input ℕ := fst.comp (snd.comp (snd.comp (snd.comp snd)))
def jI : PolyTimeFun Input ℕ := fst.comp (snd.comp (snd.comp (snd.comp (snd.comp snd))))
def uI : PolyTimeFun Input BitStr :=
  fst.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp snd)))))
def yI : PolyTimeFun Input BitStr :=
  snd.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp snd)))))
def oI : PolyTimeFun Input Unary := fst.comp dI
def szI : PolyTimeFun Input Unary := fst.comp (snd.comp dI)
def jwI : PolyTimeFun Input Unary := fst.comp (snd.comp (snd.comp dI))
def cI : PolyTimeFun Input Unary := snd.comp (snd.comp (snd.comp dI))

def zbP : PolyTimeFun Input BitStr := (map (const false)).comp kI
def blkP (b : Bool) : PolyTimeFun Input BitStr := (map (const b)).comp kI
def zeroedP (l : PolyTimeFun Input (List BitStr)) : PolyTimeFun Input (List BitStr) :=
  (mapWith snd).comp (l.pair zbP)
def isτ (t : ℕ) : PolyTimeFun Input Bool := ap₂ SAT.ArrayProg.eqNat τI (const t)

def blocksP (z : PolyTimeFun Input BitStr) : PolyTimeFun Input Blocks :=
  let n := ap₂ append mI (ap₂ append mI (const (unary 6)))
  let l := Introspection.BinaryBlock.splitBlocksProg.comp (n.pair (kI.pair z))
  (take.comp (l.pair mI)).pair ((take.comp ((drop.comp (l.pair mI)).pair mI)).pair
    (drop.comp ((drop.comp (l.pair mI)).pair mI)))

def seedOfP (seeds : PolyTimeFun Input (List BitStr)) : PolyTimeFun Input BitStr :=
  (headD []).comp (drop.comp (seeds.pair cI))

def selDirP (s : PolyTimeFun Input BitStr) (w : PolyTimeFun Input (List BitStr)) :
    PolyTimeFun Input (List BitStr) :=
  selectedDirectionProg.comp ((kI.pair (jwI.pair s)).pair w)

def ptMapP (s : PolyTimeFun Input BitStr) (dir w : PolyTimeFun Input (List BitStr)) :
    PolyTimeFun Input (List BitStr) :=
  ite (isτ 1) (axisRepresentativeProg.comp ((kI.pair (jwI.pair s)).pair w))
    (ite (isτ 2) (lineRepresentativeProg.comp (kI.pair (w.pair dir))) w)

def sliceI (l : PolyTimeFun Input (List BitStr)) : PolyTimeFun Input (List BitStr) :=
  sliceP.comp (oI.pair (szI.pair l))

def seedOutP (s : PolyTimeFun Input BitStr) (seeds : PolyTimeFun Input (List BitStr)) :
    PolyTimeFun Input (List BitStr) :=
  ite (isτ 0) (zeroedP seeds) (placeP.comp (zbP.pair (cI.pair ((s.cons (const [])).pair seeds))))

def dirOutP (s : PolyTimeFun Input BitStr) (dirs : PolyTimeFun Input (List BitStr)) :
    PolyTimeFun Input (List BitStr) :=
  ite (isτ 2) (placeP.comp (zbP.pair (oI.pair ((selDirP s (sliceI dirs)).pair dirs))))
    (zeroedP dirs)

def ptOutP (s : PolyTimeFun Input BitStr) (dir pts : PolyTimeFun Input (List BitStr)) :
    PolyTimeFun Input (List BitStr) :=
  placeP.comp (zbP.pair (oI.pair ((ptMapP s dir (sliceI pts)).pair pts)))

def margP (x : PolyTimeFun Input Blocks) : PolyTimeFun Input Blocks :=
  let pts := fst.comp x
  let dirs := fst.comp (snd.comp x)
  let seeds := snd.comp (snd.comp x)
  let s := seedOfP seeds
  (ite (ap₂ leNat (const 3) jI) (ptOutP s (selDirP s (sliceI dirs)) pts) (zeroedP pts)).pair
    ((ite (ap₂ leNat (const 2) jI) (dirOutP s dirs) (zeroedP dirs)).pair (seedOutP s seeds))

def isJ (t : ℕ) : PolyTimeFun Input Bool := ap₂ SAT.ArrayProg.eqNat jI (const t)

def linP (u y : PolyTimeFun Input Blocks) : PolyTimeFun Input Blocks :=
  let ypts := fst.comp y
  let ydirs := fst.comp (snd.comp y)
  let yseeds := snd.comp (snd.comp y)
  let su := seedOfP (snd.comp (snd.comp u))
  ite (isJ 1) ((zeroedP ypts).pair ((zeroedP ydirs).pair (seedOutP (seedOfP yseeds) yseeds)))
    (ite (isJ 2) ((zeroedP ypts).pair ((dirOutP su ydirs).pair (zeroedP yseeds)))
      (ite (isJ 3) ((ptOutP su (sliceI (fst.comp (snd.comp u))) ypts).pair
          ((zeroedP ydirs).pair (zeroedP yseeds)))
        ((zeroedP ypts).pair ((zeroedP ydirs).pair (zeroedP yseeds)))))

def constBlk (b : Bool) (l : PolyTimeFun Input (List BitStr)) : PolyTimeFun Input (List BitStr) :=
  (mapWith snd).comp (l.pair (blkP b))

def facP (u : PolyTimeFun Input Blocks) : PolyTimeFun Input Blocks :=
  let pts := fst.comp u
  let dirs := fst.comp (snd.comp u)
  let seeds := snd.comp (snd.comp u)
  ite (isJ 1) ((constBlk false pts).pair ((constBlk false dirs).pair
      (placeP.comp ((blkP false).pair (cI.pair (((blkP true).cons (const [])).pair seeds))))))
    (ite (isJ 2) ((constBlk false pts).pair ((placeP.comp ((blkP false).pair (oI.pair
        ((replicate.comp (szI.pair (blkP true))).pair dirs)))).pair (constBlk false seeds)))
      (ite (isJ 3) ((constBlk true pts).pair ((placeP.comp ((blkP true).pair (oI.pair
          ((replicate.comp (szI.pair (blkP false))).pair dirs)))).pair
          (placeP.comp ((blkP true).pair (cI.pair (((blkP false).cons (const [])).pair seeds))))))
        ((constBlk false pts).pair ((constBlk false dirs).pair (constBlk false seeds)))))

def bitsP (x : PolyTimeFun Input Blocks) : PolyTimeFun Input BitStr :=
  Introspection.BinaryBlock.flattenProg.comp
    (ap₂ append (ap₂ append (fst.comp x) (fst.comp (snd.comp x))) (snd.comp (snd.comp x)))

def isKind (t : ℕ) : PolyTimeFun Input Bool := ap₂ SAT.ArrayProg.eqNat kindI (const t)

/-- **The program of a copy.** -/
def copyProg : PolyTimeFun Input BitStr :=
  ite (isKind 1) (bitsP (margP (blocksP uI)))
    (ite (isKind 2) (bitsP (linP (blocksP uI) (blocksP yI)))
      (ite (isKind 3) (bitsP (facP (blocksP uI))) (const [])))

end Prog

section Apply

variable (x : Input)

end Apply

end MIPRE.AnswerReduction.StageProg

end


