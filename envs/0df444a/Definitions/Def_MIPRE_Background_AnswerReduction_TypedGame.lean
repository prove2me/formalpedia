-- Prove2me | Definitions.Def_MIPRE_Background_AnswerReduction_TypedGame
-- name    : MIPRE_Background_AnswerReduction_TypedGame
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T05:34:15.479959+00:00
-- url     : https://prove2.me/theorems/2b931633-2ccb-4ad3-ba9a-16fb76bc30ed
-- title:
--   Definitions of TypedGame: The typed answer-reduced game Piece AR-3c of `planning/answer-reduction.md`, concluded: the game of the typed…
-- statement:
--   The definitions of the module `MIPRE.Background.AnswerReduction.TypedGame` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The typed answer-reduced game. Piece AR-3c of `planning/answer-reduction.md`, concluded: the game of the typed answer-reduced verifier `V̂^ar` at one index, in the vocabulary the detyping compiler consumes (`MIPRE.CL.Detyping.typedGame`), with bit-string answers. * The types are `Role × PcpTy`, on the complete type graph with loops (`graph`), as for the oracularized verifier. * The CL functions are the binary family `cl` of `MIPRE/Background/AnswerReduction/Family`, the same for both players. * The predicate (`typedPred`) parses both answers by their types (`parse`), rejects a failed parse,…
--
--   **Definitions** (8): `MIPRE.AnswerReduction.ArTy` (The types of the answer-reduced verifier.); `MIPRE.AnswerReduction.decodeQ` (A typed question of the answer-reduced verifier, decoded: the type, the oracle half and the PCP half.); `MIPRE.AnswerReduction.fld` (The field of the PCP with its `k`-bit representation.); `MIPRE.AnswerReduction.gameCheck` (**The game check**: the PCP verifier of `PD`, with the input decider `D` and the parameters `(n, T, Q, σ)`, on the input question pair read…); `MIPRE.AnswerReduction.graph` (The complete type graph on the answer-reduced types, loops included.); `MIPRE.AnswerReduction.instDecidableRelArTyGraph`; `MIPRE.AnswerReduction.typedGame` (**The typed answer-reduced game** at index `n`, with answers of length at most `B`.); `MIPRE.AnswerReduction.typedPred` (**The typed answer-reduced predicate** on bit-string answers of length at most `B`.).
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `graph_nonempty`, `instNonemptyTy`, `mem_graph_edges`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.AnswerReduction.TypedGame` (`MIPRE/Background/AnswerReduction/TypedGame.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 132 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/AnswerReduction/TypedGame.lean; blueprint def:ar-typed-game

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/TypedGame.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# The typed answer-reduced game

Piece AR-3c of `planning/answer-reduction.md`, concluded: the game of the typed answer-reduced
verifier `V̂^ar` at one index, in the vocabulary the detyping compiler consumes
(`MIPRE.CL.Detyping.typedGame`), with bit-string answers.

* The types are `Role × PcpTy`, on the complete type graph with loops (`graph`), as for the
  oracularized verifier.
* The CL functions are the binary family `cl` of `MIPRE/Background/AnswerReduction/Family`, the
  same for both players.
* The predicate (`typedPred`) parses both answers by their types (`parse`), rejects a failed
  parse, and otherwise decides by the answer-reduced predicate `accepts` on the decoded questions
  (`decodeQ`: the type, the oracle half, and the PCP half read back over `F_q`).
* The game check (`gameCheck`) runs the PCP verifier of a `SAT.PcpDecider` on the input verifier's
  question pair, read off the oracle half by the input sampler's two CL functions, and the view
  `(z, α)` in the `k`-bit representation the PCP reads.

`accepts_of_typedPred` and `typedPred_enc` are the two directions AR-4 and AR-5 need: acceptance of
the bit-string predicate is acceptance of `accepts` after the parse, and `accepts` on answers of
the right format is acceptance of their honest encodings.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL SAT Pcp Cost

/-- The types of the answer-reduced verifier. -/
abbrev ArTy := Role × PcpTy

/-- The complete type graph on the answer-reduced types, loops included. -/
def graph : ArTy → ArTy → Prop := fun _ _ => True

instance : DecidableRel graph := fun _ _ => isTrue trivial

theorem mem_graph_edges (p : ArTy × ArTy) : p ∈ CL.Graph.edges graph := by
  simp only [CL.Graph.edges, Finset.mem_filter]
  exact ⟨by simp, trivial⟩

instance : Nonempty LIDT.CL.Ty := ⟨.point⟩

-- The kernel unfolds the `Finset.univ` of the 54 types while checking this; the default depth
-- does not suffice.
set_option maxRecDepth 10000 in
theorem graph_nonempty : (CL.Graph.edges graph).Nonempty :=
  ⟨Classical.arbitrary _, mem_graph_edges _⟩

variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)

/-- The field of the PCP with its `k`-bit representation. -/
abbrev fld : BinField P.k := shoupBinField P.k hk

/-- A typed question of the answer-reduced verifier, decoded: the type, the oracle half and the
PCP half. -/
def decodeQ (p : Detyping.Question ArTy (Fin (dim V n P))) :
    Q P (Fq P hk) (Fin (V.sampler.dim n) → 𝔽₂) :=
  (p.1, oraclePart V n P p.2, pcpPart V n P hk p.2)

/-- **The game check**: the PCP verifier of `PD`, with the input decider `D` and the parameters
`(n, T, Q, σ)`, on the input question pair read off the oracle half and the view `(z, α)`. -/
def gameCheck (PD : PcpDecider) (D : Prog) (T Qn σ : ℕ) (x : Fin (V.sampler.dim n) → 𝔽₂)
    (z : Fin P.m' → Fq P hk) (α : Fin (P.m' + 6) → Fq P hk) : Bool :=
  PD.verify (pcpInput D n T Qn σ (toBits ((V.sampler.cl n .alice).eval x))
    (toBits ((V.sampler.cl n .bob).eval x)) ((fld P hk).vecBits z) ((fld P hk).vecBits α))

variable [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
  (check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) →
    Bool)

/-- **The typed answer-reduced predicate** on bit-string answers of length at most `B`. -/
def typedPred (B : ℕ) (p q : Detyping.Question ArTy (Fin (dim V n P)))
    (a b : Verifier.Answers B) : Bool :=
  match parse (fld P hk) p.1.2 a.1, parse (fld P hk) q.1.2 b.1 with
  | some u, some v => accepts S S' check (decodeQ V n P hk p) (decodeQ V n P hk q) u v
  | _, _ => false

/-- **The typed answer-reduced game** at index `n`, with answers of length at most `B`. -/
def typedGame (B : ℕ) :=
  Detyping.typedGame graph graph_nonempty (fun _ => cl V n P hk S S')
    (typedPred V n P hk S S' check B)

end MIPRE.AnswerReduction

end


