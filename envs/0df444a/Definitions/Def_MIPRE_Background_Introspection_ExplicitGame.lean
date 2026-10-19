-- Prove2me | Definitions.Def_MIPRE_Background_Introspection_ExplicitGame
-- name    : MIPRE_Background_Introspection_ExplicitGame
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:13:29.511809+00:00
-- url     : https://prove2.me/theorems/d016c7cd-d3f9-4a71-8546-f52d2ff27bc4
-- title:
--   Definitions of ExplicitGame: Full typed introspection under an explicit Pauli seed enumeration The equivalence acts on all raw questions, preserves…
-- statement:
--   The definitions of the module `MIPRE.Background.Introspection.ExplicitGame` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Full typed introspection under an explicit Pauli seed enumeration. The equivalence acts on all raw questions, preserves the type, and fixes the auxiliary questions and both distinguished Pauli measurements. A permutation of the common random content proves equality of the full question-pair law, including mixed Pauli/auxiliary edges. The parsed predicate is intertwined on every question and every answer, including malformed answers and loops.
--
--   **Definitions** (7): `MIPRE.Introspection.ExplicitGame.Question` (Raw questions consist of an introspection type and its full binary content.); `MIPRE.Introspection.ExplicitGame.contentPermutation` (Change only the Pauli contents whose decoding retains the seed.); `MIPRE.Introspection.ExplicitGame.game` (The actual explicit-selector typed game, with the same source predicate.); `MIPRE.Introspection.ExplicitGame.pauliCheck` (The Pauli decision predicate with the explicit seed decoder.); `MIPRE.Introspection.ExplicitGame.pccToExplicit` (The same relabeling on the doubled questions used by PCC completeness.); `MIPRE.Introspection.ExplicitGame.questionEquiv` (A total equivalence of full raw typed questions, not only sampled outputs.); `MIPRE.Introspection.ExplicitGame.toLegacy` (Transport an explicit strategy back to the legacy full game, with its literal state.).
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `questionEquiv_aux`, `questionEquiv_pauli`, `questionEquiv_symm_pauli`, `dist_equiv`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.Introspection.ExplicitGame` (`MIPRE/Background/Introspection/ExplicitGame.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 101 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Introspection/ExplicitGame.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/ExplicitGame.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
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
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_SeedSelectorProg
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Background_QLD_CLPresentation
import Definitions.Def_MIPRE_Background_QLD_CLBinary
import Definitions.Def_MIPRE_Background_QLD_CLExplicitSeed
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_PauliRestriction
import Definitions.Def_MIPRE_Background_QLD_CLTransport
import Definitions.Def_MIPRE_Background_Introspection_PauliRestriction
import Definitions.Def_MIPRE_Background_QLD_CLExplicitTransport
import Definitions.Def_MIPRE_Foundations_GameTransportProjection
import Theorems.Thm_MIPRE_SyncStrategy_isPCC_relabel
import Theorems.Thm_MIPRE_SyncStrategy_value_relabel

/-! # Full typed introspection under an explicit Pauli seed enumeration

The equivalence acts on all raw questions, preserves the type, and fixes the
auxiliary questions and both distinguished Pauli measurements. A permutation
of the common random content proves equality of the full question-pair law,
including mixed Pauli/auxiliary edges. The parsed predicate is intertwined on
every question and every answer, including malformed answers and loops.
-/

noncomputable section
namespace MIPRE.Introspection.ExplicitGame
open Finset Classical
open QLD.PauliCL
open QLD.PauliCL.ExplicitSeed
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000

variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]

/-- Raw questions consist of an introspection type and its full binary content. -/
abbrev Question (m t ℓ : ℕ) :=
  CL.Detyping.Question (QuestionType QLD.Ty ℓ) (Fin ((3*m+3)*t))

/-- Change only the Pauli contents whose decoding retains the seed. -/
def contentPermutation (π : F ≃ F) (b : Module.Basis (Fin t) (ZMod 2) F) :
    QuestionType QLD.Ty ℓ →
      ((Fin ((3*m+3)*t) → ZMod 2) ≃ (Fin ((3*m+3)*t) → ZMod 2))
  | .inl p => binaryOutputPermutation π b p
  | .inr _ => Equiv.refl _

/-- A total equivalence of full raw typed questions, not only sampled outputs. -/
def questionEquiv (π : F ≃ F) (b : Module.Basis (Fin t) (ZMod 2) F) :
    Question m t ℓ ≃ Question m t ℓ where
  toFun q := (q.1, contentPermutation π b q.1 q.2)
  invFun q := (q.1, (contentPermutation π b q.1).symm q.2)
  left_inv q := by simp
  right_inv q := by simp

/-- The question equivalence fixes every auxiliary question. -/
@[simp] theorem questionEquiv_aux (π : F ≃ F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (u : AuxType ℓ) (w : Bool)
    (x : Fin ((3*m+3)*t) → ZMod 2) :
    questionEquiv π b (.inr (u,w),x) = (.inr (u,w),x) := rfl

/-- The question equivalence fixes both distinguished Pauli questions. -/
@[simp] theorem questionEquiv_pauli (π : F ≃ F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (W : QLD.Bas)
    (x : Fin ((3*m+3)*t) → ZMod 2) :
    questionEquiv (ℓ := ℓ) π b (.inl (.pauli W),x) = (.inl (.pauli W),x) := by
  simp [questionEquiv, contentPermutation]

/-- The inverse equivalence also fixes both distinguished Pauli questions. -/
@[simp] theorem questionEquiv_symm_pauli (π : F ≃ F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (W : QLD.Bas)
    (x : Fin ((3*m+3)*t) → ZMod 2) :
    (questionEquiv (ℓ := ℓ) π b).symm (.inl (.pauli W),x) = (.inl (.pauli W),x) :=
  (Equiv.symm_apply_eq _).mpr (questionEquiv_pauli π b W x).symm

/-- The Pauli decision predicate with the explicit seed decoder. -/
def pauliCheck (hm : m ∣ Fintype.card F) (π : F ≃ F)
    (b : Module.Basis (Fin t) (ZMod 2) F)
    (p q : QLD.Ty) (x y : Fin ((3*m+3)*t) → ZMod 2) :
    QLD.Answer F m d → QLD.Answer F m d → Bool :=
  QLD.accepts hm (binaryDecode π b p x) (binaryDecode π b q y)

/-- The actual explicit-selector typed game, with the same source predicate. -/
def game (hm : m ∣ Fintype.card F) (χ : F → Fin m) (π : F ≃ F)
    (b : Module.Basis (Fin t) (ZMod 2) F)
    (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
    (D : (ι → F₀) → (ι → F₀) → A → A → Bool) :
    Game (Question m t ℓ) (Question m t ℓ)
      (ParsedAnswer (ι → F₀) A (QLD.Answer F m d))
      (ParsedAnswer (ι → F₀) A (QLD.Answer F m d)) :=
  TypedEstimates.parsedGame QLD.adj (.pauli .X) (.pauli .Z)
    (ExplicitSeed.binaryPresentation χ b) L project D (pauliCheck hm π b)

variable (hm : m ∣ Fintype.card F) (χ : F → Fin m) (π : F ≃ F)
  (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
  (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)

/-- Simultaneous seed and output equivalences preserve the joint sampling law. -/
theorem dist_equiv {S X : Type*} [Fintype S] [Fintype X]
    (a b c d : S → X) (e : S ≃ S) (f : X ≃ X)
    (ha : ∀ s, f (a s) = c (e s)) (hb : ∀ s, f (b s) = d (e s)) (x y : X) :
    SampledGame.dist a b x y = SampledGame.dist c d (f x) (f y) := by
  unfold SampledGame.dist
  congr 1
  refine Fintype.sum_equiv e _ _ fun s => ?_
  rw [← ha, ← hb]
  simp only [Prod.mk.injEq, Equiv.apply_eq_iff_eq]

set_option backward.isDefEq.respectTransparency true

/-- Transport an explicit strategy back to the legacy full game, with its literal state. -/
abbrev toLegacy (S : TensorProductStrategy (game hm χ π b L project D)) :
    TensorProductStrategy (PauliRestriction.fullGame hm b L project D) :=
  S.relabel _ (questionEquiv π b).symm (questionEquiv π b).symm (.refl _) (.refl _)

variable [DecidableEq A]

/-- The same relabeling on the doubled questions used by PCC completeness. -/
abbrev pccToExplicit (S : SyncStrategy (PauliRestriction.fullGame hm b L project D).doubled) :
    SyncStrategy (game hm χ π b L project D).doubled :=
  S.relabel _ (Equiv.prodCongr (.refl Bool) (questionEquiv π b)) (.refl _)

end MIPRE.Introspection.ExplicitGame


