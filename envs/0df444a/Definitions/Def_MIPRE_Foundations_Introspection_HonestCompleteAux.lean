-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_HonestCompleteAux
-- name    : MIPRE_Foundations_Introspection_HonestCompleteAux
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:09:38.745722+00:00
-- url     : https://prove2.me/theorems/e94d4c9c-f254-410f-8a60-f18392f14397
-- title:
--   Definitions of HonestCompleteAux: The complete honest auxiliary measurement family All auxiliary vertices use one common register/source space
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.HonestCompleteAux` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The complete honest auxiliary measurement family. All auxiliary vertices use one common register/source space. The graph and predicate are the actual restrictions of the typed introspection construction, including every Hide level, Read, Sample, Introspect, and consistency loops.
--
--   **Definitions** (2): `MIPRE.Introspection.Honest.AuxQuestion`; `MIPRE.Introspection.Honest.auxOp`.
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `auxCheck_self`, `auxCheck_swap`, `auxOp_nonzero_fits`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.HonestCompleteAux` (`MIPRE/Foundations/Introspection/HonestCompleteAux.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 80 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/HonestCompleteAux.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HonestCompleteAux.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
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
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
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
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
import Definitions.Def_MIPRE_Foundations_Introspection_HonestFirstHide
import Definitions.Def_MIPRE_Foundations_Introspection_HonestAdaptive
import Definitions.Def_MIPRE_Foundations_Introspection_HonestRead
import Definitions.Def_MIPRE_Foundations_Introspection_HonestXCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingStep
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestLabelSupport
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingChecks
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingAcceptance
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCoreGame
import Definitions.Def_MIPRE_Foundations_Introspection_HonestReading
import Definitions.Def_MIPRE_Foundations_Introspection_HonestParsed
import Definitions.Def_MIPRE_Foundations_Introspection_HonestParsedHiding
import Theorems.Thm_MIPRE_IsPVM_orthogonal

/-! # The complete honest auxiliary measurement family

All auxiliary vertices use one common register/source space. The graph and
predicate are the actual restrictions of the typed introspection construction,
including every Hide level, Read, Sample, Introspect, and consistency loops.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {F ι A PA P : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
  [Fintype PA] [DecidableEq P] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)

abbrev AuxQuestion (ℓ : ℕ) := AuxType ℓ × Bool

def auxOp (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (t : AuxQuestion ℓ) : ParsedAnswer (ι → F) A PA →
      Matrix ((ι → F) × Fin R.d) ((ι → F) × Fin R.d) ℂ :=
  match t.1 with
  | .introspect => parsedCoreOp L D R (false, t.2)
  | .sample => parsedCoreOp L D R (true, t.2)
  | .read => parsedReadOp L D R t.2 (hL t.2)
  | .hide k => parsedHideOp L D R t.2 k.val (hL t.2)

theorem auxCheck_swap (X Z : P) (projectPauli : PA → ι → F)
    (DP : P → P → PA → PA → Bool) (t u : AuxQuestion ℓ)
    (a b : ParsedAnswer (ι → F) A PA) :
    TypedPredicate.check L X Z projectPauli D DP (.inr t) (.inr u) a b =
      TypedPredicate.check L X Z projectPauli D DP (.inr u) (.inr t) b a := by
  by_cases ht : t = u <;> by_cases hab : a = b <;>
    simp [TypedPredicate.check, ht, hab, eq_comm, Bool.and_comm, Bool.and_left_comm]

theorem auxOp_nonzero_fits (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (t : AuxQuestion ℓ) (a : ParsedAnswer (ι → F) A PA)
    (ha : auxOp L D R hL t a ≠ 0) : TypedPredicate.fits (.inr t : QuestionType P ℓ) a = true := by
  rcases t with ⟨t, w⟩
  cases t <;> cases a <;>
    simp_all only [auxOp, parsedCoreOp, parsedReadOp, parsedHideOp, ne_eq,
      not_true_eq_false, TypedPredicate.fits]

theorem auxCheck_self (X Z : P) (projectPauli : PA → ι → F)
    (DP : P → P → PA → PA → Bool) (t : AuxQuestion ℓ)
    (a : ParsedAnswer (ι → F) A PA)
    (ha : TypedPredicate.fits (.inr t : QuestionType P ℓ) a = true) :
    TypedPredicate.check L X Z projectPauli D DP (.inr t) (.inr t) a a = true := by
  rcases t with ⟨t, w⟩
  cases t <;> cases w <;> cases a <;>
    simp_all [TypedPredicate.check, TypedPredicate.fits, TypedPredicate.directed]

end MIPRE.Introspection.Honest


