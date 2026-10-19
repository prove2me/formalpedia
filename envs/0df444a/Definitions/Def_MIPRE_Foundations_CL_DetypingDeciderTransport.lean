-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderTransport
-- name    : MIPRE_Foundations_CL_DetypingDeciderTransport
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:53:11.42246+00:00
-- url     : https://prove2.me/theorems/438717af-0add-4dd9-9cbf-cdb50940ee0b
-- title:
--   Definitions of DetypingDeciderTransport: Same-state soundness for the actual detyped verifier The actual sampler's numbered CL presentations have precisely the…
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.DetypingDeciderTransport` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Same-state soundness for the actual detyped verifier. The actual sampler's numbered CL presentations have precisely the finite detyping distribution after the coordinate permutation. Together with the proved executable predicate law, this transports the existing finite-game restriction to strategies for the compiled ambient verifier.
--
--   **Definitions** (6): `MIPRE.CL.Detyping.DeciderProgram.doubledVectorEquiv` (Undo coordinate numbering while preserving the doubling tag.); `MIPRE.CL.Detyping.DeciderProgram.fromFiniteSync` (Transport a synchronous finite-game strategy to the actual compiled verifier.); `MIPRE.CL.Detyping.DeciderProgram.restrictAmbient` (Restrict an actual compiled-verifier strategy to valid typed graph views.); `MIPRE.CL.Detyping.DeciderProgram.sourceFamily`; `MIPRE.CL.Detyping.DeciderProgram.toFinite` (Read the actual compiled-verifier strategy in the unnumbered finite game.); `MIPRE.CL.Detyping.DeciderProgram.vectorEquiv` (The coordinate numbering is an equivalence of the complete question spaces.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.DetypingDeciderTransport` (`MIPRE/Foundations/CL/DetypingDeciderTransport.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 52 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingDeciderTransport.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingDeciderTransport.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderProg
import Definitions.Def_MIPRE_Foundations_CL_DetypingDecider
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingCompleteSupport
import Definitions.Def_MIPRE_Foundations_CL_DetypingComplete
import Theorems.Thm_MIPRE_SyncStrategy_isPCC_relabel
import Theorems.Thm_MIPRE_SyncStrategy_value_relabel

/-! # Same-state soundness for the actual detyped verifier

The actual sampler's numbered CL presentations have precisely the finite
detyping distribution after the coordinate permutation. Together with the
proved executable predicate law, this transports the existing finite-game
restriction to strategies for the compiled ambient verifier.
-/

noncomputable section

namespace MIPRE.CL.Detyping.DeciderProgram

open Cost Finset
set_option linter.unusedSectionVars false

variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)

/-- The coordinate numbering is an equivalence of the complete question spaces. -/
def vectorEquiv (s : ℕ) : (Coord T (Fin s) → 𝔽₂) ≃ (Fin (graphDim T + s) → 𝔽₂) where
  toFun := push (registerEquiv s).toEmbedding
  invFun := pull (registerEquiv s).toEmbedding
  left_inv := pull_push _
  right_inv z := by
    funext i
    obtain ⟨q, rfl⟩ := (registerEquiv (T := T) s).surjective i
    exact push_apply _ _ q

def sourceFamily (n : ℕ) (w : Bool) := S.cl n (Player.ofBool w)

/-- Read the actual compiled-verifier strategy in the unnumbered finite game. -/
def toFinite (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : TensorProductStrategy ((verifier E S D C hℓ hD).game n (C.outer n))) :
    TensorProductStrategy (Detyping.game E (sourceFamily S n) (typedPredicate S D C n)) :=
  R.relabel _ (vectorEquiv (S.dim n)) (vectorEquiv (S.dim n)) (.refl _) (.refl _)

/-- Restrict an actual compiled-verifier strategy to valid typed graph views. -/
def restrictAmbient (hne : (Graph.edges E).Nonempty) (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : TensorProductStrategy ((verifier E S D C hℓ hD).game n (C.outer n))) :
    TensorProductStrategy (typedGame E hne (sourceFamily S n) (typedPredicate S D C n)) :=
  Detyping.restrict E hne _ _ (toFinite E S D C hℓ hD n R)

/-- Undo coordinate numbering while preserving the doubling tag. -/
def doubledVectorEquiv (s : ℕ) :
    (Bool × (Fin (graphDim T + s) → 𝔽₂)) ≃ (Bool × (Coord T (Fin s) → 𝔽₂)) :=
  Equiv.prodCongr (.refl Bool) (vectorEquiv s).symm

/-- Transport a synchronous finite-game strategy to the actual compiled verifier. -/
def fromFiniteSync (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : SyncStrategy (Detyping.game E (sourceFamily S n) (typedPredicate S D C n)).doubled) :
    SyncStrategy ((verifier E S D C hℓ hD).game n (C.outer n)).doubled :=
  R.relabel _ (doubledVectorEquiv (S.dim n)) (.refl _)

end MIPRE.CL.Detyping.DeciderProgram


