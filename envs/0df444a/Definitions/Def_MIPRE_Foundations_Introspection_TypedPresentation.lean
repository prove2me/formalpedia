-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
-- name    : MIPRE_Foundations_Introspection_TypedPresentation
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:40:09.255481+00:00
-- url     : https://prove2.me/theorems/1beb0029-230b-42c8-b1e1-d7e4b841f4cf
-- title:
--   Definitions of TypedPresentation: The typed introspection CL presentation The three-level Pauli presentations are retained verbatim
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.TypedPresentation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The typed introspection CL presentation. The three-level Pauli presentations are retained verbatim. Every auxiliary type uses the zero presentation, padded to three levels with a full factor partition. Both players use the same family. The corresponding finite game has an exactly uniform ordered-edge law, and the cross-introspection edge asks the two zero-content questions with probability the inverse edge count.
--
--   **Definitions** (2): `MIPRE.Introspection.TypedPresentation.family` (The typed sampler's complete three-level CL family.); `MIPRE.Introspection.TypedPresentation.game` (The actual finite typed introspection game, for the supplied decision predicate.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `eval_aux`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.TypedPresentation` (`MIPRE/Foundations/Introspection/TypedPresentation.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 16 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/TypedPresentation.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TypedPresentation.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
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
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Theorems.Thm_MIPRE_CL_CLFun_factorOfPrefix_zeroOn
import Theorems.Thm_MIPRE_CL_CLFun_mapOfPrefix_zeroOn
import Theorems.Thm_MIPRE_Introspection_TypeGraph_edges_nonempty

/-! # The typed introspection CL presentation

The three-level Pauli presentations are retained verbatim. Every auxiliary
type uses the zero presentation, padded to three levels with a full factor
partition. Both players use the same family. The corresponding finite game
has an exactly uniform ordered-edge law, and the cross-introspection edge
asks the two zero-content questions with probability the inverse edge count.
-/

noncomputable section

namespace MIPRE.Introspection.TypedPresentation

open Finset Classical

variable {PauliType F ι : Type*} [Fintype ι] [DecidableEq ι] [Semiring F] {ℓ : ℕ}

/-- The typed sampler's complete three-level CL family. -/
def family (P : PauliType → CL.CLFun F ι 3) : QuestionType PauliType ℓ → CL.CLFun F ι 3
  | .inl p => P p
  | .inr _ => CL.CLFun.zeroOn univ 3

/-- All auxiliary questions have zero content. -/
@[simp] theorem eval_aux (P : PauliType → CL.CLFun F ι 3) (t : AuxType ℓ)
    (w : Bool) (z : ι → F) : (family P (.inr (t, w))).eval z = 0 :=
  CL.CLFun.eval_zeroOn univ 3 z

section Game

variable [Fintype PauliType] [DecidableEq PauliType]
  {A B : Type*} [Fintype A] [Fintype B]

/-- The actual finite typed introspection game, for the supplied decision predicate. -/
def game (E : PauliType → PauliType → Bool) (X Z : PauliType) (ℓ : ℕ)
    (P : PauliType → CL.CLFun (ZMod 2) ι 3)
    (D : CL.Detyping.Question (QuestionType PauliType ℓ) ι →
      CL.Detyping.Question (QuestionType PauliType ℓ) ι → A → B → Bool) :=
  CL.Detyping.typedGame (TypeGraph.Adj E X Z) (TypeGraph.edges_nonempty E X Z ℓ)
    (fun _ => family P) D

end Game
end MIPRE.Introspection.TypedPresentation


