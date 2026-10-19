-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_DetypingGame
-- name    : MIPRE_Foundations_CL_DetypingGame
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:54:45.902766+00:00
-- url     : https://prove2.me/theorems/05e0ba76-4444-4dab-82bf-9be032d0d02d
-- title:
--   Definitions of DetypingGame: The finite typed and detyped games This is the game at a fixed verifier index, before ambient-program compilation
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.DetypingGame` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The finite typed and detyped games. This is the game at a fixed verifier index, before ambient-program compilation. The detyped predicate accepts outside valid edge views. On valid views it calls the original predicate. The answer alphabets here are unchanged; the separate program-level cutoff and answer truncation obligations are not hidden here.
--
--   **Definitions** (9): `MIPRE.CL.Detyping.Edge` (Ordered adjacent pairs, including loops.); `MIPRE.CL.Detyping.Question` (Typed questions carry a type and its sampled content.); `MIPRE.CL.Detyping.TypedSeed` (The typed sample space is an ordered edge together with one common content seed.); `MIPRE.CL.Detyping.accepts` (The detyped predicate: call the typed predicate on an edge view, otherwise accept.); `MIPRE.CL.Detyping.game` (The actual finite detyped game, using the constructed CL presentations.); `MIPRE.CL.Detyping.question` (Embed a typed question using the type's fixed local graph view.); `MIPRE.CL.Detyping.restrict` (Restrict the strategy's measurements to fixed graph views; its state and dimensions persist.); `MIPRE.CL.Detyping.typedGame` (The actual finite typed game, sampling a uniform ordered edge and common seed.); `MIPRE.CL.Detyping.typedQuestion` (One player's typed question from an edge and common seed.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `sampled_dist_cl`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.DetypingGame` (`MIPRE/Foundations/CL/DetypingGame.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 12 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingGame.lean; blueprint lem:detype-game-soundness

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingGame.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Theorems.Thm_MIPRE_SampledGame_dist_eq_card

/-! # The finite typed and detyped games

This is the game at a fixed verifier index, before ambient-program compilation.
The detyped predicate accepts outside valid edge views. On valid views it calls
the original predicate. The answer alphabets here are unchanged; the separate
program-level cutoff and answer truncation obligations are not hidden here.
-/

noncomputable section

namespace MIPRE.CL.Detyping

open Finset Classical

theorem sampled_dist_cl {J : Type*} [Fintype J] [DecidableEq J]
    (L R : (J → ZMod 2) → (J → ZMod 2)) (x y : J → ZMod 2) :
    SampledGame.dist L R x y = clDist L R x y := by
  rw [SampledGame.dist_eq_card]
  unfold clDist
  congr 2
  apply congrArg Finset.card
  ext s
  simp

variable {T ι A B : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  [Fintype A] [Fintype B]

set_option linter.unusedSectionVars false

/-- Typed questions carry a type and its sampled content. -/
abbrev Question (T ι : Type*) := T × (ι → ZMod 2)

/-- Embed a typed question using the type's fixed local graph view. -/
def question (E : T → T → Prop) [DecidableRel E] (w : Bool) (q : Question T ι) :
    Coord T ι → ZMod 2 := Sum.elim (view E w q.1) q.2

/-- The detyped predicate: call the typed predicate on an edge view, otherwise accept. -/
def accepts (E : T → T → Prop) [DecidableRel E]
    (D : Question T ι → Question T ι → A → B → Bool)
    (x y : Coord T ι → ZMod 2) (a : A) (b : B) : Bool :=
  match select E false (pull .inl x), select E true (pull .inl y) with
  | some u, some v =>
    if E u v ∧ pull .inl x = view E false u ∧ pull .inl y = view E true v then
      D (u, pull .inr x) (v, pull .inr y) a b
    else true
  | _, _ => true

/-- Ordered adjacent pairs, including loops. -/
abbrev Edge (E : T → T → Prop) [DecidableRel E] := ↥(Graph.edges E)

/-- The typed sample space is an ordered edge together with one common content seed. -/
abbrev TypedSeed (E : T → T → Prop) [DecidableRel E] (ι : Type*) := Edge E × (ι → ZMod 2)

/-- One player's typed question from an edge and common seed. -/
def typedQuestion {ℓ : ℕ} {E : T → T → Prop} [DecidableRel E]
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (w : Bool) (z : TypedSeed E ι) : Question T ι :=
  let u := if w then z.1.val.2 else z.1.val.1
  (u, (P w u).eval z.2)

/-- The actual finite typed game, sampling a uniform ordered edge and common seed. -/
def typedGame {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) : Game (Question T ι) (Question T ι) A B := by
  letI : Nonempty (Edge E) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  exact SampledGame.game (typedQuestion (E := E) P false) (typedQuestion P true) D

/-- The actual finite detyped game, using the constructed CL presentations. -/
def game {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) :
    Game (Coord T ι → ZMod 2) (Coord T ι → ZMod 2) A B :=
  SampledGame.game (presentation E false (P false)).eval
    (presentation E true (P true)).eval (accepts E D)

/-- Restrict the strategy's measurements to fixed graph views; its state and dimensions persist. -/
def restrict {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) (S : TensorProductStrategy (game E P D)) :
    TensorProductStrategy (typedGame E hne P D) :=
  S.relabel (typedGame E hne P D) (question E false) (question E true) (.refl A) (.refl B)

end MIPRE.CL.Detyping


