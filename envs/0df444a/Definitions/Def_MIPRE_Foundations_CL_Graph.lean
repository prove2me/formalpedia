-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_Graph
-- name    : MIPRE_Foundations_CL_Graph
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:08:38.722353+00:00
-- url     : https://prove2.me/theorems/90fb5e3d-0ed6-4d0c-b97c-3fc037a20764
-- title:
--   Definitions of Graph: The two-level graph sampler The graph may have loops
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.Graph` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The two-level graph sampler. The graph may have loops. Its law is uniform on ordered adjacent pairs, so each loop is counted once. This file supplies the semantic CL presentations; compiling their finite graph table into an ambient sampler program is a separate obligation.
--
--   **Definitions** (11): `MIPRE.CL.Graph.Coord` (Four binary blocks: player, vertex/neighbor indicator, vertex.); `MIPRE.CL.Graph.decode` (Decode the finite graph table; malformed blocks have no decoded vertex.); `MIPRE.CL.Graph.edges` (Ordered edges; a loop contributes once.); `MIPRE.CL.Graph.encode` (A vertex's one-hot indicator together with its neighbor indicator.); `MIPRE.CL.Graph.localValid` (The local valid-view predicate, stated on the seed before applying the graph sampler.); `MIPRE.CL.Graph.mask` (The second stage keeps just the relevant opposite neighbor bit when decoding succeeds.); `MIPRE.CL.Graph.own` (The first factor consists of the two blocks belonging to one player.); `MIPRE.CL.Graph.pairSeed` (A seed encoding a pair of types.); `MIPRE.CL.Graph.presentation` (The actual two-level CL presentation: own blocks, then one opposite neighbor bit.); `MIPRE.CL.Graph.second` (The graph sampler's second-stage linear map, on the entire remaining factor.); `MIPRE.CL.Graph.validSeeds` (The valid seeds, expressed as an image so their exact number is transparent.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `mask_subset`, `mem_own`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.Graph` (`MIPRE/Foundations/CL/Graph.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 2 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Graph.lean; blueprint lem:detype-graph

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Graph.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic

/-! # The two-level graph sampler

The graph may have loops. Its law is uniform on ordered adjacent pairs, so each
loop is counted once. This file supplies the semantic CL presentations; compiling
their finite graph table into an ambient sampler program is a separate obligation.
-/

noncomputable section

namespace MIPRE.CL.Graph

open Finset Classical

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- Four binary blocks: player, vertex/neighbor indicator, vertex. -/
abbrev Coord (T : Type*) := Bool × (Bool × T)

/-- A vertex's one-hot indicator together with its neighbor indicator. -/
def encode (E : T → T → Prop) [DecidableRel E] (u : T) : Bool × T → ZMod 2 :=
  fun p => if p.1 then (if E u p.2 then 1 else 0) else (if p.2 = u then 1 else 0)

/-- Decode the finite graph table; malformed blocks have no decoded vertex. -/
def decode (E : T → T → Prop) [DecidableRel E] (x : Bool × T → ZMod 2) : Option T :=
  if h : ∃ u, x = encode E u then some h.choose else none

/-- The first factor consists of the two blocks belonging to one player. -/
def own (w : Bool) : Finset (Coord T) := univ.filter fun p => p.1 = w

@[simp] theorem mem_own (w : Bool) (p : Coord T) : p ∈ own w ↔ p.1 = w := by
  simp [own]

/-- The second stage keeps just the relevant opposite neighbor bit when decoding succeeds. -/
def mask (E : T → T → Prop) [DecidableRel E] (w : Bool) (x : Coord T → ZMod 2) :
    Finset (Coord T) :=
  match decode E (fun p => x (w, p)) with
  | some u => {(!w, (true, u))}
  | none => ∅

/-- The second-stage mask is contained in the complement of the first factor. -/
theorem mask_subset (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (x : Coord T → ZMod 2) : mask E w x ⊆ (own w)ᶜ := by
  unfold mask
  split
  · intro p hp
    simp only [mem_singleton] at hp
    subst p
    simp
  · exact empty_subset _

/-- The graph sampler's second-stage linear map, on the entire remaining factor. -/
def second (E : T → T → Prop) [DecidableRel E] (w : Bool) (x : Coord T → ZMod 2) :
    RegLinear (ZMod 2) (own (T := T) w)ᶜ where
  toLinearMap := proj (mask E w x)
  proj_comp_proj' z := by
    rw [proj_proj_of_subset (mask_subset E w x), proj_proj_of_subset' (mask_subset E w x)]

/-- The actual two-level CL presentation: own blocks, then one opposite neighbor bit. -/
def presentation (E : T → T → Prop) [DecidableRel E] (w : Bool) :
    CLFun (ZMod 2) (Coord T) 2 :=
  .cons (own w) (RegLinear.id (own w)) fun x =>
    .cons (own w)ᶜ (second E w x) fun _ => .zero

/-- The local valid-view predicate, stated on the seed before applying the graph sampler. -/
def localValid (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (z : Coord T → ZMod 2) : Prop :=
  ∃ u, (fun p => z (w, p)) = encode E u ∧ z (!w, (true, u)) = 1

/-- A seed encoding a pair of types. Each ordered pair has precisely this one seed. -/
def pairSeed (E : T → T → Prop) [DecidableRel E] (uv : T × T) : Coord T → ZMod 2 :=
  fun p => encode E (if p.1 then uv.2 else uv.1) p.2

/-- Ordered edges; a loop contributes once. -/
def edges (E : T → T → Prop) [DecidableRel E] : Finset (T × T) :=
  univ.filter fun p => E p.1 p.2

/-- The valid seeds, expressed as an image so their exact number is transparent. -/
def validSeeds (E : T → T → Prop) [DecidableRel E] : Finset (Coord T → ZMod 2) :=
  (edges E).image (pairSeed E)

end MIPRE.CL.Graph

end


