-- Prove2me | Definitions.Def_LeanFormalizations_Combinatorics_CombinatorialMap_Basic
-- name    : LeanFormalizations_Combinatorics_CombinatorialMap_Basic
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:44:13.918975+00:00
-- url     : https://prove2.me/theorems/1390a814-14c7-445a-9e76-046566b95237
-- title:
--   Combinatorial maps described by permutations
-- statement:
--   A combinatorial map is specified by vertex, edge and face permutations on darts, with their product equal to the identity and the edge permutation a fixed-point-free involution. This also defines permutation-preserving maps, isomorphisms, and vertices, edges and faces as permutation cycles.

-- Extracted dependency interfaces and their necessary proofs.
import Mathlib
import Mathlib.GroupTheory.Perm.Cycle.Basic

set_option autoImplicit true

/-
Copyright (c) 2024 Kyle Miller, Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Rida Hamadani
-/


structure CombinatorialMap (D : Type*) where


  vertexPerm : Equiv.Perm D
   
  edgePerm : Equiv.Perm D


  facePerm : Equiv.Perm D
  face_mul_edge_mul_vertex_eq_one : facePerm * edgePerm * vertexPerm = 1
  edgePerm_involutive : Function.Involutive edgePerm
  isEmpty_fixedPoints_edgePerm : IsEmpty (Function.fixedPoints edgePerm)

namespace CombinatorialMap

variable {D D' : Type*} {M : CombinatorialMap D} {M' : CombinatorialMap D'}


structure Hom (M : CombinatorialMap D) (M' : CombinatorialMap D') where
   
  toFun : D → D'
  vertex_comm : toFun ∘ M.vertexPerm = M'.vertexPerm ∘ toFun
  edge_comm : toFun ∘ M.edgePerm = M'.edgePerm ∘ toFun
  face_comm : toFun ∘ M.facePerm = M'.facePerm ∘ toFun


structure Iso (M : CombinatorialMap D) (M' : CombinatorialMap D') extends (D ≃ D'), Hom M M'

 


abbrev Vertex (M : CombinatorialMap D) :=
  Quotient (Equiv.Perm.SameCycle.setoid M.vertexPerm)

 
abbrev Edge (M : CombinatorialMap D) :=
  Quotient (Equiv.Perm.SameCycle.setoid M.edgePerm)

 
abbrev Face (M : CombinatorialMap D) :=
  Quotient (Equiv.Perm.SameCycle.setoid M.facePerm)


private noncomputable instance [Fintype D] [DecidableEq D] {w : D} :
    Fintype {u | M.vertexPerm.SameCycle w u} :=
  Fintype.ofFinite {u | M.vertexPerm.SameCycle w u}


noncomputable instance [Fintype D] : Fintype M.Vertex :=
  Fintype.ofFinite M.Vertex

noncomputable instance [Fintype D] : Fintype M.Edge :=
  Fintype.ofFinite M.Edge

noncomputable instance [Fintype D] : Fintype M.Face :=
  Fintype.ofFinite M.Face


end CombinatorialMap


