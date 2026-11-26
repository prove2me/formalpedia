-- Prove2me | Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
-- name    : LeanPool_K5MinorFreeChoosability_Planar_Embedding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:16:25.7764+00:00
-- url     : https://prove2.me/theorems/76992f5a-420b-5833-a0fc-8ce854a44ef7
-- title:
--   Embedding
-- statement:
--   Definitions and structural lemmas for Embedding, from Juan Pablo Traverso Gianini (jtraverso/alon-tarsi-choosability; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Alon-Tarsi theorem and 3-choosability of planar bipartite graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Embedding.lean

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V : Type*} (G : SimpleGraph V)
def dartSymm : Perm G.Dart := Function.Involutive.toPerm _ SimpleGraph.Dart.symm_involutive
structure IsRotationSystem (σ : Perm G.Dart) : Prop where
  fst_apply : ∀ d, (σ d).fst = d.fst
  sameCycle : ∀ d e : G.Dart, d.fst = e.fst → σ.SameCycle d e
structure PlaneMap where
  /-- The rotation: the next dart counterclockwise around the tail. -/
  rot : Perm G.Dart
  isRotationSystem : IsRotationSystem G rot
  eulerDefect_eq_zero : eulerDefect rot (dartSymm G) = 0
def IsPlanar : Prop := Nonempty (PlaneMap G)
namespace PlaneMap
variable {G} (M : PlaneMap G)
def facePerm : Perm G.Dart := M.rot * dartSymm G
def Face : Type _ := Quotient (SameCycle.setoid M.facePerm)
noncomputable def numFaces : ℕ := cycleCount M.facePerm
end PlaneMap
end LeanPool.K5MinorFreeChoosability


