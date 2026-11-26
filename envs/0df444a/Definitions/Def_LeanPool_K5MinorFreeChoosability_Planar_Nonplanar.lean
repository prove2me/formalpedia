-- Prove2me | Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Nonplanar
-- name    : LeanPool_K5MinorFreeChoosability_Planar_Nonplanar
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:20:52.910805+00:00
-- url     : https://prove2.me/theorems/6ba77627-99d2-4a7e-ad8a-8abf00a383eb
-- title:
--   Nonplanar
-- statement:
--   Definitions and structural lemmas for Nonplanar, from Juan Pablo Traverso Gianini (jtraverso/alon-tarsi-choosability; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Alon-Tarsi theorem and 3-choosability of planar bipartite graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Nonplanar.lean

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorClosed
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V : Type*} {G : SimpleGraph V}
section Faces
variable {σ : Perm G.Dart} (hσ : IsRotationSystem G σ)
include hσ
end Faces
end LeanPool.K5MinorFreeChoosability


