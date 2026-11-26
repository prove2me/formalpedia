-- Prove2me | Definitions.Def_AlonTarsiLib_PlanarSparse
-- name    : AlonTarsiLib_PlanarSparse
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:21:23.999416+00:00
-- url     : https://prove2.me/theorems/b922ae8d-ed6d-5c07-bc96-d7915da71970
-- title:
--   Planar Sparse
-- statement:
--   Definitions and structural lemmas for Planar Sparse, from Juan Pablo Traverso Gianini (jtraverso/alon-tarsi-choosability; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Alon-Tarsi theorem and 3-choosability of planar bipartite graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/PlanarSparse.lean

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Nonplanar
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability
namespace AlonTarsi
variable {V : Type*}
section Faces
variable {H : SimpleGraph V} {σ : Perm H.Dart} (hσ : IsRotationSystem H σ)
include hσ
end Faces
end AlonTarsi


