-- Prove2me | Definitions.Def_ErdosPosaLib_EPPacking
-- name    : ErdosPosaLib_EPPacking
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:25:52.716461+00:00
-- url     : https://prove2.me/theorems/a581297d-06f5-4310-829c-daba2c612ddd
-- title:
--   EPPacking
-- statement:
--   Definitions and structural lemmas for EPPacking, from Juan Pablo Traverso Gianini (jtraverso/erdos-posa-cycles; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Erdos-Posa theorem for cycles development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPShort
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace ErdosPosa
variable {V : Type*}
def wt (d : ℕ) : ℤ := if d = 0 then 0 else (d : ℤ) - 2
noncomputable def psi [Fintype V] (H : SimpleGraph V) : ℤ := ∑ v, wt (deg H v)
noncomputable def dsum [Fintype V] (H : SimpleGraph V) : ℕ := ∑ v, deg H v
section deleteEdge
variable [Finite V] {H : SimpleGraph V} {y z : V}
variable [Fintype V]
end deleteEdge
section deleteVerts
variable {H₀ : SimpleGraph V} {T : Set V}
end deleteVerts
end ErdosPosa


