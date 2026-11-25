-- Prove2me | Definitions.Def_ErdosPosaLib_EPMaximal
-- name    : ErdosPosaLib_EPMaximal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:27:40.002805+00:00
-- url     : https://prove2.me/theorems/8f4050bd-0873-41b6-ad24-3ea80c5bded5
-- title:
--   EPMaximal
-- statement:
--   Definitions and structural lemmas for EPMaximal, from Juan Pablo Traverso Gianini (jtraverso/erdos-posa-cycles; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Erdos-Posa theorem for cycles development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMaximal.lean

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPPacking
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace ErdosPosa
variable {V : Type*}
def Deg023 (H : SimpleGraph V) : Prop := ∀ v, deg H v = 0 ∨ deg H v = 2 ∨ deg H v = 3
def IsMax023 (G H : SimpleGraph V) : Prop :=
  H ≤ G ∧ Deg023 H ∧ ∀ K, K ≤ G → Deg023 K → H ≤ K → ∀ u v, K.Adj u v → H.Adj u v
variable [Finite V] {G H : SimpleGraph V}
end ErdosPosa


