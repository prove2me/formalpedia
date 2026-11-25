-- Prove2me | Definitions.Def_ErdosPosaLib_EPCyc
-- name    : ErdosPosaLib_EPCyc
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:19:26.987409+00:00
-- url     : https://prove2.me/theorems/5d5cb162-bc66-4003-b03d-319ae2c20f5f
-- title:
--   EPCyc
-- statement:
--   Definitions and structural lemmas for EPCyc, from Juan Pablo Traverso Gianini (jtraverso/erdos-posa-cycles; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Erdos-Posa theorem for cycles development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace ErdosPosa
variable {V : Type*}
def restr (H : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj a b := H.Adj a b ∧ a ∈ S ∧ b ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun a h => H.loopless.irrefl a h.1⟩
noncomputable def deg (H : SimpleGraph V) (v : V) : ℕ := (H.neighborSet v).ncard
def Cyc (H : SimpleGraph V) (S : Set V) : Prop := ¬ (restr H S).IsAcyclic
def MinCyc (H : SimpleGraph V) (T : Set V) : Prop :=
  Cyc H T ∧ ∀ T' ⊆ T, Cyc H T' → T' = T
end ErdosPosa


