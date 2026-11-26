-- Prove2me | Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
-- name    : LeanPool_K5MinorFreeChoosability_Reach
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:08:55.811396+00:00
-- url     : https://prove2.me/theorems/362198b4-ff19-4899-b0cc-578e9294a231
-- title:
--   Reach
-- statement:
--   Definitions and structural lemmas for Reach, from Juan Pablo Traverso Gianini (jtraverso/alon-tarsi-choosability; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Alon-Tarsi theorem and 3-choosability of planar bipartite graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.K5MinorFreeChoosability
variable {W : Type*}
def RIn (G : SimpleGraph W) (s : Set W) : W → W → Prop :=
  Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∈ s ∧ b ∈ s)
def ConnSet (G : SimpleGraph W) (s : Set W) : Prop :=
  s.Nonempty ∧ ∀ a ∈ s, ∀ b ∈ s, RIn G s a b
def restrict (G : SimpleGraph W) (s : Set W) : SimpleGraph W where
  Adj a b := G.Adj a b ∧ a ∈ s ∧ b ∈ s
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩
namespace RIn
variable {G G' : SimpleGraph W} {s t : Set W} {a b c : W}
end RIn
end LeanPool.K5MinorFreeChoosability


