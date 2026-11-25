-- Prove2me | Definitions.Def_PerfectLib_Gasparian
-- name    : PerfectLib_Gasparian
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T10:24:19.626133+00:00
-- url     : https://prove2.me/theorems/c36efbca-3d7c-44e5-b8f6-074946503234
-- title:
--   Gasparian
-- statement:
--   Definitions and structural lemmas for Gasparian, from Juan Pablo Traverso Gianini (jtraverso/perfect-graphs; see pinned Apache-2.0 LICENSE and source headers)'s pinned Lovasz's perfect graph theorems development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Finset
namespace PerfectGraph
variable {V : Type*} (G : SimpleGraph V)
def IsColOn (S : Finset V) (k : ℕ) : Prop :=
  ∃ c : V → ℕ, (∀ v ∈ S, c v < k) ∧ ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v
end PerfectGraph


