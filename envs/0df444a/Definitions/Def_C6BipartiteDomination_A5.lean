-- Prove2me | Definitions.Def_C6BipartiteDomination_A5
-- name    : C6BipartiteDomination_A5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:42:54.836483+00:00
-- url     : https://prove2.me/theorems/c8eb6f4a-14ad-4b07-b618-985e0dc4cbb3
-- title:
--   A5
-- statement:
--   Definitions and structural lemmas for A5, from shouanrenhechun and contributors (shouanrenhechun/Myproofone; see pinned Apache-2.0 LICENSE and source headers)'s pinned Bipartite domination constant c_6 = 8/15 for graphs of maximum degree at most six development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A5.lean

import Definitions.Def_C6BipartiteDomination_A4
set_option autoImplicit true
namespace C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
noncomputable def ZPart (D : Finset V) : Finset V := by
  classical
  exact D.filter fun z => ∀ u ∈ D, ¬ G.Adj z u
noncomputable def BPart (D : Finset V) : Finset V := D \ ZPart G D
noncomputable def W0Part (D : Finset V) : Finset V := by
  classical
  exact (Finset.univ \ D).filter fun w => ∀ b ∈ BPart G D, ¬ G.Adj b w
noncomputable def Z0Part (D : Finset V) : Finset V := by
  classical
  exact ZPart G D |>.filter fun z => ∀ w ∈ W0Part G D, ¬ G.Adj z w
noncomputable def Z1Part (D : Finset V) : Finset V := by
  classical
  exact (ZPart G D).filter fun z => ∃ w ∈ W0Part G D, G.Adj z w
noncomputable def degreeWithinSet (S : Finset V) (v : V) : ℕ := by
  classical
  exact (S.filter fun u => G.Adj v u).card
def ProperInducedMainBound : Prop :=
  ∀ S : Finset V, S.card < (Finset.univ : Finset V).card →
    (∀ v ∈ S, ∃ u ∈ S, G.Adj v u) →
    (∀ v ∈ S, degreeWithinSet G S v ≤ 6) →
    ∀ E, MinimumBipartiteDominatingOn G S E →
      15 * E.card ≤ 8 * S.card
end C6BipartiteDomination


