-- Prove2me | Definitions.Def_TreeStack_PebblingMove
-- name    : TreeStack_PebblingMove
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T22:05:28.492822+00:00
-- url     : https://prove2.me/theorems/dc4c417e-98c8-5ebf-9364-cb70b4a1cbf9
-- title:
--   Pebbling Move
-- statement:
--   Definitions and structural lemmas for Pebbling Move, from jfairfaxball-348 (jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees; see pinned Apache-2.0 LICENSE and README.md)'s pinned TreeStack: Csernák-Soukup stacking number equality stack(T) = estim(T) for nontrivial trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/PebblingMove.lean

import Mathlib
import Definitions.Def_TreeStack_Basic
set_option autoImplicit false
namespace TreeStack
def move {V : Type*} [DecidableEq V] (C : Configuration V) (u v : V) :
    Configuration V :=
  Function.update (Function.update C u (C u - 2)) v (C v + 1)
def PebbleStep {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (C D : Configuration V) : Prop :=
  ∃ u v, G.Adj u v ∧ 2 ≤ C u ∧ D = move C u v
def Reach {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (C D : Configuration V) : Prop :=
  Relation.ReflTransGen (PebbleStep G) C D
def StackedAt {V : Type*} (C : Configuration V) (r : V) : Prop :=
  0 < C r ∧ ∀ v, v ≠ r → C v = 0
def StackableAt {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (C : Configuration V) (r : V) : Prop :=
  ∃ D, Reach G C D ∧ StackedAt D r
def Stackable {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (C : Configuration V) : Prop :=
  ∃ r, StackableAt G C r
def UniversalStackable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∀ C : Configuration V, mass C = t → Stackable G C
def oneOn {V : Type*} [DecidableEq V] (s : Finset V) : Configuration V :=
  fun v => if v ∈ s then 1 else 0
end TreeStack


