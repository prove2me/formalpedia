-- Prove2me | Definitions.Def_TreeStack_Consolidation
-- name    : TreeStack_Consolidation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:14:39.296242+00:00
-- url     : https://prove2.me/theorems/c3534ccc-d3a4-4cb1-b9e7-b66649cbed2e
-- title:
--   Consolidation
-- statement:
--   Definitions and structural lemmas for Consolidation, from jfairfaxball-348 (jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees; see pinned Apache-2.0 LICENSE and README.md)'s pinned TreeStack: Csernák-Soukup stacking number equality stack(T) = estim(T) for nontrivial trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean

import Mathlib
import Definitions.Def_TreeStack_HeightSource
set_option autoImplicit false
namespace TreeStack
open scoped BigOperators Classical
namespace OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
noncomputable def auxSourceFiber
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (r : V) : Finset V :=
  (Finset.univ : Finset V).filter fun v =>
    auxSource C ambientRoot hScores v = r
def TreePathConnected (S : Finset V) : Prop :=
  ∀ ⦃x y : V⦄, x ∈ S → y ∈ S →
    ∃ p : T.graph.Walk x y,
      p.IsPath ∧ ∀ z ∈ p.support, z ∈ S
def HeightDominated
    (h : V → ℕ) (S : Finset V) (r : V) : Prop :=
  r ∈ S ∧ ∀ v ∈ S, h v ≤ T.graph.dist r v
noncomputable def auxSourceCarrier
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (R : Finset V) : Finset V :=
  (Finset.univ : Finset V).filter fun v =>
    auxSource C ambientRoot hScores v ∈ R
end OrientedBranch
end TreeStack


