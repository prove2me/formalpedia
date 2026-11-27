-- Prove2me | Definitions.Def_TreeStack_LeafSlack
-- name    : TreeStack_LeafSlack
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:12:39.675073+00:00
-- url     : https://prove2.me/theorems/2214f0a3-80ef-4ae3-844c-0ca34d57adc9
-- title:
--   Leaf Slack
-- statement:
--   Definitions and structural lemmas for Leaf Slack, from jfairfaxball-348 (jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees; see pinned Apache-2.0 LICENSE and README.md)'s pinned TreeStack: Csernák-Soukup stacking number equality stack(T) = estim(T) for nontrivial trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
set_option autoImplicit false
namespace TreeStack
open scoped BigOperators Classical
namespace OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
noncomputable def ambientLeaves : Finset V :=
  (Finset.univ : Finset V).filter fun v => T.graph.degree v = 1
noncomputable def ambientLeafCount : ℕ :=
  (ambientLeaves (T := T)).card
noncomputable def auxConfigurationSlack
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) : ℤ :=
  ∑ v : V,
    (auxWeightInt C ambientRoot hScores v - 1) * (C v : ℤ)
noncomputable def auxLeafSlack
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) : ℤ :=
  ∑ v ∈ ambientLeaves (T := T),
    (auxWeightInt C ambientRoot hScores v - 1)
noncomputable def ambientInternalVertices : Finset V :=
  (Finset.univ : Finset V).filter fun v => 1 < T.graph.degree v
noncomputable def auxInternalDegreePotential
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) : ℤ :=
  ∑ v ∈ ambientInternalVertices (T := T),
    (T.graph.degree v : ℤ) * auxWeightInt C ambientRoot hScores v
noncomputable def auxCompactPotential
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) : ℤ :=
  (ambientLeafCount (T := T) : ℤ) +
    auxInternalDegreePotential C ambientRoot hScores
noncomputable def rootedInternalPotential
    (T : FiniteTree V) (r : V) : ℕ :=
  ∑ v ∈ ambientInternalVertices (T := T),
    T.graph.degree v * 2 ^ T.graph.dist r v
end OrientedBranch
end TreeStack


