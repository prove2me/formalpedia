-- Prove2me | Definitions.Def_TreeStack_Estimator
-- name    : TreeStack_Estimator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T22:05:26.882111+00:00
-- url     : https://prove2.me/theorems/859a13bd-3e2c-51c0-8c51-a7aa20704960
-- title:
--   Estimator
-- statement:
--   Definitions and structural lemmas for Estimator, from jfairfaxball-348 (jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees; see pinned Apache-2.0 LICENSE and README.md)'s pinned TreeStack: Csernák-Soukup stacking number equality stack(T) = estim(T) for nontrivial trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean

import Mathlib
import Definitions.Def_TreeStack_Basic
set_option autoImplicit false
namespace TreeStack
open scoped BigOperators Classical
noncomputable def leafVertices {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : Finset V :=
  (Finset.univ : Finset V).filter fun v =>
    v ≠ r ∧ T.graph.degree v = 1
noncomputable def sigmaVertices {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : Finset V :=
  (Finset.univ : Finset V).filter fun v =>
    v = r ∨ 1 < T.graph.degree v
noncomputable def nonRootInternalVertices {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : Finset V :=
  (Finset.univ : Finset V).filter fun v =>
    v ≠ r ∧ 1 < T.graph.degree v
noncomputable def leafCount {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : ℕ :=
  (leafVertices T r).card
noncomputable def sigma {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : ℕ :=
  1 + ∑ v ∈ sigmaVertices T r,
    T.graph.degree v * 2 ^ T.graph.dist r v
noncomputable def rootEstimate {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : ℕ :=
  sigma T r + leafCount T r
noncomputable def estim {V : Type*} [Fintype V]
    (T : FiniteTree V) : ℕ :=
  (Finset.univ : Finset V).sup (rootEstimate T)
end TreeStack


