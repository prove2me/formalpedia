-- Prove2me | Definitions.Def_C6BipartiteDomination_PaperSection11
-- name    : C6BipartiteDomination_PaperSection11
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:54:53.558899+00:00
-- url     : https://prove2.me/theorems/53d87f08-ccdd-4030-b6e6-39f00ca083ef
-- title:
--   Paper Section11
-- statement:
--   Definitions and structural lemmas for Paper Section11, from shouanrenhechun and contributors (shouanrenhechun/Myproofone; see pinned Apache-2.0 LICENSE and source headers)'s pinned Bipartite domination constant c_6 = 8/15 for graphs of maximum degree at most six development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean

import Definitions.Def_C6BipartiteDomination_PaperSection10
set_option autoImplicit true
namespace C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
def paper11LeftDegree (E : Finset (V × V)) (R : Finset V) (w : V) : ℕ :=
  (E.filter fun e => e.1 = w).card
def paper11RightDegree (E : Finset (V × V)) (L : Finset V) (u : V) : ℕ :=
  (E.filter fun e => e.2 = u).card
variable (G : SimpleGraph V)
noncomputable def paper11NegativeSupports (D : Finset V) : Finset V := by
  classical
  exact (SPart G D).filter fun w => externalCharge G D w < 0
noncomputable def paper11K3Supports (D : Finset V) : Finset V := by
  classical
  exact (paper11NegativeSupports G D).filter fun w => kCharge G D w = 3
noncomputable def paper11K4Supports (D : Finset V) : Finset V := by
  classical
  exact (paper11NegativeSupports G D).filter fun w => kCharge G D w = 4
noncomputable def paper11K3IncidentSupports (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (u : V) : Finset V := by
  classical
  exact (paper11K3Supports G D).filter fun w =>
    u ∈ paperChosenRepairSet G D hCan hmax w
noncomputable def paper11NegativeIncidentSupports (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (u : V) : Finset V := by
  classical
  exact (paper11NegativeSupports G D).filter fun w =>
    u ∈ paperChosenRepairSet G D hCan hmax w
noncomputable def paper11K3RightVertices (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) : Finset V := by
  classical
  exact (BPart G D).filter fun u =>
    (paper11K3IncidentSupports G D hCan hmax u).Nonempty
noncomputable def paper11K3Edges (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) : Finset (V × V) := by
  classical
  exact (paper11K3Supports G D).biUnion fun w =>
    (paperChosenRepairSet G D hCan hmax w).image fun u => (w, u)
noncomputable def paper11K3Compensation (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (u : V) : Finset V := by
  classical
  exact (paper11K3IncidentSupports G D hCan hmax u).biUnion fun w =>
    sharedCompensation G D (supportX G D w) u
noncomputable def paper11K3SpecialBudgetVertices (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) : Finset V := by
  classical
  exact (paper11K3RightVertices G D hCan hmax).filter fun u =>
    xCharge G D u = 0 ∧
      paper11RightDegree (paper11K3Edges G D hCan hmax)
        (paper11K3Supports G D) u = 2
noncomputable def paper11K3AvailableResource (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (u : V) : ℤ := by
  classical
  exact vertexCharge G D u +
    (∑ q ∈ paper11K3Compensation G D hCan hmax u, externalCharge G D q) +
      if u ∈ paper11K3SpecialBudgetVertices G D hCan hmax then 7 else 0
end C6BipartiteDomination


