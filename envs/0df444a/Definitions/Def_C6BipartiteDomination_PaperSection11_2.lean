-- Prove2me | Definitions.Def_C6BipartiteDomination_PaperSection11_2
-- name    : C6BipartiteDomination_PaperSection11_2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:57:05.440682+00:00
-- url     : https://prove2.me/theorems/9096a8f0-ff8a-5ce1-a4ba-036c6b87d890
-- title:
--   Paper Section11 2
-- statement:
--   Definitions and structural lemmas for Paper Section11 2, from shouanrenhechun and contributors (shouanrenhechun/Myproofone; see pinned Apache-2.0 LICENSE and source headers)'s pinned Bipartite domination constant c_6 = 8/15 for graphs of maximum degree at most six development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean

import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
namespace C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
noncomputable def paper11K4IncidentSupports (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (u : V) : Finset V := by
  classical
  exact (paper11K4Supports G D).filter fun w =>
    u ∈ paperChosenRepairSet G D hCan hmax w
noncomputable def paper11K4RightVertices (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) : Finset V := by
  classical
  exact (BPart G D).filter fun u =>
    (paper11K4IncidentSupports G D hCan hmax u).Nonempty
noncomputable def paper11K4Edges (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) : Finset (V × V) := by
  classical
  exact (paper11K4Supports G D).biUnion fun w =>
    (paperChosenRepairSet G D hCan hmax w).image fun u => (w, u)
noncomputable def paper11K4Compensation (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (u : V) : Finset V := by
  classical
  exact (paper11K4IncidentSupports G D hCan hmax u).biUnion fun w =>
    sharedCompensation G D (supportX G D w) u
noncomputable def paper11K4Resource (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (u : V) : ℤ := by
  classical
  exact vertexCharge G D u +
    ∑ q ∈ paper11K4Compensation G D hCan hmax u,
      externalCharge G D q
noncomputable def paper11OwnerCompensation (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (u : V) : Finset V := by
  classical
  exact (paper11NegativeIncidentSupports G D hCan hmax u).biUnion fun w =>
    sharedCompensation G D (supportX G D w) u
noncomputable def paper11AllRepairOwners (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) : Finset V :=
  paper11K3RightVertices G D hCan hmax ∪
    paper11K4RightVertices G D hCan hmax
noncomputable def paper11AllCompensation (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) : Finset V := by
  classical
  exact (paper11AllRepairOwners G D hCan hmax).biUnion fun u =>
    paper11OwnerCompensation G D hCan hmax u
noncomputable def paper11NonnegativeSupports (D : Finset V) : Finset V :=
  SPart G D \ paper11NegativeSupports G D
noncomputable def paper11OwnerResource (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (u : V) : ℤ := by
  classical
  exact vertexCharge G D u +
    ∑ q ∈ paper11OwnerCompensation G D hCan hmax u,
      externalCharge G D q
end C6BipartiteDomination


