-- Prove2me | Definitions.Def_C6BipartiteDomination_PaperSection10
-- name    : C6BipartiteDomination_PaperSection10
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:54:05.440036+00:00
-- url     : https://prove2.me/theorems/9783706d-9e2c-4112-b198-add86bf6b95f
-- title:
--   Paper Section10
-- statement:
--   Definitions and structural lemmas for Paper Section10, from shouanrenhechun and contributors (shouanrenhechun/Myproofone; see pinned Apache-2.0 LICENSE and source headers)'s pinned Bipartite domination constant c_6 = 8/15 for graphs of maximum degree at most six development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection10.lean

import Definitions.Def_C6BipartiteDomination_PaperSection9
set_option autoImplicit true
namespace C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
structure Paper10SpecialWitness
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (q : V) where
  u : V
  w₁ : V
  w₂ : V
  z : V
  w_ne : w₁ ≠ w₂
  w₁S : w₁ ∈ SPart G D
  w₂S : w₂ ∈ SPart G D
  w₁negative : externalCharge G D w₁ < 0
  w₂negative : externalCharge G D w₂ < 0
  uB : u ∈ BPart G D
  repair₁ : u ∈ paperChosenRepairSet G D hCan hmax w₁
  repair₂ : u ∈ paperChosenRepairSet G D hCan hmax w₂
  qShared₁ : q ∈ sharedCompensation G D (supportX G D w₁) u
  qShared₂ : q ∈ sharedCompensation G D (supportX G D w₂) u
  zSupport₁ : z ∈ supportX G D w₁
  zSupport₂ : z ∈ supportX G D w₂
  qNeighborhood : neighborhoodIn G D q = {u, z}
def IsPaper10SpecialQ
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (q : V) : Prop :=
  Nonempty (Paper10SpecialWitness G hCan hmax q)
noncomputable def paper10SpecialQSet
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) : Finset V := by
  classical
  exact Finset.univ.filter (IsPaper10SpecialQ G hCan hmax)
noncomputable def paper10SpecialEndpoint
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (q : V) : Option V := by
  classical
  exact if h : IsPaper10SpecialQ G hCan hmax q then
    some (Classical.choice h).z else none
noncomputable def paper10SpecialFiber
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (Q : Finset V)
    (hQ : ∀ q ∈ Q, IsPaper10SpecialQ G hCan hmax q) (z : V) : Finset V := by
  classical
  exact Q.filter (fun q => paper10SpecialEndpoint G hCan hmax q = some z)
end C6BipartiteDomination


