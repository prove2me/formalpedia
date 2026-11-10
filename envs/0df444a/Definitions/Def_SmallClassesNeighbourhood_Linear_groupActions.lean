-- Prove2me | Definitions.Def_SmallClassesNeighbourhood_Linear_groupActions
-- name    : SmallClassesNeighbourhood_Linear_groupActions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T16:35:05.943135+00:00
-- url     : https://prove2.me/theorems/19d4552a-72c4-4db2-b0a7-e360b4890737
-- title:
--   Tuple orbits and setwise stabilizers
-- statement:
--   Let a finite group H act on a finite set Γ and let S_1,…,S_k be an ordered tuple of subsets. Define
--
--   $$H_{S_1,\ldots,S_k}=\{h\in H:hS_i=S_i\text{ for all }i\},\qquad \operatorname{Orb}_H(S_1,\ldots,S_k)=\{(hS_1,\ldots,hS_k):h\in H\}.$$
--
--   The stabilizer is an actual subgroup, and the orbit is a finite image with duplicate tuples removed. No faithfulness of the action is required. Empty tuples and empty acted-on sets are allowed. This interface supports the full orbit–stabilizer equality and subset bound in Lemma 13.
-- source:
--   John Sylvester, Viktor Zamaraev, Maksim Zhukovskii, STOC 2027 submission #1126 (October 2026), §2.3, printed pp. 8–9 (PDF pp. 9–10)

import Definitions.Def_SmallClassesNeighbourhood_Linear_graphBasics

noncomputable section

namespace SmallClassesNeighbourhood.Linear

variable {H Γ : Type} [Group H] [Fintype H] [Fintype Γ] [DecidableEq Γ] [MulAction H Γ]

def tupleStabilizer {k : ℕ} (S : Fin k → Finset Γ) : Subgroup H where
  carrier := {h | ∀ i : Fin k, ∀ x : Γ, h • x ∈ S i ↔ x ∈ S i}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb i x
    simpa only [mul_smul] using (ha i (b • x)).trans (hb i x)
  inv_mem' := by
    intro a ha i x
    have h := ha i (a⁻¹ • x)
    simpa using h.symm

def tupleOrbit {k : ℕ} (S : Fin k → Finset Γ) : Finset (Fin k → Finset Γ) := by
  classical
  exact Finset.univ.image (fun h : H => fun i => (S i).image (fun x => h • x))

end SmallClassesNeighbourhood.Linear


