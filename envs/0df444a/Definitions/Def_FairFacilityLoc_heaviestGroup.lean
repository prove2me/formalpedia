-- Prove2me | Definitions.Def_FairFacilityLoc_heaviestGroup
-- name    : FairFacilityLoc_heaviestGroup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:12:17.534206+00:00
-- url     : https://prove2.me/theorems/ada96d88-ce2c-4446-80a3-8983833b613a
-- title:
--   The index $h$: smallest index of maximum total mass
-- statement:
--   $h$ is the smallest index with $A_h=\max_jA_j$, where $A_j=E_j(\mathbf 1)$ is the total mass of group $j$.
--
--   For $d\ge4$ the mechanism uses only this group.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), §2.2, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_FairFacilityLoc_GroupStructure

namespace FairFacilityLoc

/-- **The index `h`** (Yan, Zhou, manuscript, sha256 642a1268…, §2.2, p.16, PDF p.18): the smallest index
with `A_h = max_j A_j`.

**Formalization Note.** The least element of the set of maximizers of `A_j`, which is nonempty because
`Fin m` is finite and nonempty. -/
noncomputable def heaviestGroup {n m : ℕ} (G : GroupStructure n m) : Fin m :=
  (Finset.univ.filter fun j => ∀ j', G.totalMass j' ≤ G.totalMass j).min' (by
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ G.totalMass
      ⟨⟨0, G.m_pos⟩, Finset.mem_univ _⟩
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j' => hj j' (Finset.mem_univ _)⟩⟩)

end FairFacilityLoc


