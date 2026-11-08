-- Prove2me | Definitions.Def_FairFacilityLoc_GroupStructure
-- name    : FairFacilityLoc_GroupStructure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:11:07.340594+00:00
-- url     : https://prove2.me/theorems/4fcfdbab-52ea-4f6b-84e3-ec74d4c8fe17
-- title:
--   Public group structure with sublinear group effects
-- statement:
--   There are $n$ agents $N$ and $m\ge1$ groups $G_1,\dots,G_m$, which are nonempty sets of agents with $G_1\cup\dots\cup G_m=N$ and may overlap. Each group $G_j$ carries a sublinear group effect $E_j$. The **total mass** of group $j$ is $A_j=E_j(\mathbf 1)$.
--
--   This is the public data of the problem: it is known to the mechanism, while the locations are reported.
--
--   **Formalization Note** Definitions 2.1 and 2.2 are bundled in the structure, so every quantifier over group structures ranges over sublinear ones, which matches "on sublinear group effects". The fields force $n\ge1$.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), §2.1, p.14 (PDF p.16); total mass p.15 (PDF p.17)

import Mathlib
import Definitions.Def_FairFacilityLoc_IsGroupEffect
import Definitions.Def_FairFacilityLoc_IsSublinearEffect

open scoped NNReal

namespace FairFacilityLoc

/-- **Public group structure with sublinear group effects** (Yan, Zhou, manuscript, sha256 642a1268…,
§2.1, p.14, PDF p.16): `m ≥ 1` nonempty, possibly overlapping groups `G₁, …, G_m` of the agents
`N = Fin n` with union `N`, each with a sublinear group effect `E j` on `ℝ^{G j}_{≥0}`.

**Formalization Note.** Definitions 2.1 and 2.2 are bundled, because every result of this mission is "on
sublinear group effects": every quantifier over group structures ranges over sublinear ones. The fields
force `n ≥ 1`. Agents and groups are `Fin n` and `Fin m`, 0-based. -/
structure GroupStructure (n m : ℕ) where
  /-- The groups. -/
  G : Fin m → Finset (Fin n)
  /-- The group effects. -/
  E : ∀ j, (↥(G j) → ℝ≥0) → ℝ≥0
  /-- There is at least one group. -/
  m_pos : 0 < m
  /-- The groups are nonempty. -/
  nonempty : ∀ j, (G j).Nonempty
  /-- The union of the groups is `N`. -/
  cover : ∀ i, ∃ j, i ∈ G j
  /-- Each `E j` is a group effect (Definition 2.1). -/
  isGroupEffect : ∀ j, IsGroupEffect (E j)
  /-- Each `E j` is sublinear (Definition 2.2). -/
  isSublinear : ∀ j, IsSublinearEffect (E j)

/-- The **total mass** `A_j = E_j(1)` of group `j` (p.15, PDF p.17). -/
def GroupStructure.totalMass {n m : ℕ} (G : GroupStructure n m) (j : Fin m) : ℝ≥0 :=
  G.E j 1

end FairFacilityLoc


