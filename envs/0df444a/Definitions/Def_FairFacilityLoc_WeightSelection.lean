-- Prove2me | Definitions.Def_FairFacilityLoc_WeightSelection
-- name    : FairFacilityLoc_WeightSelection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:12:40.141565+00:00
-- url     : https://prove2.me/theorems/60947506-e597-43f6-8784-22117d0ef115
-- title:
--   A choice of weight sets from the public group structure
-- statement:
--   For every group structure and every group $j$, a choice of a weight set $K_j$ of $E_j$. The choice may depend on the public group structure and not on the reports. Examples are $K(E_j)$ of Proposition 2.3 (a), and $\{w_j\mathbf 1\}$ for a linear group.
--
--   The Score-Balanced mechanism for $d\le3$ depends on this choice, so its results are stated for every choice.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), §2.2, p.16 (PDF p.18); §3.3, p.47 (PDF p.49)

import Mathlib
import Definitions.Def_FairFacilityLoc_GroupStructure
import Definitions.Def_FairFacilityLoc_IsWeightSet

open scoped NNReal

namespace FairFacilityLoc

/-- **A choice of weight sets** (Yan, Zhou, manuscript, sha256 642a1268…, §2.2, p.16, PDF p.18: "the
mechanism fixes a weight set `K_j` of each `E_j` independent of the reports"; p.47, PDF p.49: "every choice
of weight sets from the public group structure").

**Formalization Note.** `K` takes the group structure and no profile, which is "independent of the
reports". The mechanism `M_d` depends on the choice, and the statements hold for every one. -/
structure WeightSelection where
  /-- The weight set `K_j` chosen for group `j` of the group structure. -/
  K : ∀ {n m : ℕ} (G : GroupStructure n m) (j : Fin m), Set (↥(G.G j) → ℝ≥0)
  /-- Every chosen set is a weight set of its group effect. -/
  isWeightSet : ∀ {n m : ℕ} (G : GroupStructure n m) (j : Fin m), IsWeightSet (G.E j) (K G j)

end FairFacilityLoc


