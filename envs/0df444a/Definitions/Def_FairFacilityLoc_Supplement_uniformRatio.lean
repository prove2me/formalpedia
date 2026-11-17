-- Prove2me | Definitions.Def_FairFacilityLoc_Supplement_uniformRatio
-- name    : FairFacilityLoc_Supplement_uniformRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:26:53.136022+00:00
-- url     : https://prove2.me/theorems/b5199cca-e67e-4e25-b58b-1542615eba50
-- title:
--   Approximation ratio restricted to uniform group structures
-- statement:
--   A group structure is **uniform** when its linear groups partition the agents, have one common size, and use the common normalized weight $1/K$ on every member of a size-$K$ group. Thus every group has total mass one.
--
--   For a deterministic mechanism $M$ in dimension $d$, its ratio on uniform group structures is
--
--   $$
--   \rho_M^{\mathrm{unif}}(d)=\sup_{n,m,\mathcal G\ \mathrm{uniform},\,x}
--     \frac{F(M(x;\mathcal G);x,\mathcal G)}{\operatorname{OPT}(x,\mathcal G)}.
--   $$
--
--   This is the restricted worst-case ratio used in Theorem 4.1.
--
--   **Formalization Note** Groups and agents are 0-based. The ratio is valued in $[0,\infty]$ and uses the published conventions $0/0=1$ and $a/0=\infty$ for $a>0$.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), §4, pp.51–52 (PDF pp.53–54)

import Mathlib
import Definitions.Def_FairFacilityLoc_ratio

open scoped NNReal ENNReal

namespace FairFacilityLoc.Supplement

set_option autoImplicit false

/-- A public group structure is **uniform** when its groups are pairwise disjoint and have one
common size, and every group uses the linear effect with weight `1 / K` on each of its `K`
members (Yan–Zhou, *Fair and Strategyproof Facility Location in Euclidean Space*, manuscript,
sha256 642a1268…, §4, p.51, PDF p.53).

The cover condition is already a field of `FairFacilityLoc.GroupStructure`, so pairwise
disjointness makes the groups a partition. The displayed effect gives every group total mass one;
this is the normalization fixed by the paper immediately before Theorem 4.1. -/
def IsUniform {n m : ℕ} (G : FairFacilityLoc.GroupStructure n m) : Prop :=
  (∀ j k, j ≠ k → Disjoint (G.G j) (G.G k)) ∧
    (∀ j k, (G.G j).card = (G.G k).card) ∧
      ∀ (j : Fin m) (u : ↥(G.G j) → ℝ≥0),
        G.E j u = (∑ i, u i) / (G.G j).card

/-- The approximation ratio of `M` restricted to uniform group structures (Yan–Zhou,
manuscript, sha256 642a1268…, §4, pp.51–52, PDF pp.53–54).

**Formalization Note.** The supremum is in `ℝ≥0∞`, with the published `ratioAt` conventions
`0/0 = 1` and `a/0 = ∞`. It ranges over all agent and group counts, all normalized uniform
structures, and all profiles. -/
noncomputable def uniformRatio {d : ℕ} (M : FairFacilityLoc.Mechanism d) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (m : ℕ) (G : FairFacilityLoc.GroupStructure n m) (_hG : IsUniform G)
    (x : Fin n → GeoSemialgCSP.E d), FairFacilityLoc.ratioAt M G x

end FairFacilityLoc.Supplement


