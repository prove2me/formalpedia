-- Prove2me | Definitions.Def_FairFacilityLoc_canonicalWeightSet
-- name    : FairFacilityLoc_canonicalWeightSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:17.476202+00:00
-- url     : https://prove2.me/theorems/58674e2a-1137-480d-8179-623cb22c568d
-- title:
--   The set $K(E)$ of Proposition 2.3
-- statement:
--   For a function $E$ on $\mathbb R^G_{\ge0}$,
--   $$K(E)=\Bigl\{a\in\mathbb R^G_{\ge0}:\ \sum_i a_iu_i\le E(u)\ \text{ for all }u\in\mathbb R^G_{\ge0}\Bigr\}.$$
--
--   By Proposition 2.3 (a) it is a weight set of every sublinear group effect, so it provides a canonical choice of weight sets.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Proposition 2.3 (a), p.14 (PDF p.16)

import Mathlib

open scoped NNReal

namespace FairFacilityLoc

/-- **The set `K(E)`** (Yan, Zhou, manuscript, sha256 642a1268…, Proposition 2.3 (a), p.14, PDF p.16):
`K(E) = {a ∈ ℝ^ι_{≥0} : ∑ i, a i * u i ≤ E u for all u ∈ ℝ^ι_{≥0}}`. -/
def canonicalWeightSet {ι : Type*} [Fintype ι] (E : (ι → ℝ≥0) → ℝ≥0) : Set (ι → ℝ≥0) :=
  {a | ∀ u : ι → ℝ≥0, ∑ i, a i * u i ≤ E u}

end FairFacilityLoc


