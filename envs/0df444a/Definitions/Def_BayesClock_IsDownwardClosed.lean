-- Prove2me | Definitions.Def_BayesClock_IsDownwardClosed
-- name    : BayesClock_IsDownwardClosed
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:09.808066+00:00
-- url     : https://prove2.me/theorems/b3c4dd0d-844e-4b40-91f7-d8c7a7c1e9a7
-- title:
--   Downward-closed feasibility constraint
-- statement:
--   Let $N$ be a finite set of buyers. A **feasibility constraint** $\mathcal F\subseteq 2^N$ lists the subsets of buyers that can be served simultaneously. It is **downward-closed** if
--
--   $$F\in\mathcal F,\ F'\subseteq F\ \Longrightarrow\ F'\in\mathcal F,$$
--
--   and $\mathcal F$ is nonempty, equivalently $\emptyset\in\mathcal F$.
--
--   This is the class of constraints on which the paper's auctions run.
--
--   **Formalization Note** The clause $\emptyset\in\mathcal F$ excludes only the empty family, which admits no auction at all.
-- source:
--   Feldman, Gkatzelis, Gravin & Schoepflin, Bayesian and Randomized Clock Auctions, arXiv:2202.09291v1, §2, p.5

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace BayesClock

/-- `𝓕 ⊆ 2^N` is a downward-closed feasibility constraint: if `F ∈ 𝓕` then `F' ∈ 𝓕` for every
`F' ⊆ F`. Feldman et al., *Bayesian and Randomized Clock Auctions*, arXiv:2202.09291v1, §2, p.5.

**Formalization Note** `𝓕` is a `Finset (Finset N)` over a finite bidder type `N`. The clause
`∅ ∈ 𝓕` excludes only the empty family, which admits no auction at all: every nonempty
downward-closed family contains `∅`. -/
def IsDownwardClosed {N : Type*} [DecidableEq N] (𝓕 : Finset (Finset N)) : Prop :=
  ∅ ∈ 𝓕 ∧ ∀ F ∈ 𝓕, ∀ F' : Finset N, F' ⊆ F → F' ∈ 𝓕

end BayesClock


