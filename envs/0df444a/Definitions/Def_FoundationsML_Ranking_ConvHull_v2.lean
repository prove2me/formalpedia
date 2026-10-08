-- Prove2me | Definitions.Def_FoundationsML_Ranking_ConvHull_v2
-- name    : FoundationsML_Ranking_ConvHull_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:16:18.419811+00:00
-- url     : https://prove2.me/theorems/bddde8ba-cefc-4f25-bbb8-8c308a8892b4
-- title:
--   Convex hull $\mathrm{conv}(H)$ of Eq. (7.12), as used by Corollary 10.4 — corrected
-- statement:
--   **Convex hull (Eq. (7.12), p. 157, PDF p. 174; used at p. 250, PDF p. 267).** For a set $H$ of real-valued functions, $\mathrm{conv}(H) = \{\sum_{k=1}^p \mu_k h_k : p\ge1,\ \mu_k\ge0,\ h_k\in H,\ \sum_{k=1}^p\mu_k\le1\}$.
--
--   **Formalization Note.** Corrected re-issue of the retired `Ranking` module `ConvHull`, which required $\sum\mu_k = 1$. Corollary 10.4 is Theorem 10.1 applied to $\mathrm{conv}(H)$ "by lemma 7.4", whose $\mathrm{conv}(H)$ is the set (7.12) with $\sum\mu_k\le1$ (sub-convex combinations); the retired set was strictly smaller, so the corollary stated over it said less than the book. This module matches (7.12) exactly, as the Boosting chapter's `ConvHull` already did.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Eq. (7.12), p. 157 (PDF p. 174)

import Mathlib

namespace FoundationsML.Ranking

/-- The convex hull `conv(H)` of a set `H` of real-valued functions `X → ℝ` as used by Lemma 7.4
and Corollary 10.4 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, Eq. (7.12), p. 157, PDF p. 174, invoked at p. 250, PDF p. 267):
`conv(H) = {∑_{k=1}^p μ_k h_k : p ≥ 1, μ_k ≥ 0, h_k ∈ H, ∑_{k=1}^p μ_k ≤ 1}`.

**Formalization Note.** Corollary 10.4 is Theorem 10.1 applied to `conv(H)` "by lemma 7.4",
whose `conv(H)` is the set (7.12) with `∑ μ_k ≤ 1` (sub-convex combinations, i.e.
`conv(H ∪ {0})`). The retired module `Def_FoundationsML_Ranking_ConvHull` required
`∑ μ_k = 1`, a strictly smaller set, so the corollary stated over it was a weaker statement
than the book's; this re-issue matches (7.12) exactly, as the Boosting chapter's own
`ConvHull` already did. -/
def ConvHull {X : Type*} (H : Set (X → ℝ)) : Set (X → ℝ) :=
  {f | ∃ (p : ℕ) (μ : Fin p → ℝ) (hs : Fin p → (X → ℝ)),
    1 ≤ p ∧ (∀ k, 0 ≤ μ k) ∧ (∀ k, hs k ∈ H) ∧ (∑ k, μ k) ≤ 1 ∧
    f = fun x => ∑ k, μ k * hs k x}

end FoundationsML.Ranking


