-- Prove2me | Definitions.Def_FairProxy_ClosedFormDD_Coupling
-- name    : FairProxy_ClosedFormDD_Coupling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:40.511673+00:00
-- url     : https://prove2.me/theorems/5f0bb3a7-fccb-4870-beb8-475d6e4a7f18
-- title:
--   Definition 1, p. 10 — coupling set of two finite probability vectors
-- statement:
--   Let $\mathcal S$ and $\mathcal T$ be finite sets, and let $\sigma$ and $\tau$ be probability vectors on them. Their coupling set $\Pi(\sigma,\tau)$ consists of arrays $\pi(s,t)$ with the prescribed row and column sums and entries between zero and one:
--
--   $$
--   \Pi(\sigma,\tau)=\{\pi:\sum_t\pi(s,t)=\sigma(s),\;\sum_s\pi(s,t)=\tau(t),\;0\le\pi(s,t)\le1\}.
--   $$
--
--   This is Definition 1 and equation (1) of the paper. It can also serve as a finite coupling interface beyond the fairness model.
--
--   **Formalization Note** The definition accepts functions on arbitrary finite index types; the probability-vector conditions are assumptions when its theorems are used.
-- source:
--   Kallus, Mao & Zhou, Assessing Algorithmic Fairness with Unobserved Protected Class Using Data Combination, arXiv:1906.00285v2, p. 10, Definition 1, Eq. (1)

import Mathlib

namespace FairProxy.ClosedFormDD

/-- Definition 1, equation (1), p. 10: the couplings of two discrete probability vectors. -/
def couplingSet {S T : Type*} [Fintype S] [Fintype T]
    (σ : S → ℝ) (τ : T → ℝ) : Set (S → T → ℝ) :=
  {π | (∀ s, ∑ t, π s t = σ s) ∧
       (∀ t, ∑ s, π s t = τ t) ∧
       ∀ s t, 0 ≤ π s t ∧ π s t ≤ 1}

end FairProxy.ClosedFormDD


