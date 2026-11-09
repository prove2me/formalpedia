-- Prove2me | Definitions.Def_CBCLowerBound_EveryNorm_Transport
-- name    : CBCLowerBound_EveryNorm_Transport
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:59.778205+00:00
-- url     : https://prove2.me/theorems/4b4a9c78-a94f-4fb7-9ba7-2fbcf5d72d93
-- title:
--   Probability vectors and the Wasserstein-1 distance on a finite set
-- statement:
--   Let $V$ be a finite set and $d:V\times V\to\mathbb R$ a cost (later the shortest-path metric $d_G$ of a graph).
--
--   1. A **probability vector** on $V$ is a function $P:V\to\mathbb R$ with $P(v)\ge0$ for all $v$ and $\sum_v P(v)=1$.
--   2. For $P,Q:V\to\mathbb R$, a **coupling** is a function $\pi:V\times V\to\mathbb R_{\ge0}$ with $\sum_v\pi(u,v)=P(u)$ and $\sum_u\pi(u,v)=Q(v)$. The **Wasserstein-1 distance** is the minimum transportation cost
--   $$W_1(P,Q)=\min_\pi \sum_{u,v}\pi(u,v)\,d(u,v).$$
--
--   This is the cost a randomized algorithm pays between consecutive distributions on the discrete requests (p.4), and the left side of Lemma 8.
--
--   **Formalization Note** $W_1$ is written as a real infimum over couplings. For probability vectors the set of couplings is nonempty (it contains the product coupling) and compact, and for a nonnegative cost the infimum is attained, so it is the paper's minimum.
-- source:
--   Nicolas Christianson, A Linear Lower Bound for Convex Body Chasing in Every Norm, STOC 2027 submission #674 (October 2026), p.12, §3.2 (couplings and W_1), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/674.pdf

import Mathlib

namespace CBCLowerBound.EveryNorm

/-! # Probability vectors and the Wasserstein-1 distance on a finite set
(Christianson, STOC 2027 #674, §3.2, p.12) -/

variable {V : Type} [Fintype V]

/-- `P : V → ℝ` is a **probability vector** (a probability distribution on the finite set `V`):
nonnegative masses summing to one. -/
def IsProbVec (P : V → ℝ) : Prop :=
  (∀ v, 0 ≤ P v) ∧ ∑ v, P v = 1

/-- The **Wasserstein-1 distance** (optimal transportation cost) between mass vectors `P`, `Q`
on a finite set with cost `d` (p.12): the infimum, over all couplings `π ≥ 0` with
`∑_v π(u,v) = P(u)` and `∑_u π(u,v) = Q(v)`, of `∑_{u,v} π(u,v) d(u,v)`. For two probability
vectors the set of couplings is nonempty (the product coupling) and compact, so for a
nonnegative cost this is the minimum of the paper. -/
noncomputable def W1 (d : V → V → ℝ) (P Q : V → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ π : V → V → ℝ, (∀ u v, 0 ≤ π u v) ∧ (∀ u, ∑ v, π u v = P u) ∧
    (∀ v, ∑ u, π u v = Q v) ∧ c = ∑ u, ∑ v, π u v * d u v}

end CBCLowerBound.EveryNorm


