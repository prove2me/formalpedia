-- Prove2me | Definitions.Def_PlanarMetricElections_Peer_Supplement_WeakNet
-- name    : PlanarMetricElections_Peer_Supplement_WeakNet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:42:49.917088+00:00
-- url     : https://prove2.me/theorems/6f423c43-ddb8-4697-8cfc-b155ccaada1b
-- title:
--   Weak convex net factor $\varepsilon_k$ on $\mathbb R^r$ (equation (1))
-- statement:
--   Let $P\subseteq\mathbb R^r$ be nonempty and finite and $Q\subseteq\mathbb R^r$ finite. The **uncovered mass** of $Q$ is the largest fraction of $P$ contained in a convex set that avoids $Q$:
--
--   $$U_P(Q)=\sup\{\mu_P(K): K\subseteq\mathbb R^r\ \text{convex},\ K\cap Q=\emptyset\}.$$
--
--   The weak convex net factor of equation (1), for the family of all convex sets, is
--
--   $$\varepsilon_k=\sup_{\substack{P\subseteq\mathbb R^r\\ P\ \text{finite, nonempty}}}\ \inf_{\substack{Q\subseteq\mathbb R^r\\ |Q|\le k}} U_P(Q).$$
--
--   The points of $Q$ may be placed anywhere in $\mathbb R^r$, and $Q=\emptyset$ is allowed. Equivalently, $\varepsilon_k$ is the least $\varepsilon$ such that every $P$ has a weak $\varepsilon$-net of size $k$: a set $Q$ with $|Q|\le k$ meeting every convex set containing **more than** an $\varepsilon$ fraction of $P$.
--
--   **Formalization Note** All convex sets are allowed, including the empty, open, unbounded and lower-dimensional ones; the empty set makes every supremum range nonempty, and all values lie in $[0,1]$, so the real `sSup`/`sInf` are the true extrema. The published definition `WeakEpsNets_LowerBound_Nets` uses the threshold "at least", so it is not reused.
-- source:
--   Gabriel Morete de Azevedo, Ulysse Hennebelle, STOC 2027 submission #1404 (October 2026), Section 2 (Weak and strong ε-nets), equation (1), p. 4 (PDF p. 5)

import Definitions.Def_PlanarMetricElections_Peer_Supplement_EuclideanMass

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace PlanarMetricElections.Peer.Supplement

/-- Largest mass of `P` in a convex set of `ℝ^r` avoiding `Q`. All convex sets are allowed
(the empty set too, so the set below is nonempty); values lie in `[0, 1]`. -/
def uncoveredMass {r : ℕ} (P Q : Finset (Euc r)) : ℝ :=
  sSup {m : ℝ | ∃ K : Set (Euc r), Convex ℝ K ∧ Disjoint K (↑Q : Set (Euc r)) ∧
    m = euclidMass P K}

/-- Best weak net of at most `k` arbitrary points of `ℝ^r` for `P`; the empty net is permitted,
as in equation (1). -/
def weakNetInstance {r : ℕ} (P : Finset (Euc r)) (k : ℕ) : ℝ :=
  sInf {u : ℝ | ∃ Q : Finset (Euc r), Q.card ≤ k ∧ u = uncoveredMass P Q}

/-- The weak convex net factor `ε_k` on `ℝ^r` of equation (1): supremum over nonempty finite
`P ⊆ ℝ^r`. -/
def weakNetFactor (r k : ℕ) : ℝ :=
  sSup {e : ℝ | ∃ P : Finset (Euc r), P.Nonempty ∧ e = weakNetInstance P k}

end PlanarMetricElections.Peer.Supplement


