-- Prove2me | Definitions.Def_GibbsCongestion_baseExchangeWalk
-- name    : GibbsCongestion_baseExchangeWalk
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:00:23.260462+00:00
-- url     : https://prove2.me/theorems/51c26e83-28ce-482a-9142-30c80f2fe8cf
-- title:
--   Base-exchange Markov chain
-- statement:
--   Let $\mathcal B$ be the set of bases of a matroid and $w\ge0$ a weight function on bases. The **base-exchange Markov chain** moves from the current base $B$ by:
--
--   1. selecting $e\in B$ uniformly at random and removing it;
--   2. picking a base $B'\supseteq B-e$ with probability proportional to $w(B')$ among all such bases.
--
--   As a matrix, $K(B,B')=\frac1{|B|}\sum_{e\in B}[\,B-e\subseteq B'\,]\,w(B')\big/\sum_{B''\supseteq B-e}w(B'')$. It is reversible with stationary distribution $\pi(B)\propto w(B)$.
--
--   **Formalization Note** The chain is defined for any finite family of bases; its state space is the set of bases of positive weight (the support of $\pi$), since bases of weight $0$ are never chosen. The new base may equal the old one.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.4, p.11

import Mathlib

namespace GibbsCongestion

/-- The **base-exchange Markov chain** (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.4, p.11) on a family `𝔅` of bases with a
weight function `w ≥ 0`: from the current base `B`, select `e ∈ B` uniformly at random and remove
it, then pick a base `B' ⊇ B − e` with probability proportional to `w(B')` among all such bases.

**Formalization Note** The state space is the set of bases of positive weight,
`{B ∈ 𝔅 : w(B) > 0}` (the support of the distribution `π(B) ∝ w(B)`); bases of weight `0` are
never chosen. The base `B'` may equal `B`. -/
noncomputable def baseExchangeWalk {α : Type*} [Fintype α] [DecidableEq α] (𝔅 : Finset (Finset α))
    (w : Finset α → ℝ) :
    Matrix {B : Finset α // B ∈ 𝔅 ∧ 0 < w B} {B : Finset α // B ∈ 𝔅 ∧ 0 < w B} ℝ :=
  fun B B' => (1 / (B.1.card : ℝ)) * ∑ e ∈ B.1,
    if B.1.erase e ⊆ B'.1 then
      w B'.1 / ∑ B'' ∈ Finset.univ.filter
          (fun B'' : {B : Finset α // B ∈ 𝔅 ∧ 0 < w B} => B.1.erase e ⊆ B''.1), w B''.1
    else 0

end GibbsCongestion


