-- Prove2me | Definitions.Def_MultiplayerNoCollision_phase1Estimate
-- name    : MultiplayerNoCollision_phase1Estimate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:03.609119+00:00
-- url     : https://prove2.me/theorems/10391f98-9297-4086-850b-1a75de8c906d
-- title:
--   The scaled Phase-1 estimate $\hat\mu_{i,t}$
-- statement:
--   Let $h$ be a player's history of $t$ rounds and $i$ an arm. Let $n_i$ be the number of rounds $s<t$ in which arm $i$ was pulled. The **estimate** of $\mu_i$ is
--   $$\hat\mu_{i,t}=\frac{1}{(1-1/K)^{m-1}}\cdot\frac{1}{n_i}\sum_{s<t:\,A(s)=i}r(s)$$
--   if $n_i\ge1$, and $\hat\mu_{i,t}=0$ if arm $i$ was never pulled.
--
--   The average includes the zero rewards caused by collisions. When the other players pull uniformly random arms, $(1-1/K)^{m-1}$ is the probability that a pull is collision-free, so dividing by it makes the average an unbiased estimate of $\mu_i$.
--
--   **Formalization Note** $1-1/K$ is real arithmetic; $m-1$ is natural subtraction and is used with $m\ge2$.
-- source:
--   Lugosi, Mehrabian, Multiplayer bandits without observing collision information, arXiv:1808.08416v2, §3, Phase 1, p.8; Algorithm 1, lines 2 and 6, p.10

import Mathlib
import Definitions.Def_MultiplayerNoCollision_Policy

namespace MultiplayerNoCollision

open Finset

/-- **The scaled mean estimate of Phase 1.** Lugosi, Mehrabian, arXiv:1808.08416v2, §3, p.8: "the
estimate for arm `i` is the average reward received from arm `i` divided by `(1 − 1/K)^{m−1}`", and
Algorithm 1, lines 2 and 6, p.10 (`µ̂_i ← 0` initially).

For a history `h` of `t` rounds, `phase1Estimate m K h i` is the average of the rewards `h s` over the
rounds `s < t` in which arm `i` was pulled, divided by `(1 − 1/K)^{m−1}`, and `0` if arm `i` was
never pulled. This is the paper's `µ̂_{i,t}` when `h` is the player's history of `t` rounds.

**Formalization Note.** The average includes the zero rewards caused by collisions. `1 − 1/K` is
real arithmetic; `m − 1` is natural subtraction, used with `m ≥ 2`. -/
noncomputable def phase1Estimate (m K : ℕ) {t : ℕ} (h : History K t) (i : Fin K) : ℝ :=
  open Classical in
  let pulls := univ.filter fun s : Fin t => (h s).1 = i
  if pulls.card = 0 then 0
  else ((∑ s ∈ pulls, (h s).2) / pulls.card) / (1 - 1 / (K : ℝ)) ^ (m - 1)

end MultiplayerNoCollision


