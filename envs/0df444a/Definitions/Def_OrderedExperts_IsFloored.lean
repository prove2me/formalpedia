-- Prove2me | Definitions.Def_OrderedExperts_IsFloored
-- name    : OrderedExperts_IsFloored
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:40.427276+00:00
-- url     : https://prove2.me/theorems/132f9e06-3444-45ef-a944-36d90fefc7a9
-- title:
--   Floored intended distribution on $m$ active ranks
-- statement:
--   Let $m$ be the number of active actions of a round, ranked $1,\dots,m$, and let $\pi$ be a vector on these ranks. The pair $(\xi,\pi)$ satisfies the **floor** if
--   1. $0<\xi\le 1$;
--   2. $\pi(j)\ge \xi/m$ for every rank $j=1,\dots,m$;
--   3. $\sum_{j=1}^m\pi(j)=1$, i.e. $\pi$ is a probability distribution on the ranks.
--
--   These are the standing assumptions of Section 3 of the paper: $\pi$ is the distribution with which the learner intends to play, mixed with $\xi$ times the uniform distribution so that every active action has probability at least $\xi/m$. They force $m\ge1$ and $\pi(j)>0$ on every active rank.
--
--   **Formalization Note** $\pi:\mathbb N\to\mathbb R$ is read only on the ranks $1,\dots,m$; values elsewhere are unconstrained and are never read by the mission's statements.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Sec. 3, p.6, and Sec. 3.1, p.6

import Mathlib

namespace OrderedExperts

/-- **Floored intended distribution.** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Sec. 3, p.6, and Sec. 3.1, p.6: "π is the
distribution over ranks {1, . . . , m} with which the learner intends to play." "We assume a floor on
the intended distribution, `π(j) ≥ ξ/m`, `j = 1, . . . , m`, where `0 < ξ ≤ 1`".

`IsFloored m ξ π` says that `0 < ξ ≤ 1`, that `π(j) ≥ ξ/m` for every active rank `j ∈ {1, …, m}`,
and that `π` is a probability vector on `{1, …, m}`. These are the standing assumptions of
Section 3; they force `m ≥ 1` and `π(j) > 0` on every active rank.

**Formalization Note.** `π : ℕ → ℝ` is read only on the ranks `1, …, m`; its values elsewhere are
unconstrained and are never read by the statements of the mission. -/
def IsFloored (m : ℕ) (ξ : ℝ) (π : ℕ → ℝ) : Prop :=
  0 < ξ ∧ ξ ≤ 1 ∧ (∀ j ∈ Finset.Icc 1 m, ξ / m ≤ π j) ∧ ∑ j ∈ Finset.Icc 1 m, π j = 1

end OrderedExperts


