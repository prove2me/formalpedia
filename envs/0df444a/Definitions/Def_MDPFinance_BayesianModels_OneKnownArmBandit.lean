-- Prove2me | Definitions.Def_MDPFinance_BayesianModels_OneKnownArmBandit
-- name    : MDPFinance_BayesianModels_OneKnownArmBandit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:18:41.217748+00:00
-- url     : https://prove2.me/theorems/a340885b-2d57-422d-9923-4d1c60d7af96
-- title:
--   The one-known-arm bandit's value function (Section 5.5)
-- statement:
--   This definition packages the concrete finite-state Markov Decision Model of the
--   one-known-arm specialization (p. 169-170) of the two-armed bandit, the setting for Theorem
--   5.5.2: arm 1's success probability $p_1 \in (0,1)$ is known, so the information state reduces to
--   $(m,n) \in \mathbb N_0^2$, the successes/failures observed at arm 2 alone.
--
--   With $p(m,n) := (m+1)/(m+n+2)$ the posterior mean success probability at arm 2 and
--   $(Pv)(m,n) := p(m,n)v(m+1,n) + (1-p(m,n))v(m,n+1)$, the Bellman equation reduces to
--   $$
--   J_k(m,n) = \max\big[p_1 + \beta J_{k-1}(m,n),\; p(m,n) + \beta (PJ_{k-1})(m,n)\big],
--   \qquad J_0 \equiv 0.
--   $$
--   `dK` is the arm-2-minus-arm-1 advantage of the one-step problem,
--   $d_k(m,n) := [p(m,n)+\beta(PJ_{k-1})(m,n)] - [p_1+\beta J_{k-1}(m,n)]$, used in the book's own
--   proof of Theorem 5.5.2a to characterize the optimal action; `VpiK` is the value of a general
--   Markov policy through this recursion, used to state Theorem 5.5.2's optimality claim.
--
--   **Formalization Note.** Arms are coded `0`/`1` for arm 1 (known)/arm 2 (unknown) throughout, to
--   avoid the book's `1`/`2` colliding with `Fin 2`'s `0`-based indexing.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 169, p. 169 (unnumbered, underlies Theorem 5.5.2)

import Mathlib

namespace MDPFinance.BayesianModels

/-- The one-known-arm bandit's information state (Bäuerle–Rieder, p. 169-170, PDF 182-183):
`(m,n)` records the number `m` of successes and `n` of failures observed so far at arm 2 (the
arm with unknown success probability; arm 1's success probability `p_1` is known). -/
abbrev KnownArmState := ℕ × ℕ

/-- `p(m,n) := (m+1)/(m+n+2)`, the posterior mean success probability at arm 2
(Bäuerle–Rieder, p. 169, PDF 182). -/
noncomputable def pK (mn : KnownArmState) : ℝ := (mn.1 + 1) / (mn.1 + mn.2 + 2)

/-- `(Pv)(m,n) := p(m,n) v(m+1,n) + (1-p(m,n)) v(m,n+1)` for bounded `v : ℕ_0^2 → ℝ`
(Bäuerle–Rieder, p. 169, PDF 182). -/
noncomputable def PK (v : KnownArmState → ℝ) (mn : KnownArmState) : ℝ :=
  pK mn * v (mn.1 + 1, mn.2) + (1 - pK mn) * v (mn.1, mn.2 + 1)

/-- `J_k(m,n) := max[p_1 + β J_{k-1}(m,n), p(m,n) + β (P J_{k-1})(m,n)]`, `J_0 ≡ 0`
(Bäuerle–Rieder, p. 169, PDF 182), the value function of the one-known-arm bandit (known success
probability `p_1 ∈ (0,1)`) with `k` stages remaining. -/
noncomputable def JK (p1 β : ℝ) : ℕ → KnownArmState → ℝ
  | 0, _ => 0
  | (k + 1), mn => max (p1 + β * JK p1 β k mn) (pK mn + β * PK (JK p1 β k) mn)

/-- `d_k(m,n) := [p(m,n) + β (P J_{k-1})(m,n)] - [p_1 + β J_{k-1}(m,n)]`, the arm-2-minus-arm-1
advantage of the one-step problem at `k` stages remaining (Bäuerle–Rieder, proof of Theorem
5.5.2a, p. 184, PDF 184-185: `d_k(m,n) := LJ_{k-1}((m,n),2) - LJ_{k-1}((m,n),1)`). -/
noncomputable def dK (p1 β : ℝ) : ℕ → KnownArmState → ℝ
  | 0, _ => 0
  | (k + 1), mn => pK mn + β * PK (JK p1 β k) mn - (p1 + β * JK p1 β k mn)

/-- The expected total reward `V_k^f(m,n)` of a (Markov) policy `f : ℕ → KnownArmState → Fin 2`
(`f k` the decision rule used when `k` stages remain; `0` = arm 1 (known), `1` = arm 2 (unknown))
over `k` further stages from `(m,n)`, in the one-known-arm bandit, `β`-discounted. -/
noncomputable def VpiK (p1 β : ℝ) (f : ℕ → KnownArmState → Fin 2) : ℕ → KnownArmState → ℝ
  | 0, _ => 0
  | (k + 1), mn =>
      if f (k + 1) mn = 0 then p1 + β * VpiK p1 β f k mn
      else pK mn + β * PK (VpiK p1 β f k) mn

end MDPFinance.BayesianModels


