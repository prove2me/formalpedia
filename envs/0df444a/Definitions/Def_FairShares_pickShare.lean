-- Prove2me | Definitions.Def_FairShares_pickShare
-- name    : FairShares_pickShare
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:13:02.048435+00:00
-- url     : https://prove2.me/theorems/d94311cf-b2a2-424d-9d56-211d0515ecde
-- title:
--   The $\omega$-Picking-Order share
-- statement:
--   Fix a picking order $\omega$ for $m$ goods and $n\ge1$ agents. The **$\omega$-Picking-Order share** of an agent with valuation $v$ is
--   $$
--   \min_{k\in[n]} x_k ,
--   $$
--   the minimum over all identities the agent could have of what she can ensure with that identity.
--
--   **Formalization Note** The minimum is `⨅ k : Fin n`, the true minimum for $n\ge1$ (every statement about it assumes $n\ge1$).
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, §4.1, p.15

import Mathlib
import Definitions.Def_FairShares_pickValue

namespace FairShares

/-- **The ω-Picking-Order share.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, §4.1, p.15: "Fix a picking order ω. The ω-Picking-Order share of an agent with valuation v
is min_{k∈[n]} xk. That is, the minimum over all possible identities of the agent, of the maximum
she can ensures herself with that identity when the picking order is ω."

`pickShare ω v = min_{k} pickValue ω v k`.

**Formalization Note.** The minimum over the finite index type `Fin n` is written `⨅ k : Fin n`;
it is the true minimum for `n ≥ 1`, which every statement about it assumes (at `n = 0` it is
`0`). As a function of `v` at fixed `m, n`, `pickShare ω` plays the role of `s(·, n)`. -/
noncomputable def pickShare {m n : ℕ} (ω : Fin m → Fin n) (v : Finset (Fin m) → ℝ) : ℝ :=
  ⨅ k : Fin n, pickValue ω v k

end FairShares


