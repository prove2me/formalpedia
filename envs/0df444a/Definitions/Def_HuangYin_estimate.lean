-- Prove2me | Definitions.Def_HuangYin_estimate
-- name    : HuangYin_estimate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:34:45.046073+00:00
-- url     : https://prove2.me/theorems/c11ce686-d99a-4a89-be9a-c0ab6776d1ca
-- title:
--   A customer's estimate from one anecdote, with no prior belief
-- statement:
--   A customer in period $t$ collects $K$ anecdotes, each revealing whether a past buyer obtained product $H$, and estimates the probability of receiving $H$ as the average of a prior belief $\xi_0$ and the anecdotes,
--
--   $$\tilde\xi_{ti}=\frac{\xi_0+\sum_{k=1}^K \mathbf 1^{(t)}_{i,k}}{K+1}.$$
--
--   For one anecdote ($K=1$) and no prior belief ($\xi_0=0$, the paper's assumption from p. 9 on), the estimate is $1/2$ if the anecdote reveals $H$ and $0$ if it reveals $L$.
--
--   **Formalization Note** The Lean function takes a Boolean saying whether the anecdote is $H$ and keeps the paper's formula with $K=1$, $\xi_0=0$ substituted.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), §3.1, p. 8 (the estimate), and p. 9 (ξ0 = 0)

import Mathlib

namespace HuangYin

/-- **A customer's estimated probability of product H, for one anecdote and no prior belief**
(§3.1, p. 8, and p. 9; unnumbered).
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), §3.1, p. 8: "ξ̃ti = (ξ0 + Σ_{k=1}^{K} 1(t)_{i,k}) / (K + 1)", and p. 9: "We thus assume
that ξ0 = 0 hereafter".

`estimate b` is this average for `K = 1` and `ξ0 = 0`, where `b` says whether the single
anecdote reveals product `H` (`1(t)_{i,1} = 1`). It equals `1/2` if `b` and `0` otherwise.

**Formalization Note.** `K = 1` (the case of §4 and Proposition 1) and `ξ0 = 0` (the paper's
standing assumption from p. 9 on) are built in; the formula is kept in the paper's form
`(ξ0 + Σ)/(K + 1)` with these values substituted. -/
noncomputable def estimate (b : Bool) : ℝ := (0 + (if b then 1 else 0)) / (1 + 1)

end HuangYin


