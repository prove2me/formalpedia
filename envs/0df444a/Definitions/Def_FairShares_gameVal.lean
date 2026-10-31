-- Prove2me | Definitions.Def_FairShares_gameVal
-- name    : FairShares_gameVal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:37.258388+00:00
-- url     : https://prove2.me/theorems/0e92a845-6e59-4f98-9ec7-b2acb7c1644e
-- title:
--   Value of the picking game against an adversary
-- statement:
--   Fix a valuation $v$ on the bundles of $M=\{0,\dots,m-1\}$ and an agent identity $k$. Agent $k$ plays a picking game against an adversary: the remaining picks are made in a given order (a list of agents); at a pick by $k$ she takes one remaining item, at any other pick the adversary removes one remaining item. The outcome is $v$ of the bundle $k$ ends with; $k$ maximizes it and the adversary minimizes it.
--
--   $\mathrm{gameVal}(v,k,\text{order},R,H)$ is the value of this game, by backward induction, when the remaining items are $R$ and $k$ already holds $H$:
--   $$
--   \mathrm{gameVal}(p::ps,R,H)=\begin{cases}\max_{e\in R}\mathrm{gameVal}(ps,R\setminus\{e\},H\cup\{e\}) & p=k,\\ \min_{e\in R}\mathrm{gameVal}(ps,R\setminus\{e\},H) & p\ne k,\end{cases}
--   $$
--   and it equals $v(H)$ when the order or the remaining items are exhausted.
--
--   **Formalization Note** This is the max-min value of the finite perfect-information game of §4.1; no property of $v$ is assumed.
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, §4.1, p.15

import Mathlib

namespace FairShares

/-- **Value of the picking game for agent `k` against an adversary.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, §4.1, p.15: "Let xk be the maximum value that agent k ∈ [n] with valuation v can ensure she
gets when the picking order is ω. That is, the maximum value when facing an adversary that makes
all picks when ωj ≠ k in order to minimize the value that agent k gets."

`gameVal v k ps R H` is the backward-induction value, measured by `v`, of the final holdings of
agent `k` when the remaining items are `R`, `k` already holds `H`, and the remaining picks are made
in the order `ps` (a list of agents): at a pick by `k` she takes the item maximizing her
continuation value, at a pick by any other agent the adversary removes the item minimizing it.
When the list or the remaining items run out, the value is `v H`.

**Formalization Note.** This is the max-min value of the finite zero-sum game of perfect
information the paper describes (the maximum over strategies of `k` of the minimum over
adversary strategies, by backward induction). No property of `v` (additivity, monotonicity) is
assumed. -/
noncomputable def gameVal {m n : ℕ} (v : Finset (Fin m) → ℝ) (k : Fin n) :
    List (Fin n) → Finset (Fin m) → Finset (Fin m) → ℝ
  | [], _, H => v H
  | p :: ps, R, H =>
    if hR : R.Nonempty then
      if p = k then R.sup' hR (fun e => gameVal v k ps (R.erase e) (insert e H))
      else R.inf' hR (fun e => gameVal v k ps (R.erase e) H)
    else v H

end FairShares


