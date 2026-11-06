-- Prove2me | Definitions.Def_AuctionMatroidInt_utility
-- name    : AuctionMatroidInt_utility
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:26:14.052592+00:00
-- url     : https://prove2.me/theorems/0baefe63-1b94-4487-b842-3421b83afb36
-- title:
--   Implicit prices $\bar p$, $p$ and utilities $q$ induced by $(X,\pi)$, displays (1)–(3)
-- statement:
--   Let $M_2=(E,\mathcal I_2)$ be a matroid, $X\subseteq E$, $\pi(e)$ a price for each $e\in X$ (with $\pi(e)=\bot$ for $e\notin X$), $w\in\mathbb R^E$ and $\varepsilon>0$. Define, for $e\in E$,
--
--   $$
--   \bar p(e)=\begin{cases}\pi(e)&e\in X,\\ 0&e\notin X,\ X+e\in\mathcal I_2,\\ \min\{\pi(f): f\in C_2(X\mid e)-e\}&e\notin X,\ X+e\notin\mathcal I_2,\end{cases}
--   $$
--
--   the price vector $p(e)=\pi(e)$ for $e\in X$ and $p(e)=\bar p(e)+\varepsilon w(e)$ for $e\notin X$, and the utility vector
--
--   $$
--   q(e)=\lceil w(e)-p(e)\rceil_{1+\varepsilon}\in\Lambda .
--   $$
--
--   In the auction interpretation $\bar p(e)$ is the cheapest price of an item Bob must give up to sell $e$, and $p(e)$ adds a profit $\varepsilon w(e)$; $q(e)$ is Alice's rounded utility for buying $e$. The algorithm maintains only $X$ and $\pi$ and computes these values on demand.
--
--   **Formalization Note** `pbar`, `price` and `utility` read `π` only on `X`; $C_2(X\mid e)-e$ is `fundCircuitErase I₂ X e` (Observation 2.1). The minimum is over a set that is nonempty when $M_2$ is loopless (as the paper notes); when it is empty the definition returns $0$, which no statement uses.
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), §5.1.1, displays (1), (2), (3), p.20 (PDF p.22)

import Mathlib
import Definitions.Def_AuctionMatroidInt_fundCircuitErase
import Definitions.Def_AuctionMatroidInt_roundUp

namespace AuctionMatroidInt

open Classical in
/-- **The vector `p̄` induced by `X` and `π`, display (1).**
Huang, Kobayashi, Terao (manuscript, sha256 2e12cb4a…), §5.1.1, (1), p.20:
`p̄(e) = π(e)` if `e ∈ X`; `0` if `e ∈ E \ X` and `X + e ∈ I₂`;
`min{π(f) | f ∈ C₂(X | e) − e}` if `e ∈ E \ X` and `X + e ∉ I₂`.

**Formalization Note.** `π : α → ℝ` is read **only on `X`** (the paper writes `π(e) = ⊥` for
`e ∉ X`): `C₂(X | e) − e` is `fundCircuitErase I₂ X e ⊆ X` (Observation 2.1). The minimum is
`Finset.inf'`; the paper notes the set is nonempty "because we have assumed that M₂ has no
loops", and the `if` only guards the definition when it is empty (a loop of `M₂`), where the
value `0` is never used by a statement (they all assume `M₂` loopless). -/
noncomputable def pbar {α : Type*} [DecidableEq α] (I₂ : Finset α → Prop) (X : Finset α)
    (π : α → ℝ) (e : α) : ℝ :=
  if e ∈ X then π e
  else if I₂ (insert e X) then 0
  else if h : (fundCircuitErase I₂ X e).Nonempty then (fundCircuitErase I₂ X e).inf' h π
  else 0

open Classical in
/-- **The price vector `p` induced by `X` and `π`, display (2)** (§5.1.1, p.20):
`p(e) = π(e)` for `e ∈ X` and `p(e) = p̄(e) + εw(e)` for `e ∈ E \ X`. -/
noncomputable def price {α : Type*} [DecidableEq α] (ε : ℝ) (w : α → ℝ) (I₂ : Finset α → Prop)
    (X : Finset α) (π : α → ℝ) (e : α) : ℝ :=
  if e ∈ X then π e else pbar I₂ X π e + ε * w e

/-- **The utility vector `q` induced by `X` and `π`, display (3)** (§5.1.1, p.20):
`q(e) := ⌈w(e) − p(e)⌉_{1+ε}` for `e ∈ E`. -/
noncomputable def utility {α : Type*} [DecidableEq α] (ε : ℝ) (w : α → ℝ) (I₂ : Finset α → Prop)
    (X : Finset α) (π : α → ℝ) (e : α) : ℝ :=
  roundUp ε (w e - price ε w I₂ X π e)

end AuctionMatroidInt


