-- Prove2me | Definitions.Def_CommissionsSubscriptions_Market
-- name    : CommissionsSubscriptions_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:21:37.750127+00:00
-- url     : https://prove2.me/theorems/287f3e91-51f6-4b33-972b-f3fbce22be37
-- title:
--   Market data of a networked two-sided market
-- statement:
--   A **networked market** consists of finitely many seller types $S$ and buyer types $B$, and:
--
--   1. a **compatibility network**: an edge set $E\subseteq S\times B$; the edge $(i,j)$ means that type-$j$ buyers can trade with type-$i$ sellers;
--   2. masses $s_i$ of type-$i$ sellers and $b_j$ of type-$j$ buyers;
--   3. disutilities $c_i$: a buyer with idiosyncratic value $v_b$ who trades with a type-$i$ seller has value $v_b-c_i$;
--   4. value distributions $F_{s_i}$ (sellers' reservation values) and $F_{b_j}$ (buyers' values), cumulative distribution functions extended to all of $\mathbb R$ by $F(v)=0$ for $v\le0$ and $F(v)=1$ for $v\ge\bar v$.
--
--   This is the data of the model of §2 of the paper; every object of the mission is built from it.
--
--   **Formalization Note** The structure carries the data only. The standing conditions ($s_i,b_j>0$, $c_i\ge0$, degree at least one, Assumption 1) form the predicate `MarketHyp`. Arbitrary finite types replace $\{1,\dots,n\}$ and $\{1,\dots,m\}$.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), §2, pp. 7–8

import Mathlib

namespace CommissionsSubscriptions

/-- **Market data of a networked two-sided market.**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), §2, pp. 7–8.

* `S` (seller types) and `B` (buyer types) are finite types; the paper's `S = {1,…,n}`,
  `B = {1,…,m}`.
* `E : Finset (S × B)` is the edge set of the compatibility network `G(B ∪ S, E)`; the pair
  `(i, j)` is the edge between seller type `i` and buyer type `j`.
* `s i > 0` and `b j > 0` are the masses of type-`i` sellers and type-`j` buyers.
* `c i ≥ 0` is the disutility a buyer incurs from transacting with a type-`i` seller.
* `Fs i`, `Fb j` are the value distributions (CDFs) of type-`i` sellers and type-`j` buyers,
  already extended to `ℝ` as on p. 8 (`F(v) = 0` for `v ≤ 0`, `F(v) = 1` for `v ≥ v̄`).

**Formalization Note.** The structure carries the data only. The paper's standing conditions
(positive masses, `c ≥ 0`, every type has degree at least one, Assumption 1) are the predicate
`MarketHyp`. Arbitrary finite types generalize `{1,…,n}` and `{1,…,m}`. -/
structure Market (S B : Type) where
  /-- Edge set of the compatibility network; `(i, j)` joins seller type `i` and buyer type `j`. -/
  E : Finset (S × B)
  /-- Mass `s_i` of type-`i` sellers. -/
  s : S → ℝ
  /-- Mass `b_j` of type-`j` buyers. -/
  b : B → ℝ
  /-- Disutility `c_i` of transacting with a type-`i` seller. -/
  c : S → ℝ
  /-- Value distribution `F_{s_i}` of type-`i` sellers, extended to `ℝ`. -/
  Fs : S → ℝ → ℝ
  /-- Value distribution `F_{b_j}` of type-`j` buyers, extended to `ℝ`. -/
  Fb : B → ℝ → ℝ

end CommissionsSubscriptions


