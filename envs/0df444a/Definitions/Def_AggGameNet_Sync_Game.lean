-- Prove2me | Definitions.Def_AggGameNet_Sync_Game
-- name    : AggGameNet_Sync_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:33:46.657347+00:00
-- url     : https://prove2.me/theorems/23bb2df7-71fe-4e94-bbc8-578b4f3a2bde
-- title:
--   (1) and (5), pp. 4, 6 — decision space, the Minkowski sum K̄ of the strategy sets, and product-set variational inequalities
-- statement:
--   There are $N$ players indexed by $i\in\{1,\dots,N\}$, each choosing a decision $x_i\in\mathbb R^n$. Given the strategy sets $K_i\subseteq\mathbb R^n$, the set of attainable aggregates is the Minkowski sum of equation (1),
--
--   $$
--   \bar K=\sum_{i=1}^N K_i=\Big\{\sum_{i=1}^N x_i \;:\; x_i\in K_i\text{ for every } i\Big\}.
--   $$
--
--   For a map $T$ sending a decision profile $x=(x_1,\dots,x_N)$ to a profile $T(x)=(T_1(x),\dots,T_N(x))$, a point $x^*$ solves the variational inequality $\mathrm{VI}(K,T)$ on the product set $K=\prod_i K_i$ when $x_i^*\in K_i$ for every $i$ and
--
--   $$
--   \sum_{i=1}^N (x_i-x_i^*)^\top T_i(x^*)\ \ge\ 0\qquad\text{for every } x\in K .
--   $$
--
--   These are the objects of §2 on which every result of the paper is stated; the game's own map $\phi$ of (5) is plugged in as $T$ in the companion definition of the setting.
--
--   **Formalization Note** Decisions live in `EuclideanSpace ℝ (Fin n)`, so $\|\cdot\|$ is the Euclidean norm. A profile is a function `Fin N → E n` (players indexed from $0$). The inner product on $\mathbb R^{nN}$ is written as the sum of the blockwise inner products, because Mathlib's norm on function types is the sup norm.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, (1), p. 4, and VI(K, φ) with (5), p. 6

import Mathlib

namespace AggGameNet.Sync

/-- The common decision space of the players. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The attainable aggregate set, equation (1). -/
def Kbar {N n : ℕ} (K : Fin N → Set (E n)) : Set (E n) :=
  {u | ∃ x : Fin N → E n, (∀ i, x i ∈ K i) ∧ u = ∑ i, x i}

/-- A solution of a product-set variational inequality. -/
def IsVI {N n : ℕ} (K : Fin N → Set (E n))
    (op : (Fin N → E n) → Fin N → E n) (xs : Fin N → E n) : Prop :=
  (∀ i, xs i ∈ K i) ∧
    ∀ x : Fin N → E n, (∀ i, x i ∈ K i) →
      0 ≤ ∑ i, inner ℝ (x i - xs i) (op xs i)

end AggGameNet.Sync


