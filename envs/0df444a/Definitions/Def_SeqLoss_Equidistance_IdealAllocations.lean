-- Prove2me | Definitions.Def_SeqLoss_Equidistance_IdealAllocations
-- name    : SeqLoss_Equidistance_IdealAllocations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:33.545618+00:00
-- url     : https://prove2.me/theorems/424088f3-39fa-4290-b8c6-8e228dde989b
-- title:
--   pp. 13–14 — ideal allocations $c_k$, ordered allocations $\bar X(\ell)$, Euclidean distance, equidistance from $c_1,\dots,c_n$
-- statement:
--   Fix a loss problem $\ell\in L^n$ with total loss $L$.
--
--   For $k\in\{1,\dots,n\}$ the **ideal allocation** $c_k$ (§4.1) charges the first $k$ agents equally and the others nothing:
--   $$c_k=\Big(\underbrace{\tfrac Lk,\dots,\tfrac Lk}_{k},0,\dots,0\Big).$$
--   Thus $c_1=(L,0,\dots,0)$ and $c_n=(L/n,\dots,L/n)$.
--
--   The set of **ordered allocations** is $\bar X(\ell)=\{x\in X(\ell)\mid x_1\ge\dots\ge x_n\}$.
--
--   Distances are **Euclidean**: $d(x,y)=\big(\sum_{i=1}^n(x_i-y_i)^2\big)^{1/2}$.
--
--   A vector $x\in\mathbb R^n$ is **equidistant from the ideal allocations** when $d(x,c_k)=d(x,c_{k'})$ for all $k,k'\in\{1,\dots,n\}$.
--
--   These are the objects in which Theorem 2 of the paper is stated.
--
--   **Formalization Note** $c_k$ is defined for every natural number $k$ (its first $k$ coordinates, 0-based indices $i<k$, equal $L/k$); only $1\le k\le n$ is meaningful, and every statement of the mission quantifies over that range only ($c_0$ would be the zero vector in Lean). The Euclidean distance is Mathlib's distance on `EuclideanSpace ℝ (Fin n)`, not the sup distance of `Fin n → ℝ`. $x_1\ge\dots\ge x_n$ is `Antitone x` on `Fin n`.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), pp. 13–14, §4.1 (definition of X̄(ℓ) and of c_k)

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting

namespace SeqLoss.Equidistance

/-- The ideal allocation `c_k = (L/k, …, L/k, 0, …, 0)` (§4.1, p. 14): the first `k` agents
(0-based indices `i < k`) each pay `L / k`, the others pay `0`. Meaningful for `1 ≤ k ≤ n`. -/
noncomputable def ideal {n : ℕ} (ℓ : Fin n → ℝ) (k : ℕ) : Fin n → ℝ :=
  fun i => if i.val < k then SeqLoss.FixedFraction.total ℓ / k else 0

/-- `x ∈ X̄(ℓ)` (p. 13): `x` is an allocation with `x_1 ≥ ⋯ ≥ x_n`. -/
def IsOrderedAllocation {n : ℕ} (ℓ x : Fin n → ℝ) : Prop :=
  SeqLoss.FixedFraction.IsAllocation ℓ x ∧ Antitone x

/-- The Euclidean distance on `ℝ^n`, through Mathlib's `EuclideanSpace ℝ (Fin n)`
(not the sup distance of `Fin n → ℝ`). -/
noncomputable def euclDist {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 y)

/-- `x` is at equal Euclidean distance from all ideal allocations `c_1, …, c_n`. -/
def IsEquidistantFromIdeals {n : ℕ} (ℓ x : Fin n → ℝ) : Prop :=
  ∀ k k' : ℕ, 1 ≤ k → k ≤ n → 1 ≤ k' → k' ≤ n →
    euclDist x (ideal ℓ k) = euclDist x (ideal ℓ k')

end SeqLoss.Equidistance


