-- Prove2me | Definitions.Def_MTSActionPredictions_SyncRestart_Supplement_Paging
-- name    : MTSActionPredictions_SyncRestart_Supplement_Paging
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:28:11.231921+00:00
-- url     : https://prove2.me/theorems/92d0f4b4-82bd-4514-970e-94650eaa600e
-- title:
--   Fractional weighted paging: configurations, weighted movement cost, and online rules
-- statement:
--   There are $n$ pages with weights $w_p\ge0$ and a cache of size $k$. A **fractional cache configuration** is $x\in[0,1]^n$ with $\sum_p x_p=k$; it is **integral** when every $x_p\in\{0,1\}$. It serves a request to page $p$ iff $x_p=1$. The cost of moving from $x$ to $x'$ is
--   $$d(x,x')=\sum_p w_p\,|x_p-x'_p|,$$
--   so loading and eviction are both charged. For requests $p_1,\dots,p_T$ a sequence $X_0,X_1,\dots,X_T$ **serves** them when each $X_t$ ($t\ge1$) is a fractional configuration with $X_t(p_t)=1$; its cost is $\sum_{t=1}^T d(X_{t-1},X_t)$. A deterministic online rule maps the initial configuration and the revealed prefix of requests to the current configuration.
--
--   These objects state Theorem 10.
--
--   **Formalization Note** Zero weights are allowed: the cost is the explicit weighted sum, not a metric. Request list entry $i$ is the request at time $i+1$.
-- source:
--   Júlia Baligács, Christian Coester, Alexa Tudose, STOC 2027 submission #1248 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1248.pdf; §4, PDF pp. 9–10 / printed pp. 8–9

import Mathlib

open scoped BigOperators

namespace MTSActionPredictions.SyncRestart.Supplement

/-! # Fractional weighted paging (§4, PDF 9–10 / printed 8–9)

There are `n` pages with weights `w_p ≥ 0` and a cache of size `k`. A fractional cache
configuration is `x ∈ [0,1]^n` with `∑_p x_p = k`; it serves a request to page `p` iff `x_p = 1`.
Moving between configurations costs `d(x, x') = ∑_p w_p |x_p − x'_p|` (loading and eviction are
both charged). Request list entry `i` is the request at time `i + 1`. -/

/-- A fractional cache configuration of size `k`: `x ∈ [0,1]^n` with `∑_p x_p = k`. -/
def IsFracCache {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : Prop :=
  (∀ p, 0 ≤ x p ∧ x p ≤ 1) ∧ ∑ p, x p = k

/-- An integral cache configuration of size `k`: a fractional one with coordinates in `{0, 1}`. -/
def IsIntegralCache {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : Prop :=
  IsFracCache k x ∧ ∀ p, x p = 0 ∨ x p = 1

/-- The weighted distance `d(x, x') = ∑_p w_p |x_p − x'_p|`. -/
def cacheDist {n : ℕ} (w : Fin n → ℝ) (x x' : Fin n → ℝ) : ℝ :=
  ∑ p, w p * |x p - x' p|

/-- The total movement cost `∑_{t=1}^T d(X_{t−1}, X_t)` of a sequence of configurations. -/
def pagingCost {n : ℕ} (w : Fin n → ℝ) (T : ℕ) (X : ℕ → Fin n → ℝ) : ℝ :=
  ∑ t ∈ Finset.range T, cacheDist w (X t) (X (t + 1))

/-- A sequence of configurations serves the requests `q`: for every `1 ≤ t ≤ T`, `X_t` is a
fractional cache configuration of size `k` holding the requested page fully, `X_t(p_t) = 1`. -/
def ServesRequests {n : ℕ} (k : ℕ) (q : List (Fin n)) (X : ℕ → Fin n → ℝ) : Prop :=
  ∀ (t : ℕ) (ht : t < q.length), IsFracCache k (X (t + 1)) ∧ X (t + 1) q[t] = 1

/-- A deterministic online algorithm for fractional weighted paging: the initial configuration and
the revealed prefix of requested pages determine the current configuration. -/
abbrev PagingRule (n : ℕ) := (Fin n → ℝ) → List (Fin n) → (Fin n → ℝ)

/-- The configurations produced by a paging rule from `x₀` on requests `q`; time `0` is `x₀`. -/
def pagingTraj {n : ℕ} (A : PagingRule n) (x₀ : Fin n → ℝ) (q : List (Fin n)) (t : ℕ) :
    Fin n → ℝ :=
  if t = 0 then x₀ else A x₀ (q.take t)

end MTSActionPredictions.SyncRestart.Supplement


