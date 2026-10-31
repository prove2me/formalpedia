-- Prove2me | Definitions.Def_StreamSubmod_threshStep
-- name    : StreamSubmod_threshStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:15.634666+00:00
-- url     : https://prove2.me/theorems/68805f96-eb1a-4209-9868-db4f7c26d43c
-- title:
--   One step of single-threshold selection among $p$ solutions
-- statement:
--   Let $e$ be an arriving element, $S_1,\dots,S_p$ the current solutions and $\theta$ a threshold. Write $f(e\mid S)=f(S\cup\{e\})-f(S)$ for the marginal contribution of $e$ to $S$. The element is added to a solution $S_i$ with
--
--   $$
--   |S_i|<k\quad\text{and}\quad f(e\mid S_i)\ge\theta,
--   $$
--
--   and discarded if there is no such $i$. The threshold used by the algorithms is $\theta=c\tau/k$ with $c=\alpha/(1+\alpha)$. This module defines the marginal, the threshold, the scan through the indices and the step. The step also returns the number of marginal values it computed, which is at most $p$.
--
--   This single step is what Algorithm 1 runs once, and what Algorithm 2 runs once for every guess of $f(\mathrm{OPT})$.
--
--   **Formalization Note** The paper picks an arbitrary admissible $i$. The scan takes the smallest one, in both algorithms. A marginal value is computed only for solutions with fewer than $k$ elements.
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, §2, p.6 (marginal contribution); Algorithm 1, lines 1, 4–5, p.7; Algorithm 2, lines 1, 10–11, p.11

import Mathlib

namespace StreamSubmod

variable {E : Type} [DecidableEq E]

/-- The marginal contribution `f(e | S) = f(S ∪ {e}) - f(S)` (Alaluf, Ene, Feldman, Nguyen & Suh,
arXiv:1911.12959v3, §2, p.6). -/
def marginal (f : Finset E → ℝ) (e : E) (S : Finset E) : ℝ :=
  f (insert e S) - f S

/-- The threshold `cτ/k`, with `c = α/(1+α)` (Algorithm 1, lines 1 and 4, p.7; Algorithm 2, lines 1
and 10, p.11). -/
noncomputable def threshold (α : ℝ) (k : ℕ) (τ : ℝ) : ℝ :=
  α / (1 + α) * τ / (k : ℝ)

/-- The test "there exists an integer `1 ≤ i ≤ p` such that `|S_i| < k` and `f(e | S_i) ≥ θ`"
(Algorithm 1, line 4, p.7; Algorithm 2, line 10, p.11), as a scan through the indices of a list.
It returns the first index that passes, if any, together with the number of marginal values `f(e | S_i)`
it computed. -/
noncomputable def scan {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E)
    (S : Fin p → Finset E) : List (Fin p) → Option (Fin p) × ℕ
  | [] => (none, 0)
  | i :: is =>
    if (S i).card < k then
      if θ ≤ marginal f e (S i) then (some i, 1)
      else
        let r := scan f k θ e S is
        (r.1, r.2 + 1)
    else scan f k θ e S is

/-- One threshold step on the solutions `S_1, …, S_p`: the element `e` is added to `S_i` for the
smallest `i` passing the test of `scan` with threshold `θ`, and discarded if there is no such `i`
(Algorithm 1, lines 4–5, p.7; Algorithm 2, lines 10–11, p.11). The second component is the number
of marginal values computed.

**Formalization Note.** The paper picks "an arbitrary" admissible `i`; the same rule, the smallest
admissible index, is used in Algorithms 1 and 2. A marginal value is computed only for a solution
with fewer than `k` elements, and at most `p` of them per step. -/
noncomputable def threshStep {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E)
    (S : Fin p → Finset E) : (Fin p → Finset E) × ℕ :=
  match scan f k θ e S (List.finRange p) with
  | (some i, n) => (Function.update S i (insert e (S i)), n)
  | (none, n) => (S, n)

end StreamSubmod


