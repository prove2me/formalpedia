-- Prove2me | Definitions.Def_RestartPD_Adaptive_Restarts
-- name    : RestartPD_Adaptive_Restarts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T17:44:09.945718+00:00
-- url     : https://prove2.me/theorems/d7b40f45-6a6f-4f26-b7ea-c8a1103b31aa
-- title:
--   Algorithm 1 with adaptive restart criterion (30)
-- statement:
--   For each feasible start $z^0$, let $\mathcal R(z^0)$ be the set of admissible sequences of averaged inner outputs $\bar z^t$. **Property 3** says that fixed constants $q,C>0$ work for every such start, every admissible sequence, and every integer $t\ge1$: $\bar z^t$ is feasible and
--   $$
--   \rho_{\|\bar z^t-z^0\|_p}(\bar z^t)\le\frac{2C\|\bar z^t-z^0\|_p}{t},\qquad
--   \|\bar z^t-z^0\|_p\le(q+2)\operatorname{dist}_p(z^0,Z^\star).
--   $$
--
--   An adaptive run consists of outer starts $z^{k,0}$, inner averages $\bar z^{k,t}$, and positive restart lengths $\tau^k$. At every restart $z^{k+1,0}=\bar z^{k,\tau^k}$. The first length $\tau^0$ is selected by the user. For $k\ge1$, $\tau^k$ is the first positive $t$ for which
--   $$
--   \rho_{\|\bar z^{k,t}-z^{k,0}\|_p}(\bar z^{k,t})\le
--   \beta\rho_{\|z^{k,0}-z^{k-1,0}\|_p}(z^{k,0}).
--   $$
--
--   The first-trigger requirement is the algorithmic part needed to bound each later restart length.
--
--   **Formalization Note** A run is a set-valued relation because an inner primal–dual step can have multiple outputs. The value at inner time zero is unused. Both sides of the restart test use extended-real gaps, including the right-limsup definition when a seminorm displacement is zero.
-- source:
--   Applegate, Hinder, Lu & Lubin, Faster First-Order Primal-Dual Methods for Linear Programming using Restarts and Sharpness, arXiv:2105.12715v4, pp. 9–10 and 15–16, Property 3, Algorithm 1, (30)

import Mathlib
import Definitions.Def_RestartPD_Fixed_Problem
import Definitions.Def_RestartPD_Fixed_Algorithms

namespace RestartPD.Adaptive

variable {n m : ℕ}

/-- The n ≥ 1 branch of the adaptive restart criterion (30). -/
def RestartCond (L : RestartPD.Fixed.Primal n → RestartPD.Fixed.Dual m → ℝ) (X : Set (RestartPD.Fixed.Primal n))
    (Y : Set (RestartPD.Fixed.Dual m)) (p : Seminorm ℝ (RestartPD.Fixed.E n m)) (β : ℝ)
    (z : ℕ → RestartPD.Fixed.E n m) (zb : ℕ → ℕ → RestartPD.Fixed.E n m) (n t : ℕ) : Prop :=
  RestartPD.Fixed.rho L X Y p (p (zb n t - z n)) (zb n t) ≤
    ((β : ℝ) : EReal) *
      RestartPD.Fixed.rho L X Y p (p (z n - z (n - 1))) (z n)

/-- Algorithm 1 with rule (30): the first interval is prescribed; every later interval
is the first positive time at which the normalized-gap condition holds. -/
def IsAdaptiveRestartRun (L : RestartPD.Fixed.Primal n → RestartPD.Fixed.Dual m → ℝ)
    (X : Set (RestartPD.Fixed.Primal n)) (Y : Set (RestartPD.Fixed.Dual m))
    (p : Seminorm ℝ (RestartPD.Fixed.E n m)) (Runs : RestartPD.Fixed.E n m → Set (ℕ → RestartPD.Fixed.E n m))
    (β : ℝ) (τ : ℕ → ℕ) (z : ℕ → RestartPD.Fixed.E n m)
    (zb : ℕ → ℕ → RestartPD.Fixed.E n m) : Prop :=
  1 ≤ τ 0 ∧
    (∀ k, zb k ∈ Runs (z k) ∧ z (k + 1) = zb k (τ k)) ∧
    ∀ k, 1 ≤ k →
      1 ≤ τ k ∧ RestartCond L X Y p β z zb k (τ k) ∧
        ∀ t, 1 ≤ t → t < τ k → ¬ RestartCond L X Y p β z zb k t

end RestartPD.Adaptive


