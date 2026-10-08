-- Prove2me | Definitions.Def_PrimalDualSubgrad_Stoch_SDA
-- name    : PrimalDualSubgrad_Stoch_SDA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:46:06.353987+00:00
-- url     : https://prove2.me/theorems/9a797387-ea36-4c4a-ba13-2e70ddcba83c
-- title:
--   Method of Simple Dual Averages (2.21) and $L_k = \max_{i\le k}\|g_i\|_*$
-- statement:
--   Let $d$ be a prox-function of $Q$ with prox-center $x_0$, $\pi_\beta$ the corresponding argmin map and $\hat\beta_k$ the sequence (2.19). Fix $\gamma > 0$ and a sequence of answers $g_0, g_1, \dots \in E^*$. The **method of simple dual averages** generates
--   $$x_0 = \text{prox-center}, \qquad s_{k+1} = \sum_{i=0}^k g_i, \qquad x_{k+1} = \pi_{\gamma\hat\beta_{k+1}}(-s_{k+1}), \quad k \ge 0.$$
--   In the paper $g_k = \mathcal G(x_k)$ is the answer of a black-box oracle at $x_k$; here the answers are arbitrary data, which covers every oracle, including the stochastic one of §6.
--
--   We also write $L_k = \max_{0 \le i \le k} \|g_i\|_*$.
--
--   This is the dual averaging scheme (2.14) with unit weights $\lambda_k = 1$ and $\beta_k = \gamma\hat\beta_k$; its stochastic version is studied in §6.
--
--   **Formalization Note** The initial point is the prox-center, which is $\pi_{\beta_0}(0)$ in the paper's general scheme; the box (2.21) does not repeat it. The points of the method are a function of the whole answer sequence $g$.
-- source:
--   Nesterov, Primal-dual subgradient methods for convex problems, Math. Program. 120 (2009), p. 11, (2.21) and Theorem 2 (L_k)

import Mathlib
import Definitions.Def_PrimalDualSubgrad_Stoch_ProxSetting

namespace PrimalDualSubgrad.Stoch

open Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Nesterov 2009, p. 11, (2.21), the Method of Simple Dual Averages, for a given sequence of
oracle answers `g : ℕ → E*`: `x₀` is the prox-center, `s_{k+1} = ∑_{i=0}^k g_i` and
`x_{k+1} = π_{γ β̂_{k+1}}(-s_{k+1})`. (In (2.21) `g_k = G(x_k)`; taking `g` as data covers every
oracle, deterministic or not.) -/
noncomputable def sdaPoints (π : ℝ → StrongDual ℝ E → E) (γ : ℝ) (x0 : E)
    (g : ℕ → StrongDual ℝ E) : ℕ → E
  | 0 => x0
  | (k + 1) => π (γ * betaHat (k + 1)) (-(∑ i ∈ range (k + 1), g i))

/-- `L_k = max_{0 ≤ i ≤ k} ‖g_i‖_*` (Nesterov 2009, p. 11, Theorem 2); the dual norm is the
operator norm on `StrongDual ℝ E`. -/
noncomputable def maxDualNorm (g : ℕ → StrongDual ℝ E) (k : ℕ) : ℝ :=
  (range (k + 1)).sup' nonempty_range_add_one (fun i => ‖g i‖)

end PrimalDualSubgrad.Stoch


