-- Prove2me | Definitions.Def_ScenarioReduction_BinaryTree_redCost
-- name    : ScenarioReduction_BinaryTree_redCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:02:48.118013+00:00
-- url     : https://prove2.me/theorems/ca7e105e-ed9f-4b3f-ab14-f1c21eae083c
-- title:
--   Reduction cost $D_J=\sum_{i\in J}p_i\min_{j\notin J}\|\omega_i-\omega_j\|_\infty$ of a regular binary tree (eq. (8))
-- statement:
--   Let $\omega_1,\dots,\omega_N$ be the $N=2^K$ scenarios of a regular binary scenario tree with level parameters $\delta^1,\dots,\delta^K$, each with probability $p_i=1/N$. Deleting the scenarios with indices in a set $J\subset\{1,\dots,N\}$ (with at least one scenario kept) and redistributing their probability optimally onto the kept scenarios costs
--
--   $$D_J=\sum_{i\in J}p_i\,\min_{j\notin J}\|\omega_i-\omega_j\|_\infty,\qquad \|\omega-\tilde\omega\|_\infty=\max_{k=0,\dots,K}|\omega^k-\tilde\omega^k|.$$
--
--   This is the objective of the optimal reduction problem (8) with the cost $c(\omega,\tilde\omega)=\|\omega-\tilde\omega\|_\infty$ that Section 3 uses ($h\equiv1$ and the maximum norm on $\mathbb R^{K+1}$). The minimal value of $D_J$ over all $J$ with $\#J=N-n$ is the minimal distance between the original tree and a reduced tree with $n$ scenarios.
--
--   **Formalization Note** The kept set $\{1,\dots,N\}\setminus J$ is required to be nonempty (argument `hJ`), so the inner minimum is a genuine finite minimum (`Finset.inf'`). The weight $p_i=1/2^K$ is written out in every summand. The norm on `Fin (K+1) → ℝ` is Mathlib's sup norm, i.e. exactly $\|\cdot\|_\infty$.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 190, eq. (8); p. 196, choice of c (h ≡ 1, maximum norm) and p_i = 1/N (p. 195)

import Mathlib
import Definitions.Def_ScenarioReduction_BinaryTree_scenario

namespace ScenarioReduction.BinaryTree

/-- Reduction cost of eq. (8) for the regular binary tree with `N = 2^K` scenarios,
uniform weights `p_i = 1/N`, and `c(ω, ω̃) = ‖ω - ω̃‖_∞` (Mathlib's norm on `Fin (K+1) → ℝ`
is the sup norm):
`D_J = ∑_{i ∈ J} p_i min_{j ∉ J} ‖ω_i - ω_j‖_∞`, for a set `J` of deleted scenarios whose
complement is nonempty. -/
noncomputable def redCost {K : ℕ} (δ : ℕ → ℝ) (J : Finset (Fin K → Fin 2))
    (hJ : Jᶜ.Nonempty) : ℝ :=
  ∑ σ ∈ J, (1 / (2 ^ K : ℝ)) * Jᶜ.inf' hJ (fun τ => ‖scenario δ σ - scenario δ τ‖)

end ScenarioReduction.BinaryTree


