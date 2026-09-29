-- Prove2me | Definitions.Def_ScenarioReduction_TernaryTree_scenario
-- name    : ScenarioReduction_TernaryTree_scenario
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:07:57.822019+00:00
-- url     : https://prove2.me/theorems/4f61c376-a102-4768-8ef0-4ffc58eb0958
-- title:
--   Regular ternary scenario tree: $\omega_i^k = \sum_{j=0}^{k} \delta^j_{i_j}$ with $\delta^j_{i_j} = (i_j - 2)\delta^j$ (eq. (19))
-- statement:
--   Fix a depth $K \in \mathbb{N}$ and branch widths $\delta^1, \dots, \delta^K \ge 0$. A **regular ternary scenario tree** has $N = 3^K$ scenarios $\omega_i = (\omega_i^0, \omega_i^1, \dots, \omega_i^K) \in \mathbb{R}^{K+1}$, one for each index tuple $(i_1, \dots, i_K) \in \{1,2,3\}^K$, where $i_k$ records which of the three successors the path takes at level $k$. Level $k$ has the symmetric set of increments $V_k = \{-\delta^k, 0, \delta^k\}$, and choosing successor $i_k$ adds $\delta^k_{i_k} = (i_k - 2)\,\delta^k$. The scenario is the running sum
--
--   $$
--   \omega_i^k = \sum_{j=0}^{k} \delta^j_{i_j}, \qquad k = 0, 1, \dots, K,
--   $$
--
--   with $\delta^0 = 0$, so every scenario starts at the common root $\omega_i^0 = 0$.
--
--   This is the test family of Section 3 of Heitsch and Römisch: trees for which the optimal scenario-reduction distance can be computed in closed form.
--
--   **Formalization Note** A scenario is indexed by $\sigma : \mathrm{Fin}\,K \to \mathrm{Fin}\,3$; the entry $\sigma(r)$ is the successor chosen at paper level $r+1$, and the values $0, 1, 2$ of $\mathrm{Fin}\,3$ stand for the paper's $i = 1, 2, 3$, i.e. for the increments $-\delta^{r+1}, 0, +\delta^{r+1}$. The widths are a function $\delta : \mathbb{N} \to \mathbb{R}$ of which only $\delta(1), \dots, \delta(K)$ are used; the paper's $\delta^0 = 0$ is built in by starting the sum at level $1$. The scenario is a vector in $\mathrm{Fin}(K+1) \to \mathbb{R}$, whose Mathlib norm is the maximum norm $\max_{k} |\omega^k|$ used by the paper.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), pp. 195–196, §3, eq. (19) and the paragraph after it

import Mathlib

namespace ScenarioReduction.TernaryTree

/-- Regular ternary scenario tree, eq. (19) of Heitsch–Römisch (2003), with `d = 3`.
A scenario is indexed by `σ : Fin K → Fin 3`, where `σ r` is the branch taken at paper level
`r + 1`; the `Fin 3` values `0, 1, 2` stand for the paper's indices `i = 1, 2, 3`, i.e. for the
increments `-δ^{r+1}, 0, +δ^{r+1}`. The scenario is the vector `(ω⁰, …, ωᴷ) ∈ ℝ^{K+1}` with
`ωᵏ = Σ_{j=1}^{k} (i_j - 2) δ^j`; level `0` is the empty sum (the common root, `δ⁰ = 0`). -/
noncomputable def scenario {K : ℕ} (δ : ℕ → ℝ) (σ : Fin K → Fin 3) : Fin (K + 1) → ℝ :=
  fun k => ∑ r ∈ Finset.univ.filter (fun r : Fin K => r.val < k.val),
    (((σ r : ℕ) : ℝ) - 1) * δ (r.val + 1)

end ScenarioReduction.TernaryTree


