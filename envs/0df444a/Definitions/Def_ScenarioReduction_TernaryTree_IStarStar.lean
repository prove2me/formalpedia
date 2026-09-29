-- Prove2me | Definitions.Def_ScenarioReduction_TernaryTree_IStarStar
-- name    : ScenarioReduction_TernaryTree_IStarStar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:08:40.544737+00:00
-- url     : https://prove2.me/theorems/f99d7258-9c51-4dc4-9b75-bf0ddeba2d94
-- title:
--   The index set $I_{**}$ of the proof of Proposition 3.2
-- statement:
--   In a regular ternary scenario tree of depth $K$, fix a level $k_0$ with $1 \le k_0 \le K-2$. Call the successor $i_k = 2$ (increment $0$) at level $k$ the **middle** branch and $i_k \in \{1, 3\}$ (increment $\pm\delta^k$) an **outer** branch. The index set $I_{**}$ consists of the scenarios $i$ such that either
--
--   1. $i$ takes the middle branch at level $k_0$ and outer branches at levels $k_0+1$ and $k_0+2$, or
--   2. $i$ takes an outer branch at level $k_0$ and middle branches at levels $k_0+1$ and $k_0+2$.
--
--   In the paper's notation,
--
--   $$
--   I_{**} = \bigl\{ i : (\delta^{k_0}_{i_{k_0}} = 0 \wedge \delta^{k_0+1}_{i_{k_0+1}} \ne 0 \wedge \delta^{k_0+2}_{i_{k_0+2}} \ne 0) \vee (\delta^{k_0}_{i_{k_0}} \ne 0 \wedge \delta^{k_0+1}_{i_{k_0+1}} = 0 \wedge \delta^{k_0+2}_{i_{k_0+2}} = 0) \bigr\}.
--   $$
--
--   The scenarios in $I_{**}$ are the ones kept in the optimal reduction of Proposition 3.2.
--
--   **Formalization Note** The paper tests the increments $\delta^k_{i_k}$ for being zero. This definition tests the branch indices instead ($\sigma(r) = 1$ in $\mathrm{Fin}\,3$ for the middle branch at level $r+1$). The two agree whenever $\delta^{k_0}, \delta^{k_0+1}, \delta^{k_0+2} > 0$; when one of these widths is $0$ the paper's value test no longer singles out the middle branch and its set does not have $\tfrac29 N$ elements, while the index-based set does. The definition depends only on $K$ and $k_0$. For a level outside $1, \dots, K$ neither predicate holds.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), pp. 198–199, proof of Proposition 3.2

import Mathlib

namespace ScenarioReduction.TernaryTree

/-- Scenario `σ` takes the middle branch (increment `0`) at paper level `l` (`1 ≤ l ≤ K`). -/
def IsMid {K : ℕ} (σ : Fin K → Fin 3) (l : ℕ) : Prop :=
  ∃ r : Fin K, r.val + 1 = l ∧ σ r = 1

/-- Scenario `σ` takes an outer branch (increment `±δ^l`) at paper level `l` (`1 ≤ l ≤ K`). -/
def IsOuter {K : ℕ} (σ : Fin K → Fin 3) (l : ℕ) : Prop :=
  ∃ r : Fin K, r.val + 1 = l ∧ σ r ≠ 1

/-- The index set `I_**` of the proof of Proposition 3.2 of Heitsch–Römisch (2003), stated by
branch indices: the middle branch at level `k0` and outer branches at levels `k0+1`, `k0+2`, or an
outer branch at level `k0` and middle branches at levels `k0+1`, `k0+2`. -/
noncomputable def IStarStar (K k0 : ℕ) : Finset (Fin K → Fin 3) := by
  classical
  exact Finset.univ.filter (fun σ =>
    (IsMid σ k0 ∧ IsOuter σ (k0 + 1) ∧ IsOuter σ (k0 + 2)) ∨
    (IsOuter σ k0 ∧ IsMid σ (k0 + 1) ∧ IsMid σ (k0 + 2)))

end ScenarioReduction.TernaryTree


