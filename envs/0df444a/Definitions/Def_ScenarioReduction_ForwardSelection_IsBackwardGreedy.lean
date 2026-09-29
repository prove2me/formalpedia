-- Prove2me | Definitions.Def_ScenarioReduction_ForwardSelection_IsBackwardGreedy
-- name    : ScenarioReduction_ForwardSelection_IsBackwardGreedy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:57:33.9414+00:00
-- url     : https://prove2.me/theorems/de0ccd2a-e7e8-48d0-8381-1dccbd6f4e4b
-- title:
--   Single-deletion costs $p_l\min_{j\ne l}c(\omega_l,\omega_j)$ of (9) and the greedy selection rule (11)
-- statement:
--   Let $N\ge 2$, let $c=(c_{lj})$ be a cost matrix and $p_1,\dots,p_N$ probabilities. The **single-deletion cost** of scenario $l$ is
--   $$
--   a_l=p_l\min_{j\neq l}c_{lj},
--   $$
--   the objective of problem (9), i.e. the reduction cost of deleting $l$ alone.
--
--   A sequence $l_1,\dots,l_m$ is selected by **rule (11)** if, for each $i=1,\dots,m$,
--   $$
--   l_i\in\arg\min_{l\in\{1,\dots,N\}\setminus\{l_1,\dots,l_{i-1}\}}a_l ,
--   $$
--   with any tie-breaking. The indices are then distinct, and $a_{l_1}\le a_{l_2}\le\cdots$ lists the $m$ smallest single-deletion costs.
--
--   **Formalization Note** The sequence is a function `l : ℕ → Fin N` with 1-based steps; its value at $0$ is unused. The hypothesis $N\ge 2$ makes $\{j:j\neq l\}$ nonempty, so the inner minimum is a `Finset.inf'`; the file records that fact as a lemma.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 191, eqs. (9) and (11)

import Mathlib

namespace ScenarioReduction.ForwardSelection

variable {N : ℕ}

/-- For `N ≥ 2` and any index `l`, the set `{j : j ≠ l}` is nonempty. -/
theorem univ_erase_nonempty (hN : 1 < N) (l : Fin N) : (Finset.univ.erase l).Nonempty :=
  Finset.card_pos.1 (by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega)

/-- The single-deletion cost `a_l = p_l · min_{j ≠ l} c(ω_l, ω_j)` of eq. (9), p. 191. -/
noncomputable def singleCost (c : Fin N → Fin N → ℝ) (p : Fin N → ℝ) (hN : 1 < N) (l : Fin N) :
    ℝ :=
  p l * (Finset.univ.erase l).inf' (univ_erase_nonempty hN l) (fun j => c l j)

/-- `l₁, …, l_m` (1-based, `l : ℕ → Fin N`) are selected by rule (11), p. 191:
`lᵢ ∈ arg min_{l ∈ {1..N} ∖ {l₁, …, l_{i-1}}} p_l min_{j ≠ l} c(ω_l, ω_j)` for `i = 1, …, m`. -/
def IsBackwardGreedy (c : Fin N → Fin N → ℝ) (p : Fin N → ℝ) (hN : 1 < N) (m : ℕ)
    (l : ℕ → Fin N) : Prop :=
  ∀ i ∈ Finset.Icc 1 m, l i ∉ (Finset.Ico 1 i).image l ∧
    ∀ l' : Fin N, l' ∉ (Finset.Ico 1 i).image l → singleCost c p hN (l i) ≤ singleCost c p hN l'

end ScenarioReduction.ForwardSelection


