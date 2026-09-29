-- Prove2me | Definitions.Def_ScenarioReduction_ForwardSelection_IsFastForwardRun
-- name    : ScenarioReduction_ForwardSelection_IsFastForwardRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:57:15.730639+00:00
-- url     : https://prove2.me/theorems/130e3d25-a1a1-43fd-a247-e24657e02137
-- title:
--   Algorithm 2.4 (fast forward selection) and the forward selection principle (16)
-- statement:
--   Let $c=(c_{kv})$ be a cost matrix and $p_1,\dots,p_N$ probabilities. A candidate run is a sequence $u_1,u_2,\dots$ of indices in $\{1,\dots,N\}$. Put $J^{[0]}=\{1,\dots,N\}$ and $J^{[i]}=\{1,\dots,N\}\setminus\{u_1,\dots,u_i\}$.
--
--   The quantities of **Algorithm 2.4** are defined recursively:
--   $$
--   c^{[1]}_{kv}=c_{kv},\qquad c^{[i]}_{kv}=\min\bigl\{c^{[i-1]}_{kv},\,c^{[i-1]}_{ku_{i-1}}\bigr\}\quad(i\ge 2),
--   $$
--   $$
--   z^{[i]}_v=\sum_{k\in J^{[i-1]}\setminus\{v\}}p_k\,c^{[i]}_{kv}\qquad(i\ge 1).
--   $$
--   For $i=1$ the sum runs over all $k\neq v$, as in Step 1 of the algorithm.
--
--   1. $u_1,\dots,u_n$ is a **run of Algorithm 2.4** if, for each $i=1,\dots,n$, $u_i\in J^{[i-1]}$ and $z^{[i]}_{u_i}\le z^{[i]}_v$ for every $v\in J^{[i-1]}$, i.e. $u_i\in\arg\min_{v\in J^{[i-1]}}z^{[i]}_v$ with any tie-breaking.
--   2. $u_1,\dots,u_n$ satisfies the **forward selection principle (16)** if, for each $i=1,\dots,n$, $u_i\in J^{[i-1]}$ and
--   $$
--   u_i\in\arg\min_{v\in J^{[i-1]}}\ \sum_{k\in J^{[i-1]}\setminus\{v\}}p_k\min_{j\notin J^{[i-1]}\setminus\{v\}}c_{kj}=\arg\min_{v\in J^{[i-1]}}D_{J^{[i-1]}\setminus\{v\}} .
--   $$
--
--   Forward selection builds the kept set one scenario at a time; Algorithm 2.4 evaluates its objective by an $O(N)$ update of the matrix $c^{[i]}$ per step instead of recomputing each inner minimum.
--
--   **Formalization Note** Steps are 1-based: the run is a function `u : ℕ → Fin N` whose value at $0$ is never used. $c^{[i]}$ is defined for all $k,v$ (the paper uses it only for $k,v\in J^{[i-1]}$), and index $0$ repeats $c$ and is unused. The recursion is the printed pairwise minimum with $u_{i-1}$, not a closed form. The file also records that $J^{[i]}$ has nonempty complement for $i\ge 1$ (it misses $u_i$).
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 193, eq. (16); pp. 193–194, Algorithm 2.4, Steps 1 and i

import Mathlib
import Definitions.Def_ScenarioReduction_ForwardSelection_reductionCost

namespace ScenarioReduction.ForwardSelection

variable {N : ℕ}

/-- The indices selected in steps `1, …, i`: `{u₁, …, uᵢ}`. A run is a sequence `u : ℕ → Fin N`
with 1-based steps; `u 0` is never used. -/
def sel (u : ℕ → Fin N) (i : ℕ) : Finset (Fin N) :=
  (Finset.Icc 1 i).image u

/-- `J^{[i]} = {1, …, N} ∖ {u₁, …, uᵢ}` (p. 193 and Algorithm 2.4); `J^{[0]} = {1, …, N}`. -/
def Jstep (u : ℕ → Fin N) (i : ℕ) : Finset (Fin N) :=
  Finset.univ \ sel u i

/-- For `i ≥ 1`, `uᵢ ∉ J^{[i]}`, so the complement of `J^{[i]}` is nonempty. -/
theorem Jstep_compl_nonempty (u : ℕ → Fin N) {i : ℕ} (hi : 1 ≤ i) : (Jstep u i)ᶜ.Nonempty :=
  ⟨u i, by simp only [Jstep, sel, Finset.mem_compl, Finset.mem_sdiff, Finset.mem_univ, true_and,
             not_not]
           exact Finset.mem_image.2 ⟨i, Finset.mem_Icc.2 ⟨hi, le_rfl⟩, rfl⟩⟩

/-- The cost matrices of Algorithm 2.4 (pp. 193–194):
`c^{[1]}_{kv} = c(ωₖ, ωᵥ)` and `c^{[i]}_{kv} = min{c^{[i-1]}_{kv}, c^{[i-1]}_{k u_{i-1}}}` for `i ≥ 2`.
They are defined for all `k, v` (the paper uses them for `k, v ∈ J^{[i-1]}`); index `0` repeats
`c` and is never used. -/
def cStep (c : Fin N → Fin N → ℝ) (u : ℕ → Fin N) : ℕ → Fin N → Fin N → ℝ
  | 0, k, v => c k v
  | 1, k, v => c k v
  | i + 2, k, v => min (cStep c u (i + 1) k v) (cStep c u (i + 1) k (u (i + 1)))

/-- `z^{[i]}_v = ∑_{k ∈ J^{[i-1]} ∖ {v}} pₖ c^{[i]}_{kv}` (Algorithm 2.4); for `i = 1` the sum runs
over `k ≠ v`. -/
def zStep (c : Fin N → Fin N → ℝ) (p : Fin N → ℝ) (u : ℕ → Fin N) (i : ℕ) (v : Fin N) : ℝ :=
  ∑ k ∈ (Jstep u (i - 1)).erase v, p k * cStep c u i k v

/-- `u₁, …, uₙ` is a run of Algorithm 2.4 (fast forward selection), with any tie-breaking:
for each `i = 1, …, n`, `uᵢ ∈ arg min_{v ∈ J^{[i-1]}} z^{[i]}_v`. -/
def IsFastForwardRun (c : Fin N → Fin N → ℝ) (p : Fin N → ℝ) (n : ℕ) (u : ℕ → Fin N) : Prop :=
  ∀ i ∈ Finset.Icc 1 n, u i ∈ Jstep u (i - 1) ∧
    ∀ v ∈ Jstep u (i - 1), zStep c p u i (u i) ≤ zStep c p u i v

/-- `u₁, …, uₙ` satisfies the forward selection principle (16), p. 193: for each `i = 1, …, n`,
`uᵢ ∈ arg min_{v ∈ J^{[i-1]}} D_{J^{[i-1]} ∖ {v}}`, where `D` is the reduction cost (8). -/
def IsForwardSelection (c : Fin N → Fin N → ℝ) (p : Fin N → ℝ) (n : ℕ) (u : ℕ → Fin N) : Prop :=
  ∀ i ∈ Finset.Icc 1 n, u i ∈ Jstep u (i - 1) ∧
    ∀ v ∈ Jstep u (i - 1),
      reductionCost c p ((Jstep u (i - 1)).erase (u i)) (compl_erase_nonempty _ _) ≤
        reductionCost c p ((Jstep u (i - 1)).erase v) (compl_erase_nonempty _ _)

end ScenarioReduction.ForwardSelection


