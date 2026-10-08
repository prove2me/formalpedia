-- Prove2me | Definitions.Def_WagelmansELS_DualGreedy_Greedy
-- name    : WagelmansELS_DualGreedy_Greedy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:10.630734+00:00
-- url     : https://prove2.me/theorems/24b415c8-6985-45a0-8037-5cd89b69b63e
-- title:
--   Section 4: the greedy forward rule for Program D′
-- statement:
--   For a positive-demand period $j$, the greedy forward rule chooses the largest dual value allowed by constraints $i\le j$ after the earlier values are fixed:
--
--   $$v_j=\min_{1\le i\le j}\left\{c_i+\frac{f_i-\sum_{t=i}^{j-1}d_t\max\{0,v_t-c_i\}}{d_j}\right\}. $$
--
--   If $d_j=0$, the rule imposes no condition on $v_j$. The module also defines one recursive choice that sets each such free coordinate to zero. This separates the mathematical rule, which allows every zero-demand choice, from a concrete witness.
--
--   **Formalization Note** The sum before $j$ uses the half-open interval $[i,j)$ and is empty when $i=j$. Division occurs only in the positive-demand branch of the predicate and construction.
-- source:
--   Wagelmans, Van Hoesel and Kolen, Economic Lot Sizing, Oper. Res. 40 Supp. 1 (1992), p. S153, Section 4, the paragraph after Program D′

import Mathlib
import Definitions.Def_WagelmansELS_DualGreedy_Model

namespace WagelmansELS.DualGreedy

/-- Use of constraint `i` before period `j`; the interval is empty at `i = j`. -/
def pastUse (P : Instance) (v : ℕ → ℝ) (i j : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ico i j, P.d t * max 0 (v t - P.c i)

/-- The upper bound on `v_j` given by constraint `i`, when `d_j > 0`. -/
noncomputable def greedyBound (P : Instance) (v : ℕ → ℝ) (i j : ℕ) : ℝ :=
  P.c i + (P.f i - pastUse P v i j) / P.d j

/-- The greedy forward rule at each positive-demand period. Zero-demand coordinates are free. -/
def IsGreedyForward (P : Instance) (v : ℕ → ℝ) : Prop :=
  ∀ (j : ℕ) (hj1 : 1 ≤ j) (_hjn : j ≤ P.n) (_hdj : 0 < P.d j),
    v j = (Finset.Icc 1 j).inf' (by
      refine ⟨1, Finset.mem_Icc.mpr ?_⟩
      exact ⟨le_refl _, hj1⟩) (fun i => greedyBound P v i j)

/-- One choice of greedy forward solution; zero-demand coordinates are set to zero. -/
noncomputable def greedy (P : Instance) (j : ℕ) : ℝ :=
  (Nat.rec (motive := fun _ => ℕ → ℝ) (fun _ => (0 : ℝ)) (fun k hist =>
    fun t => if t = k + 1 then
      if k + 1 ≤ P.n ∧ 0 < P.d (k + 1) then
        (Finset.Icc 1 (k + 1)).inf' (by
          refine ⟨1, Finset.mem_Icc.mpr ?_⟩
          omega) (fun i => greedyBound P hist i (k + 1))
      else 0
    else hist t) j) j

end WagelmansELS.DualGreedy


