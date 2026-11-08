-- Prove2me | Definitions.Def_LowDimMeanEst_Algorithm2
-- name    : LowDimMeanEst_Algorithm2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:44:25.010829+00:00
-- url     : https://prove2.me/theorems/1f463c48-e6f5-4d86-8c66-c23428510351
-- title:
--   Algorithm 2 (trimming weights) as a relation, with the $\alpha=0$ output when the search has none (correction C1)
-- statement:
--   **Algorithm 2** receives samples $x_1,\dots,x_N\in\mathbb R^d$ and $\delta>0$. For a level $\alpha\ge0$ consider the convex program
--
--   $$\min_{w\in[0,1]^N}\ \sum_i w_i^2\qquad\text{s.t.}\qquad \frac1N\sum_{i=1}^N(1-w_i)\,x_ix_i^\top\preceq\alpha I .$$
--
--   Its feasible set is nonempty and its objective strictly convex, so it has a unique solution $w(\alpha)$. Let $\alpha_{\max}=\big\|\frac1N\sum_ix_ix_i^\top\big\|_{op}$. The algorithm searches $\alpha\in[0,\alpha_{\max}]$ for a solution with
--
--   $$\sum_i w_i(\alpha)=\tfrac13\log\tfrac1\delta ,$$
--
--   and returns those weights. An **output of the printed search** is any such $w(\alpha)$.
--
--   **Correction C1.** A sample $x_i=0$ receives $w_i=0$ at every level, so when fewer than $\frac13\log\frac1\delta$ samples are nonzero the printed search has no output (for example, if $D$ is a point mass, every recentred sample in Algorithm 1 is $0$). In that case the corrected algorithm returns the solution at $\alpha=0$, which keeps every nonzero sample with weight $1$; this is where the paper's binary search converges, since the sum is too small at every midpoint. On inputs where the printed search has an output, the two algorithms have the same outputs.
--
--   **Formalization Note** The constraint $\frac1N\sum(1-w_i)x_ix_i^\top\preceq\alpha I$ is written as $\frac1N\sum_i(1-w_i)\langle x_i,z\rangle^2\le\alpha\|z\|^2$ for all $z$. The binary search is replaced by its specification, a relation: every admissible $\alpha$ gives an output, and the theorems of the mission quantify over all outputs.
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Algorithm 2, p.9

import Mathlib
import Definitions.Def_LowDimMeanEst_Basic

open MeasureTheory

namespace LowDimMeanEst

/-!
# Algorithm 2 (sample trimming weights), as a relation, with the correction C1

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…), Algorithm 2, p.9:

"Input: n′ samples {x′ᵢ} ∈ ℝᵈ, and parameter δ > 0.
1. Compute α_max = ∥(1/n′) Σᵢ x′ᵢ x′ᵢ⊤∥op.
2. Binary search over parameter α ∈ [0, α_max], such that the solution {wᵢ} to the below SDP
   satisfies Σᵢ wᵢ = (1/3) log(1/δ):
   w = arg min_{0≤w₁,…,w_{n′}≤1} Σᵢ wᵢ²  s.t. (1/n′) Σ_{i=1}^{n′} (1 − wᵢ) x′ᵢ x′ᵢ⊤ ⪯ αI.
3. Return {wᵢ}."

**Formalization Note.**
* Samples are `x : Fin N → E d` (`N = n′`, indices 0-based). The constraint
  `(1/N) Σ (1 − wᵢ) xᵢxᵢ⊤ ⪯ αI` is written in its quadratic-form version: for every `z`,
  `(1/N) Σ (1 − wᵢ)⟨xᵢ, z⟩² ≤ α‖z‖²`. At `N = 0` Lean's `1/0 = 0` makes the constraint `0 ≤ α‖z‖²`.
* The binary search is replaced by its specification (`IsSearchOutput`): an output is the solution
  of the program at **some** `α ∈ [0, α_max]` whose weights sum to exactly `(1/3) log(1/δ)`. The
  relation does not pick a value: every such solution is an output, and the statements of the
  mission quantify over all of them.
* **Correction C1** (`IsTrimOutput`). A sample `xᵢ = 0` receives `wᵢ = 0` at every `α`, so when
  fewer than `(1/3) log(1/δ)` samples are nonzero no `α` reaches the required sum and the printed
  algorithm has no output (for instance when `D` is a point mass, every recentred sample is `0`).
  In that case the output is the solution at `α = 0`, which is the limit of the paper's binary
  search (the sum is too small at every midpoint, so the search moves to `0`). On every input
  where the printed algorithm has an output, the outputs coincide.
-/

/-- Feasibility for the program of Algorithm 2 at level `α`: `w ∈ [0,1]^N` and
`(1/N) Σᵢ (1 − wᵢ) xᵢxᵢ⊤ ⪯ αI`. -/
def IsFeasible {d N : ℕ} (x : Fin N → E d) (α : ℝ) (w : Fin N → ℝ) : Prop :=
  (∀ i, 0 ≤ w i ∧ w i ≤ 1) ∧
    ∀ z : E d, (1 / (N : ℝ)) * ∑ i, (1 - w i) * (inner ℝ (x i) z) ^ 2 ≤ α * ‖z‖ ^ 2

/-- `w` solves the program of Algorithm 2 at level `α`: feasible and minimizing `Σᵢ wᵢ²` among
feasible weights. -/
def IsTrimSolution {d N : ℕ} (x : Fin N → E d) (α : ℝ) (w : Fin N → ℝ) : Prop :=
  IsFeasible x α w ∧ ∀ w' : Fin N → ℝ, IsFeasible x α w' → ∑ i, w i ^ 2 ≤ ∑ i, w' i ^ 2

/-- `α_max = ∥(1/N) Σᵢ xᵢxᵢ⊤∥op` (Algorithm 2, step 1). `(innerSL ℝ xᵢ).smulRight xᵢ` is the map
`z ↦ ⟨xᵢ, z⟩ xᵢ`, i.e. the matrix `xᵢxᵢ⊤`. -/
noncomputable def alphaMax {d N : ℕ} (x : Fin N → E d) : ℝ :=
  ‖(1 / (N : ℝ)) • ∑ i, (innerSL ℝ (x i)).smulRight (x i)‖

/-- An output of the printed Algorithm 2: the solution at some `α ∈ [0, α_max]` whose weights sum
to `(1/3) log(1/δ)`. -/
def IsSearchOutput {d N : ℕ} (x : Fin N → E d) (δ : ℝ) (w : Fin N → ℝ) : Prop :=
  ∃ α : ℝ, 0 ≤ α ∧ α ≤ alphaMax x ∧ IsTrimSolution x α w ∧ ∑ i, w i = logInv δ / 3

/-- An output of Algorithm 2 with correction C1: an output of the printed search, or, when the
printed search has none, the solution at `α = 0`. -/
def IsTrimOutput {d N : ℕ} (x : Fin N → E d) (δ : ℝ) (w : Fin N → ℝ) : Prop :=
  IsSearchOutput x δ w ∨ ((¬ ∃ w' : Fin N → ℝ, IsSearchOutput x δ w') ∧ IsTrimSolution x 0 w)

end LowDimMeanEst


