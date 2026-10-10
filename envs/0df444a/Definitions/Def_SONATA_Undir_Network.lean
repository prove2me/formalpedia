-- Prove2me | Definitions.Def_SONATA_Undir_Network
-- name    : SONATA_Undir_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T19:14:58.791371+00:00
-- url     : https://prove2.me/theorems/5d17dce3-b546-40be-8edc-763b95422367
-- title:
--   (21), (22), (25), (26), Assumption D — stacked vectors, consensus errors, graph-compliant doubly stochastic weights and ρ = σ(Ŵ − J)
-- statement:
--   This module fixes the network notation of Sun, Daneshmand and Scutari for $m$ agents, each holding a vector in $\mathbb R^d$.
--
--   1. **Stacked vectors** (21). A stacked vector is $\mathbf x=[\mathbf x_1^\top,\dots,\mathbf x_m^\top]^\top\in\mathbb R^{md}$, with $\mathbf x_i\in\mathbb R^d$ the copy of agent $i$. Its Euclidean norm is
--   $$\|\mathbf x\|=\Big(\sum_{i=1}^m\|\mathbf x_i\|^2\Big)^{1/2}.$$
--   2. **Average and consensus error** (22). $\bar{\mathbf x}=\frac1m\sum_{i=1}^m\mathbf x_i$ and $\mathbf x_\perp=\mathbf x-\mathbf 1_m\otimes\bar{\mathbf x}$, whose $i$-th block is $\mathbf x_i-\bar{\mathbf x}$.
--   3. **Mixing** (25). For an $m\times m$ matrix $\mathbf W=(w_{ij})$, $\widehat{\mathbf W}=\mathbf W\otimes\mathbf I_d$ acts on stacked vectors by $(\widehat{\mathbf W}\mathbf x)_i=\sum_j w_{ij}\mathbf x_j$.
--   4. **Assumption D.** Given an undirected graph $\mathcal G=(\mathcal V,\mathcal E)$ on $\mathcal V=\{1,\dots,m\}$, the matrix $\mathbf W$ satisfies: (D1) $w_{ii}>0$ for all $i$; (D2) $w_{ij}>0$ if $(i,j)\in\mathcal E$ and $w_{ij}=0$ otherwise; and $\mathbf W$ is doubly stochastic, $\mathbf 1^\top\mathbf W=\mathbf 1^\top$ and $\mathbf W\mathbf 1=\mathbf 1$.
--   5. **The mixing rate** (26). With $\mathbf J=\frac1m\mathbf 1_m\mathbf 1_m^\top\otimes\mathbf I_d$,
--   $$\rho=\sigma(\widehat{\mathbf W}-\mathbf J),$$
--   the largest singular value of $\widehat{\mathbf W}-\mathbf J$.
--
--   Under Assumptions B (connectivity) and D, $\rho<1$ (the paper's (26)); this module only defines $\rho$, it does not assume the bound.
--
--   **Formalization Note.** A stacked vector is `Fin m → EuclideanSpace ℝ (Fin d)`; Lean's default sup norm on this type is never used, the Euclidean norm is written out as `stackNorm` (and its square `stackNormSq`). The graph is a `SimpleGraph` (symmetric, no self-loops), so "otherwise" in D2 ranges over pairs $i\ne j$ that are not adjacent. Since the factor $\mathbf I_d$ does not change singular values, $\rho$ is the operator norm of $\mathbf W-\frac1m\mathbf 1\mathbf 1^\top$ on Euclidean $\mathbb R^m$ (`Matrix.toEuclideanCLM`).
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, pp. 12, 14, Assumption D, (21), (22), (25), (26)

import Mathlib

namespace SONATA.Undir

/-- The Euclidean space `ℝᵈ` in which every agent's variable lives (Sun, Daneshmand & Scutari,
arXiv:1905.02637v2, Problem (P), p. 1). -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A stacked vector `x = [x₁ᵀ, …, x_mᵀ]ᵀ ∈ ℝ^{md}` ((21), p. 14): component `i` is agent `i`'s
local vector `xᵢ ∈ ℝᵈ`. Lean's default (sup) norm on this type is never used. -/
abbrev Stack (m d : ℕ) := Fin m → E d

/-- The squared Euclidean norm `‖x‖² = ∑ᵢ ‖xᵢ‖²` of a stacked vector (21). -/
noncomputable def stackNormSq {m d : ℕ} (v : Stack m d) : ℝ := ∑ i, ‖v i‖ ^ 2

/-- The Euclidean norm `‖x‖ = (∑ᵢ ‖xᵢ‖²)^{1/2}` of a stacked vector (21). -/
noncomputable def stackNorm {m d : ℕ} (v : Stack m d) : ℝ := Real.sqrt (stackNormSq v)

/-- The average `x̄ = (1/m) ∑ᵢ xᵢ ∈ ℝᵈ` of a stacked vector (p. 14). -/
noncomputable def avg {m d : ℕ} (v : Stack m d) : E d := (m : ℝ)⁻¹ • ∑ i, v i

/-- The consensus disagreement `x_⊥ = x − 1_m ⊗ x̄` ((22), p. 14): component `i` is `xᵢ − x̄`. -/
noncomputable def perp {m d : ℕ} (v : Stack m d) : Stack m d := fun i => v i - avg v

/-- Mixing with a weight matrix, `(Ŵ x)ᵢ = ∑ⱼ wᵢⱼ xⱼ` with `Ŵ = W ⊗ I_d` ((25), p. 14). -/
def mix {m d : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (v : Stack m d) : Stack m d :=
  fun i => ∑ j, W i j • v j

/-- Assumption D (p. 12): the weight matrix `W = (wᵢⱼ)` has a sparsity pattern compliant with the
undirected graph `𝒢 = (𝒱, ℰ)`, `𝒱 = {1, …, m}`:
* D1 `wᵢᵢ > 0` for all `i`;
* D2 `wᵢⱼ > 0` if `(i, j) ∈ ℰ`, and `wᵢⱼ = 0` otherwise (`i ≠ j`, `(i, j) ∉ ℰ`);
* `W` is doubly stochastic: `1ᵀ W = 1ᵀ` and `W 1 = 1`.
The edge set is that of a `SimpleGraph` (symmetric, loopless). -/
structure AssumptionD {m : ℕ} (Gr : SimpleGraph (Fin m)) (W : Matrix (Fin m) (Fin m) ℝ) :
    Prop where
  diag_pos : ∀ i, 0 < W i i
  adj_pos : ∀ i j, i ≠ j → Gr.Adj i j → 0 < W i j
  nonadj_zero : ∀ i j, i ≠ j → ¬ Gr.Adj i j → W i j = 0
  col_sum : ∀ j, ∑ i, W i j = 1
  row_sum : ∀ i, ∑ j, W i j = 1

/-- The averaging matrix `(1/m) 1_m 1_mᵀ` (the `m × m` factor of `J` in (25), p. 14). -/
noncomputable def avgMat (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun _ _ => (m : ℝ)⁻¹

/-- `ρ = σ(Ŵ − J)` ((26), p. 14), the largest singular value of `Ŵ − J = (W − (1/m)11ᵀ) ⊗ I_d`.
The Kronecker factor `I_d` does not change the singular values, so `ρ` is the operator norm of
`W − (1/m)11ᵀ` acting on Euclidean `ℝᵐ`. -/
noncomputable def rho {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (W - avgMat m)‖

end SONATA.Undir


