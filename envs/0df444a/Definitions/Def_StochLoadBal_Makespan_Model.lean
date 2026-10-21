-- Prove2me | Definitions.Def_StochLoadBal_Makespan_Model
-- name    : StochLoadBal_Makespan_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:33.081757+00:00
-- url     : https://prove2.me/theorems/ca432694-bdcf-4373-ab90-662a07c91342
-- title:
--   Stochastic jobs on unrelated machines: expected makespan, scaling, truncated/exceptional parts and effective size β_k (§2, §2.1, Definition 1, pp. 4–6)
-- statement:
--   This file fixes the model of stochastic load balancing on unrelated machines (StocMakespan) of Gupta, Kumar, Nagarajan and Shen.
--
--   There are $m$ machines $[m]$ and $n$ jobs $[n]$. On a probability space $(\Omega,\mathcal F,P)$, the random variable $X_{ij}\ge 0$ is the processing time (size) of job $j$ on machine $i$. An **assignment** is a map $\sigma:[n]\to[m]$; it puts the set $J_i=\{j:\sigma(j)=i\}$ of jobs on machine $i$.
--
--   1. **Load and makespan.** The load of machine $i$ is $\sum_{j\in J_i}X_{ij}$, the makespan is $\max_{i\in[m]}\sum_{j\in J_i}X_{ij}$, and the **expected makespan** of $\sigma$ is
--   $$\mathbb E\Big[\max_{i\in[m]}\sum_{j\in J_i}X_{ij}\Big].$$
--   2. **Scaling.** For $M>0$, the scaled instance has sizes $X_{ij}/M$.
--   3. **Truncated and exceptional parts** (§2.1). For a size $x$,
--   $$x' := x\cdot\mathbf 1(x\le 1)\quad\text{(truncated part)},\qquad x'' := x\cdot\mathbf 1(x>1)\quad\text{(exceptional part)},$$
--   applied pointwise to $X_{ij}$, so $X_{ij}=X'_{ij}+X''_{ij}$.
--   4. **Effective size** (Definition 1). For a random variable $Y$ and an integer $k\ge 2$,
--   $$\beta_k(Y) := \frac{1}{\log k}\,\log \mathbb E\big[e^{(\log k)\,Y}\big],$$
--   and $\beta_1(Y) := \mathbb E[Y]$. Here $\log$ is the natural logarithm.
--
--   The effective size $\beta_k$ is the deterministic surrogate for a truncated size that the LP and the rounding of the paper work with; the parameter $k$ is the number of machines among which a load must be balanced.
--
--   **Formalization Note** Machines are `Fin m`, jobs `Fin n` (0-based), and the makespan is the supremum `⨆ i : Fin m` of the loads, which is their maximum when $m\ge1$ (every theorem assumes $m\ge1$). Expectations are Bochner integrals; the theorems assume each $X_{ij}$ measurable, nonnegative and integrable, so no integral takes the junk value $0$. The value $\beta_0$ is a junk value ($0$) and is never used.
-- source:
--   Gupta, Kumar, Nagarajan & Shen, Stochastic Load Balancing on Unrelated Machines, arXiv:1904.07271v1, pp. 4–6, §2 (model, scaling p. 5), §2.1 and Definition 1 (eq. (2))

import Mathlib

namespace StochLoadBal.Makespan

open MeasureTheory

/-- The **truncated part** `x' := x · 1(x ≤ 1)` of a size (§2.1, p. 5). -/
noncomputable def trunc (x : ℝ) : ℝ := if x ≤ 1 then x else 0

/-- The **exceptional part** `x'' := x · 1(x > 1)` of a size (§2.1, p. 5). -/
noncomputable def exc (x : ℝ) : ℝ := if 1 < x then x else 0

/-- Scaling every size down by the factor `M` (p. 5, "scaling down all random variables by
factor M"): `(X / M)_{ij} = X_{ij} / M`. -/
noncomputable def scale {m n : ℕ} {Ω : Type*} (M : ℝ) (X : Fin m → Fin n → Ω → ℝ) :
    Fin m → Fin n → Ω → ℝ :=
  fun i j ω => X i j ω / M

/-- The load `Σ_{j ∈ J_i} X_{ij}(ω)` of machine `i` under the assignment `σ`, where
`J_i = {j | σ j = i}`. -/
noncomputable def load {m n : ℕ} {Ω : Type*} (X : Fin m → Fin n → Ω → ℝ) (σ : Fin n → Fin m)
    (i : Fin m) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => σ j = i), X i j ω

/-- The makespan `max_{i ∈ [m]} Σ_{j ∈ J_i} X_{ij}(ω)` of the assignment `σ` at outcome `ω`
(the supremum over the finite index set `Fin m`; it is the maximum when `m ≥ 1`). -/
noncomputable def makespan {m n : ℕ} {Ω : Type*} (X : Fin m → Fin n → Ω → ℝ)
    (σ : Fin n → Fin m) (ω : Ω) : ℝ :=
  ⨆ i : Fin m, load X σ i ω

/-- The **expected makespan** `E[max_{i ∈ [m]} Σ_{j ∈ J_i} X_{ij}]` of the assignment `σ`
(§2, p. 4). -/
noncomputable def expMakespan {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Fin m → Fin n → Ω → ℝ) (σ : Fin n → Fin m) : ℝ :=
  ∫ ω, makespan X σ ω ∂P

/-- The **effective size** (Definition 1, p. 6): for an integer `k ≥ 2`,
`β_k(Y) = (1 / log k) · log E[e^{(log k) Y}]`, and `β_1(Y) = E[Y]`.
(Junk value: `β_0(Y) = 0`, since `Real.log 0 = 0` and division by `0` is `0`; never used.) -/
noncomputable def effSize {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (k : ℕ)
    (Y : Ω → ℝ) : ℝ :=
  if k = 1 then ∫ ω, Y ω ∂P
  else Real.log (∫ ω, Real.exp (Real.log k * Y ω) ∂P) / Real.log k

end StochLoadBal.Makespan


