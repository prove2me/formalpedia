-- Prove2me | Definitions.Def_ChitourPrescribedTime_Linear_chain
-- name    : ChitourPrescribedTime_Linear_chain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:57:01.701987+00:00
-- url     : https://prove2.me/theorems/3cb51553-d987-45c6-a095-44adca186e9b
-- title:
--   The chain of integrators: Jordan block $J_n$, input vector $e_n$, dilation $D^{\mathbf r}_\mu$, weights $D_{\mathbf r}$
-- statement:
--   Let $n$ be a positive integer and let $(e_i)_{1\le i\le n}$ be the canonical basis of $\mathbb R^n$. This file fixes the linear-algebra objects of the perturbed chain of integrators
--   $$\dot x = J_n x + (d + b u)\, e_n .$$
--
--   1. The **$n$-th Jordan block** $J_n$ is the $n\times n$ real matrix with $J_n e_i = e_{i-1}$ for $1\le i\le n$, with the convention $e_0 = 0$. Its only nonzero entries are ones on the superdiagonal.
--   2. The **input vector** $e_n$ is the last canonical basis vector.
--   3. With the weights $r_i = n-i+1$, the **dilation** with parameter $\mu$ is the diagonal matrix
--   $$D^{\mathbf r}_\mu = \operatorname{diag}\big(\mu^{r_i}\big)_{i=1}^n = \operatorname{diag}(\mu^{n},\mu^{n-1},\dots,\mu).$$
--   For $\mu>0$ it satisfies $D^{\mathbf r}_\mu J_n (D^{\mathbf r}_\mu)^{-1} = \mu J_n$ and $D^{\mathbf r}_\mu e_n = \mu e_n$.
--   4. The **weight matrix** is $D_{\mathbf r} = \operatorname{diag}(r_i)_{1\le i\le n} = \operatorname{diag}(n, n-1, \dots, 1)$.
--   5. $\|v\| = \big(\sum_i v_i^2\big)^{1/2}$ is the Euclidean norm on $\mathbb R^n$.
--
--   These objects appear in every statement of the mission: $J_n$ and $e_n$ define the plant, and $D^{\mathbf r}_\mu$ and $D_{\mathbf r}$ define the time-varying change of coordinates and the feedback.
--
--   **Formalization Note** Vectors of $\mathbb R^n$ are functions `Fin n → ℝ`. The coordinate `i : Fin n` stands for the paper's index $i = $ `i.val + 1`, so the weight $r_i = n-i+1$ is `n - i.val` (no truncation, since `i.val < n`). The entry of `jordanBlock n` in row `i`, column `j` is $1$ exactly when `j.val = i.val + 1`. The Euclidean norm is written out as `eucNorm`, because the norm Mathlib puts on `Fin n → ℝ` is the sup norm. The definitions make sense for $n = 0$ (empty matrices); every theorem of the mission assumes $n \ge 1$.
-- source:
--   Chitour, Ushirobira, Bouhemou, Stabilization for a Perturbed Chain of Integrators in Prescribed Time, SIAM J. Control Optim. 58 (2020), p. 1022, eq. (1); p. 1026, §3, eq. (5); p. 1027, definition of D_r

import Mathlib

namespace ChitourPrescribedTime.Linear

/-- The `n`-th Jordan block `J_n` (Chitour–Ushirobira–Bouhemou 2020, §1 and §3, pp. 1022, 1026):
`J_n e_i = e_{i-1}` for `1 ≤ i ≤ n`, with `e_0 = 0`. Coordinates are `Fin n`; the paper's index
`i ∈ {1, …, n}` is `i.val + 1`. The entry in row `i`, column `j` is `1` exactly when
`j.val = i.val + 1` (the superdiagonal), so column `j` holds the basis vector of index `j - 1`. -/
def jordanBlock (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if (j : ℕ) = (i : ℕ) + 1 then 1 else 0

/-- The last canonical basis vector `e_n` of `ℝ^n` (the input direction of the chain of
integrators (1)); its only nonzero coordinate is the one with `i.val + 1 = n`. -/
def eN (n : ℕ) : Fin n → ℝ := fun i => if (i : ℕ) + 1 = n then 1 else 0

/-- The dilation `D^r_μ = diag(μ^{r_i})_{i=1}^n` with weights `r_i = n - i + 1` (§3, (5), p. 1026).
With the 0-based coordinate `i : Fin n` (paper index `i.val + 1`) the weight is `n - i.val`,
which is at least `1` since `i.val < n`. -/
noncomputable def dil (n : ℕ) (μ : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i : Fin n => μ ^ (n - (i : ℕ))

/-- The weight matrix `D_r = diag(r_i)_{1 ≤ i ≤ n}`, `r_i = n - i + 1` (§3, p. 1027). -/
noncomputable def Dr (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i : Fin n => ((n - (i : ℕ) : ℕ) : ℝ)

/-- The Euclidean norm `‖v‖ = (∑ᵢ vᵢ²)^{1/2}` of a vector of `ℝ^n` (the sup norm that Mathlib
puts on `Fin n → ℝ` is not the paper's norm). -/
noncomputable def eucNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

end ChitourPrescribedTime.Linear


