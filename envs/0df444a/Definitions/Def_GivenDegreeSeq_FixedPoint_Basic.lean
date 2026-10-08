-- Prove2me | Definitions.Def_GivenDegreeSeq_FixedPoint_Basic
-- name    : GivenDegreeSeq_FixedPoint_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:50:55.276439+00:00
-- url     : https://prove2.me/theorems/b6b1e0f6-343f-4de9-8b05-97c41ed22cb9
-- title:
--   The $\beta$-model ML equations (3), the maps $r_{ij}$ and $\varphi$ of (4)–(5), $\partial\varphi_i/\partial x_j$ and the matrix $J(x,y)$
-- statement:
--   Fix $n$ vertices $1,\dots,n$ and a vector $\beta=(\beta_1,\dots,\beta_n)\in\mathbb R^n$. In the **$\beta$-model** an edge between distinct vertices $i$ and $j$ is present with probability
--   $$p_{ij}(\beta)=\frac{e^{\beta_i+\beta_j}}{1+e^{\beta_i+\beta_j}}.$$
--
--   1. Given numbers $d_1,\dots,d_n$ (the degrees of an observed graph), the **maximum likelihood (ML) equations** (3) for $\hat\beta\in\mathbb R^n$ are
--   $$d_i=\sum_{j\ne i}\frac{e^{\hat\beta_i+\hat\beta_j}}{1+e^{\hat\beta_i+\hat\beta_j}},\qquad i=1,\dots,n.$$
--   2. For $1\le i\ne j\le n$ and $x\in\mathbb R^n$, eq. (4) sets
--   $$r_{ij}(x):=\frac{1}{e^{-x_j}+e^{x_i}}.$$
--   3. Eq. (5) defines $\varphi:\mathbb R^n\to\mathbb R^n$ componentwise by
--   $$\varphi_i(x):=\log d_i-\log\sum_{j\ne i}r_{ij}(x).$$
--   4. $\partial\varphi_i/\partial x_j(x)$ denotes the partial derivative of $\varphi_i$ in the $j$-th coordinate at $x$.
--   5. For $x,y\in\mathbb R^n$, $J(x,y)$ is the $n\times n$ matrix with entries
--   $$J_{ij}(x,y)=\int_0^1\frac{\partial\varphi_i}{\partial x_j}(tx+(1-t)y)\,dt.$$
--
--   The fixed points of $\varphi$ are the solutions of (3), and iterating $\varphi$ is the paper's algorithm for computing the MLE; $J(x,y)$ is the averaged Jacobian through which the contraction properties of $\varphi$ are expressed.
--
--   **Formalization Note** Vertices are `Fin n` $=\{0,\dots,n-1\}$ and vectors are `Fin n → ℝ`; Mathlib's norm on this type is the sup norm $|x|_\infty$. The degrees $d$ are real numbers; every statement about $\varphi$ assumes $d_i>0$ (otherwise $\log d_i$ is Lean's junk value $\log 0=0$). The partial derivative is the Fréchet derivative of $y\mapsto\varphi_i(y)$ applied to the $j$-th unit vector ($\varphi$ is smooth). The integral is the interval integral over $[0,1]$.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 6 (β-model), p. 7 Eq. (3), p. 8 Eqs. (4)–(5), p. 12 (∂φ_i/∂x_j and J(x,y))

import Mathlib

namespace GivenDegreeSeq.FixedPoint

/-! Chatterjee, Diaconis & Sly, *Random Graphs with a Given Degree Sequence*,
arXiv:1005.1136v5: the β-model edge probability (p. 6), the maximum likelihood equations (3)
(p. 7), the functions `r_ij` and `φ` of (4)–(5) (p. 8), the partial derivatives `∂φ_i/∂x_j`
and the matrix `J(x, y)` of p. 12.

Vertices `1, …, n` of the paper are `Fin n = {0, …, n − 1}`; vectors of `ℝⁿ` are
`Fin n → ℝ`, whose Mathlib norm is the sup norm `|x|∞ = max_i |x_i|`. -/

/-- β-model edge probability `p_ij(β) = e^{β_i+β_j}/(1 + e^{β_i+β_j})` (p. 6). -/
noncomputable def edgeProb {n : ℕ} (β : Fin n → ℝ) (i j : Fin n) : ℝ :=
  Real.exp (β i + β j) / (1 + Real.exp (β i + β j))

/-- The maximum likelihood equations (3) (p. 7) for the degree vector `d` at `b`:
`d_i = Σ_{j ≠ i} e^{b_i+b_j}/(1 + e^{b_i+b_j})` for every `i`. -/
def MLEq {n : ℕ} (d b : Fin n → ℝ) : Prop :=
  ∀ i, d i = ∑ j ∈ Finset.univ.erase i, edgeProb b i j

/-- `r_ij(x) = 1/(e^{−x_j} + e^{x_i})`, eq. (4) (p. 8). -/
noncomputable def r {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) : ℝ :=
  1 / (Real.exp (-x j) + Real.exp (x i))

/-- The map `φ : ℝⁿ → ℝⁿ` with `φ_i(x) = log d_i − log Σ_{j ≠ i} r_ij(x)`, eq. (5) (p. 8),
for a degree vector `d` (every statement about `φ` assumes `d_i > 0`). -/
noncomputable def phi {n : ℕ} (d : Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.log (d i) - Real.log (∑ j ∈ Finset.univ.erase i, r x i j)

/-- The partial derivative `∂φ_i/∂x_j` at `x` (p. 12): the Fréchet derivative of
`y ↦ φ_i(y)` at `x` applied to the `j`-th standard basis vector. -/
noncomputable def partialPhi {n : ℕ} (d : Fin n → ℝ) (x : Fin n → ℝ) (i j : Fin n) : ℝ :=
  fderiv ℝ (fun y => phi d y i) x (Pi.single j 1)

/-- The matrix `J(x, y)` of p. 12 with entries
`J_ij(x, y) = ∫₀¹ ∂φ_i/∂x_j (t x + (1 − t) y) dt`. -/
noncomputable def J {n : ℕ} (d x y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ t in (0 : ℝ)..1, partialPhi d (t • x + (1 - t) • y) i j

end GivenDegreeSeq.FixedPoint


