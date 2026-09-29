-- Prove2me | Definitions.Def_FatkhullinPolyak_Flow_LQR
-- name    : FatkhullinPolyak_Flow_LQR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:43:03.852862+00:00
-- url     : https://prove2.me/theorems/f07d1f10-3600-4074-b792-f72fe8e76608
-- title:
--   Static output-feedback LQR: stabilizing set $\mathcal S$, Lyapunov solutions $X(K)$, $Y(K)$, cost $f(K)=\mathrm{Tr}(X(K)\Sigma)$, sublevel set $\mathcal S_0$, gradient formula (3.3)
-- statement:
--   The objects of the static output-feedback linear-quadratic regulator (LQR) problem of Fatkhullin and Polyak.
--
--   Fix dimensions $n, m, r$ and real matrices $A\in\mathbb R^{n\times n}$, $B\in\mathbb R^{n\times m}$, $C\in\mathbb R^{r\times n}$, weights $Q\in\mathbb R^{n\times n}$, $R\in\mathbb R^{m\times m}$ and an initial-state covariance $\Sigma\in\mathbb R^{n\times n}$. A gain is a matrix $K\in\mathbb R^{m\times r}$.
--
--   1. A square real matrix $M$ is **Hurwitz** if every complex eigenvalue $z$ of $M$ satisfies $\Re z<0$.
--   2. The **closed-loop matrix** is $A_K = A - BKC$, and the **set of stabilizing gains** is
--   $$\mathcal S = \{K\in\mathbb R^{m\times r} : A_K \text{ is Hurwitz}\}.$$
--   3. $X(K)$ is the solution $X$ of the Lyapunov equation (2.7)
--   $$A_K^\top X + X A_K + C^\top K^\top R K C + Q = 0,$$
--   and $Y(K)$ is the solution $Y$ of the Lyapunov equation (3.4)
--   $$A_K Y + Y A_K^\top + \Sigma = 0.$$
--   For $K\in\mathcal S$ both equations have exactly one solution.
--   4. The **LQR cost** (2.6) is $f(K) = \mathrm{Tr}(X(K)\Sigma)$, and for a gain $K_0$ the **sublevel set** is
--   $$\mathcal S_0 = \{K\in\mathcal S : f(K)\le f(K_0)\}.$$
--   5. The **gradient formula** (3.3) is
--   $$\nabla f(K) = 2\,(RKC - B^\top X(K))\,Y(K)\,C^\top,$$
--   and $\|M\|_F=\big(\sum_{i,j}M_{ij}^2\big)^{1/2}$ is the Frobenius norm.
--
--   These are the data of every statement of this mission: the gradient flow runs in $\mathcal S$, decreases $f$, and stays in $\mathcal S_0$.
--
--   **Formalization Note** $X(K)$ and $Y(K)$ are defined as "the unique solution if the equation has exactly one solution, and the zero matrix otherwise". For $K\in\mathcal S$ the Lyapunov operator is invertible, so this is the paper's $X(K)$ (which is then positive definite when $Q\succ0$) and $Y(K)$. The zero value off $\mathcal S$ is a placeholder that no statement of the mission relies on: every statement evaluates $f$ and $\nabla f$ only at gains that are in $\mathcal S$ by hypothesis or by conclusion. $\nabla f$ is defined by the formula (3.3); that it is the gradient of $f$ is Lemma 3.11. The set-builder for $\mathcal S$ on p. 3 writes $\mathbb R^{m\times n}$; the gain is $m\times r$ (p. 3, two lines earlier), which is what is used here.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 3, (2.3) and the definitions of S and S₀; p. 4, Problem 2.2, (2.6)–(2.7); p. 7, Lemma 3.11, (3.3)–(3.4)

import Mathlib

namespace FatkhullinPolyak.Flow

open Matrix

/-- A real square matrix is Hurwitz if every complex eigenvalue has negative real part. -/
def IsHurwitz {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∀ z ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)), z.re < 0

/-- The closed-loop matrix `A_K = A - B K C` of (2.3). -/
def closedLoop {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (K : Matrix (Fin m) (Fin r) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  A - B * K * C

/-- The set `S` of stabilizing static output-feedback gains `K ∈ ℝ^{m×r}` (p. 3). -/
def stabSet {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) : Set (Matrix (Fin m) (Fin r) ℝ) :=
  {K | IsHurwitz (closedLoop A B C K)}

open Classical in
/-- `X(K)`: the unique solution `X` of the Lyapunov equation (2.7)
`A_Kᵀ X + X A_K + Cᵀ Kᵀ R K C + Q = 0`. When the solution is not unique (possible only for
`K ∉ S`) the junk value `0` is returned. -/
noncomputable def lyapX {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (K : Matrix (Fin m) (Fin r) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  if h : ∃! X : Matrix (Fin n) (Fin n) ℝ,
      (closedLoop A B C K)ᵀ * X + X * closedLoop A B C K + Cᵀ * Kᵀ * R * K * C + Q = 0
  then h.exists.choose else 0

open Classical in
/-- `Y(K)`: the unique solution `Y` of the Lyapunov equation (3.4)
`A_K Y + Y A_Kᵀ + Σ = 0`; junk value `0` when the solution is not unique. -/
noncomputable def lyapY {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (K : Matrix (Fin m) (Fin r) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  if h : ∃! Y : Matrix (Fin n) (Fin n) ℝ,
      closedLoop A B C K * Y + Y * (closedLoop A B C K)ᵀ + Sig = 0
  then h.exists.choose else 0

/-- The LQR cost `f(K) = Tr(X(K) Σ)` of Problem 2.2, (2.6). -/
noncomputable def cost {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin m) (Fin r) ℝ) : ℝ :=
  trace (lyapX A B C Q R K * Sig)

/-- The sublevel set `S₀ = {K ∈ S : f(K) ≤ f(K₀)}` (p. 3). -/
def sublevel {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (K₀ : Matrix (Fin m) (Fin r) ℝ) :
    Set (Matrix (Fin m) (Fin r) ℝ) :=
  {K | K ∈ stabSet A B C ∧ cost A B C Q R Sig K ≤ cost A B C Q R Sig K₀}

/-- The gradient formula (3.3): `∇f(K) = 2 (R K C - Bᵀ X(K)) Y(K) Cᵀ`. -/
noncomputable def grad {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin m) (Fin r) ℝ) : Matrix (Fin m) (Fin r) ℝ :=
  (2 : ℝ) • ((R * K * C - Bᵀ * lyapX A B C Q R K) * lyapY A B C Sig K * Cᵀ)

/-- The Frobenius norm `‖M‖_F = √(∑ᵢⱼ Mᵢⱼ²)`. -/
noncomputable def frobNorm {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, M i j ^ 2)

end FatkhullinPolyak.Flow


