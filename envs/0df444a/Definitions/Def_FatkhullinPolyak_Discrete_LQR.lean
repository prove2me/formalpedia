-- Prove2me | Definitions.Def_FatkhullinPolyak_Discrete_LQR
-- name    : FatkhullinPolyak_Discrete_LQR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:34:59.767342+00:00
-- url     : https://prove2.me/theorems/d91366c5-c5e1-4fea-8ea6-12dcc18885be
-- title:
--   Static output-feedback LQR: stabilizing set $\mathcal S$, $X(K)$, $Y(K)$, cost $f(K)=\mathrm{Tr}(X(K)\Sigma)$, gradient formula (3.3), sublevel set $\mathcal S_0$, gradient-method iterates (4.4)
-- statement:
--   The objects of the static output-feedback linear-quadratic regulator (LQR) problem of Fatkhullin and Polyak, and the gradient method for it.
--
--   Fix $A\in\mathbb R^{n\times n}$, $B\in\mathbb R^{n\times m}$, $C\in\mathbb R^{r\times n}$, weights $Q\in\mathbb R^{n\times n}$, $R\in\mathbb R^{m\times m}$ and an initial-state covariance $\Sigma\in\mathbb R^{n\times n}$. A gain is a matrix $K\in\mathbb R^{m\times r}$; the closed-loop matrix is $A_K=A-BKC$.
--
--   1. The **set of stabilizing gains** is $\mathcal S=\{K\in\mathbb R^{m\times r}: A_K\text{ is Hurwitz}\}$.
--   2. $X(K)$ is the solution of the Lyapunov equation (2.7)
--   $$A_K^\top X + X A_K + C^\top K^\top R K C + Q = 0,$$
--   and $Y(K)$ is the solution of (3.4)
--   $$A_K Y + Y A_K^\top + \Sigma = 0 .$$
--   3. The **LQR cost** (2.6) is $f(K)=\mathrm{Tr}\big(X(K)\Sigma\big)$.
--   4. The **gradient formula** (3.3) is
--   $$\nabla f(K) = 2\big(RKC - B^\top X(K)\big)\,Y(K)\,C^\top .$$
--   5. For a gain $K_0$, the **sublevel set** is $\mathcal S_0=\{K\in\mathcal S: f(K)\le f(K_0)\}$.
--   6. Given a step sequence $(\gamma_j)_{j\ge0}$, the **gradient method** (4.4) is
--   $$K_{j+1}=K_j-\gamma_j\nabla f(K_j),$$
--   started from the known stabilizing gain $K_0$.
--
--   These are the data of every theorem of the mission. State feedback (SLQR) is the case $r=n$, $C=I$, where the paper writes $f_S$ for $f$.
--
--   **Formalization Note** $X(K)$ and $Y(K)$ are the Lyapunov solutions of the toolkit definition (unique solution, $0$ if the solution is not unique). For $K\in\mathcal S$ the Lyapunov operator is invertible, so they are the paper's $X(K)\succ0$ and $Y(K)$. Off $\mathcal S$ the value is a placeholder that no statement relies on: every theorem evaluates $f$ and $\nabla f$ only at gains that are in $\mathcal S$ by hypothesis or by conclusion (in particular the iterates are proved, not assumed, to stay in $\mathcal S_0$). $\nabla f$ is the formula (3.3); that it is the gradient of $f$ is Lemma 3.11. The set-builder for $\mathcal S$ on p. 3 writes $\mathbb R^{m\times n}$, a misprint for $\mathbb R^{m\times r}$ (the gain is $m\times r$ two lines earlier).
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 3 ((2.3), definitions of S and S₀), p. 4 (Problem 2.2, (2.6)–(2.7)), p. 7 (Lemma 3.11, (3.3)–(3.4)), p. 10 ((4.4))

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_Matrix

namespace FatkhullinPolyak.Discrete

/-- The set `S` of stabilizing static output-feedback gains `K ∈ ℝ^{m×r}`: those for which the
closed-loop matrix `A_K = A − BKC` is Hurwitz (p. 3). -/
def stabSet {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) : Set (Matrix (Fin m) (Fin r) ℝ) :=
  {K | IsHurwitz (A - B * K * C)}

/-- `X(K)`: the solution of the Lyapunov equation (2.7),
`(A − BKC)ᵀ X + X (A − BKC) + CᵀKᵀRKC + Q = 0` (p. 4). Unique for `K ∈ S`. -/
noncomputable def lyapX {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (K : Matrix (Fin m) (Fin r) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  lyapSol (A - B * K * C) (C.transpose * K.transpose * R * K * C + Q)

/-- `Y(K)`: the solution of the Lyapunov equation (3.4), `A_K Y + Y A_Kᵀ + Σ = 0` with
`A_K = A − BKC` (p. 7). Unique for `K ∈ S`. -/
noncomputable def lyapY {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (K : Matrix (Fin m) (Fin r) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  lyapSol (A - B * K * C).transpose Sig

/-- The LQR cost `f(K) = Tr(X(K) Σ)` of Problem 2.2, (2.6) (p. 4). Meaningful for `K ∈ S`. -/
noncomputable def lqrCost {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin m) (Fin r) ℝ) : ℝ :=
  Matrix.trace (lyapX A B C Q R K * Sig)

/-- The gradient formula (3.3): `∇f(K) = 2 (RKC − Bᵀ X(K)) Y(K) Cᵀ` (p. 7). Lemma 3.11 is the
theorem that this is the gradient of `f` on `S`. -/
noncomputable def lqrGrad {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin m) (Fin r) ℝ) : Matrix (Fin m) (Fin r) ℝ :=
  (2 : ℝ) • ((R * K * C - B.transpose * lyapX A B C Q R K) * lyapY A B C Sig K * C.transpose)

/-- The sublevel set `S₀ = {K ∈ S : f(K) ≤ f(K₀)}` (p. 3). -/
def sublevel {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (K₀ : Matrix (Fin m) (Fin r) ℝ) :
    Set (Matrix (Fin m) (Fin r) ℝ) :=
  {K | K ∈ stabSet A B C ∧ lqrCost A B C Q R Sig K ≤ lqrCost A B C Q R Sig K₀}

/-- The iterates of the gradient method (4.4), `K_{j+1} = K_j − γ_j ∇f(K_j)`, started at the
known stabilizing gain `K₀` (p. 10), with step sequence `γ`. -/
noncomputable def gradIter {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (K₀ : Matrix (Fin m) (Fin r) ℝ) (γ : ℕ → ℝ) :
    ℕ → Matrix (Fin m) (Fin r) ℝ
  | 0 => K₀
  | j + 1 => gradIter A B C Q R Sig K₀ γ j - γ j • lqrGrad A B C Q R Sig (gradIter A B C Q R Sig K₀ γ j)

end FatkhullinPolyak.Discrete


