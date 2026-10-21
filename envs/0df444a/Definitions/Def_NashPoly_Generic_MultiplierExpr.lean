-- Prove2me | Definitions.Def_NashPoly_Generic_MultiplierExpr
-- name    : NashPoly_Generic_MultiplierExpr
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:14.409582+00:00
-- url     : https://prove2.me/theorems/7f390d5a-449b-4c06-ac05-5a2ad4d5a0c9
-- title:
--   (3.1)–(3.3), (3.6), (3.7), (3.10), pp. 7–9 — the matrix G_i, Lagrange multiplier expressions, the set G and the feasible set of (3.10)
-- statement:
--   This file defines the polynomial Lagrange multiplier expressions of §3.1 and the optimization problems (3.7) and (3.10) of §3.2 for a NEPP $(f_i, g_{i,j}, E_i)$.
--
--   **The matrix $G_i$** (3.1). For a tuple $g=(g_1,\dots,g_m)$ of polynomials in $z\in\mathbb R^{n'}$, $G(z)$ is the $(n'+m)\times m$ polynomial matrix whose $j$-th column is $\nabla g_j(z)$ stacked on top of $g_j(z)e_j$:
--   $$G(z)=\begin{bmatrix}\nabla g_1(z)&\cdots&\nabla g_m(z)\\ \operatorname{diag}(g_1(z),\dots,g_m(z))\end{bmatrix}.$$
--   For player $i$, $G_i=G$ built from $g_i=(g_{i,1},\dots,g_{i,m_i})$, and $\hat f_i(x)=(\nabla_{x_i}f_i(x),0,\dots,0)\in\mathbb R^{n_i+m_i}$.
--
--   **Multiplier expressions** (3.2)–(3.3). Given matrix polynomials $H_i(x_i)$ of size $m_i\times(n_i+m_i)$, set
--   $$\lambda_{i,j}(x)=\bigl(H_i(x_i)\hat f_i(x)\bigr)_j .$$
--   When $H_i G_i=I_{m_i}$, these are the polynomial expressions of the Lagrange multipliers.
--
--   **The set $G$** (3.6), (3.7). $G$ is the set of $x\in\mathbb R^n$ such that for every player $i$
--   $$\nabla_{x_i}f_i(x)-\sum_{j=1}^{m_i}\lambda_{i,j}(x)\nabla_{x_i}g_{i,j}(x_i)=0,\quad g_{i,j}(x_i)=0\ (j\in E_i),$$
--   $$\lambda_{i,j}(x)g_{i,j}(x_i)=0,\quad g_{i,j}(x_i)\ge0,\quad \lambda_{i,j}(x)\ge0\quad (j\in I_i).$$
--
--   **The feasible set of (3.10).** For cut sets $K_i\subseteq\mathbb R^{n_i}$, $\mathrm{Feas}(K)$ is the set of $x\in G$ with $f_i(v,x_{-i})-f_i(x_i,x_{-i})\ge 0$ for all $v\in K_i$ and all $i$.
--
--   **The objective.** For an $(n+1)\times(n+1)$ matrix $\Theta$ and $[x]_1=(1,x_1,\dots,x_n)$, $\theta(x)=[x]_1^T\Theta[x]_1$; (3.7) and (3.10) minimize $\theta$ over $G$ and $\mathrm{Feas}(K)$.
--
--   These are the objects Algorithm 3.1 and Theorems 3.2–3.3 are about.
--
--   **Formalization Note** $H_i$ is data: a matrix with entries in $\mathbb R[x_i]$, rows indexed by $[m_i]$ and columns by $[n_i]\sqcup[m_i]$ (gradient rows first). $[x]_1$ is indexed by $\mathrm{Option}$ of the joint index type, with the extra index carrying the constant $1$. No property of $H_i$ or $\Theta$ is assumed in the definitions; the theorems assume $H_iG_i=I$ as an identity of polynomial matrices and $\Theta$ positive definite.
-- source:
--   Nie & Tang, Nash Equilibrium Problems of Polynomials, arXiv:2006.09490v2, pp. 7–8, (3.1)–(3.3), (3.6); p. 9, (3.7), (3.10)

import Mathlib
import Definitions.Def_NashPoly_Generic_NEP

namespace NashPoly.Generic

open MvPolynomial Matrix

/-- The polynomial matrix `G_i(x_i)` of (3.1), p. 7, for a constraining tuple
`g = (g_1, …, g_m)` in `ℝ[z]`, `z ∈ ℝ^{n'}`: an `(n' + m) × m` matrix whose column `j` is
`∇ g_j(z)` on top (rows `Sum.inl k`) and `g_j(z) e_j` below (rows `Sum.inr j'`). -/
noncomputable def Gmat {n' m' : ℕ} (g : Fin m' → MvPolynomial (Fin n') ℝ) :
    Matrix (Fin n' ⊕ Fin m') (Fin m') (MvPolynomial (Fin n') ℝ) :=
  Matrix.of fun r j => Sum.elim (fun k => pderiv k (g j)) (fun j' => if j' = j then g j else 0) r

variable {N : ℕ} {n m : Fin N → ℕ}

namespace NEP

variable (P : NEP N n m)

/-- `f̂_i(x) = (∇_{x_i} f_i(x), 0, …, 0) ∈ ℝ^{n_i + m_i}`, (3.1), p. 7. -/
noncomputable def fhat (i : Fin N) (x : Var n → ℝ) : Fin (n i) ⊕ Fin (m i) → ℝ :=
  Sum.elim (P.gradf i x) 0

/-- The Lagrange multiplier expression (3.3), p. 8: `λ_{i,j}(x) = (H_i(x_i) f̂_i(x))_j`, for a
matrix polynomial `H_i(x_i)` (`m_i × (n_i + m_i)`, entries in `ℝ[x_i]`). -/
noncomputable def lam
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ))
    (i : Fin N) (x : Var n → ℝ) (j : Fin (m i)) : ℝ :=
  ∑ r, eval (blk x i) (H i j r) * P.fhat i x r

/-- The set `G` of points satisfying the polynomial system (3.6), p. 8 (the feasible set of
(3.7), p. 9), for the multiplier expressions built from `H`. -/
def GSet
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ)) :
    Set (Var n → ℝ) :=
  {x | ∀ i,
    (∀ k, P.gradf i x k - ∑ j, P.lam H i x j * P.gradg i j x k = 0) ∧
    (∀ j ∈ P.E i, eval (blk x i) (P.g i j) = 0) ∧
    (∀ j ∉ P.E i, P.lam H i x j * eval (blk x i) (P.g i j) = 0) ∧
    (∀ j ∉ P.E i, 0 ≤ eval (blk x i) (P.g i j)) ∧
    (∀ j ∉ P.E i, 0 ≤ P.lam H i x j)}

/-- The feasible set of (3.10), p. 9: the points of `G` satisfying the cuts
`f_i(v, x_{-i}) − f_i(x_i, x_{-i}) ≥ 0` for every `v ∈ K_i` and every player `i`. -/
def Feas
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ))
    (K : (i : Fin N) → Set (Fin (n i) → ℝ)) : Set (Var n → ℝ) :=
  P.GSet H ∩ {x | ∀ i, ∀ v ∈ K i, eval x (P.f i) ≤ eval (repl x i v) (P.f i)}

end NEP

/-- `[x]_1 = (1, x_1, …, x_n)` (p. 9), indexed by `Option (Var n)` with `none ↦ 1`. -/
def xbar1 (x : Var n → ℝ) : Option (Var n) → ℝ := fun o => Option.elim o 1 x

/-- The objective `[x]_1^T Θ [x]_1` of (3.7) and (3.10), p. 9. -/
def theta (Θ : Matrix (Option (Var n)) (Option (Var n)) ℝ) (x : Var n → ℝ) : ℝ :=
  xbar1 x ⬝ᵥ Θ *ᵥ xbar1 x

end NashPoly.Generic


