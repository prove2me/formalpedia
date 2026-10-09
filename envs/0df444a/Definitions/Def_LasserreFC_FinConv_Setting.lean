-- Prove2me | Definitions.Def_LasserreFC_FinConv_Setting
-- name    : LasserreFC_FinConv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:34.888634+00:00
-- url     : https://prove2.me/theorems/840acf9c-ea93-47dc-9ba3-1698cb204417
-- title:
--   (1.1)–(1.7), pp. 1–3 — the polynomial optimization problem, its feasible set and the classical optimality conditions
-- statement:
--   This file fixes the polynomial optimization problem and the classical optimality conditions of Nie's paper.
--
--   Let $n, m_1, m_2 \in \mathbb N$ and let $f, h_1, \dots, h_{m_1}, g_1, \dots, g_{m_2} \in \mathbb R[x]$ be real polynomials in $x = (x_1, \dots, x_n)$. Problem (1.1) is
--
--   $$\min\ f(x) \quad \text{s.t.}\quad h_i(x) = 0\ (i \in [m_1]),\qquad g_j(x) \ge 0\ (j \in [m_2]),$$
--
--   and $K = \{x \in \mathbb R^n : h(x) = 0,\ g(x) \ge 0\}$ is its feasible set; $m_1 = 0$ or $m_2 = 0$ is allowed. The real variety of the equality constraints is $V_{\mathbb R}(h) = \{x \in \mathbb R^n : h_1(x) = \dots = h_{m_1}(x) = 0\}$.
--
--   For a point $u$, the active set is $J(u) = \{j : g_j(u) = 0\}$. The following conditions are defined at $u$:
--
--   1. **Constraint qualification (CQC):** the gradients $\nabla h_1(u), \dots, \nabla h_{m_1}(u), \nabla g_j(u)$ ($j \in J(u)$) are linearly independent.
--   2. **(1.3)–(1.4):** multipliers $\lambda \in \mathbb R^{m_1}$, $\mu \in \mathbb R^{m_2}$ satisfy $\nabla f(u) = \sum_i \lambda_i \nabla h_i(u) + \sum_j \mu_j \nabla g_j(u)$, $\mu_j g_j(u) = 0$ and $\mu_j \ge 0$ for all $j$.
--   3. **Strict complementarity (SCC), (1.5):** $\mu_j + g_j(u) > 0$ for all $j$.
--   4. **Second order sufficiency (SOSC), (1.7):** with the Lagrange function $L(x) = f(x) - \sum_i \lambda_i h_i(x) - \sum_{j \in J(u)} \mu_j g_j(x)$,
--   $$v^T \nabla_x^2 L(u)\, v > 0 \quad \text{for all } 0 \ne v \in G(u)^\perp,$$
--   where $G(u)^\perp$ is the null space of the Jacobian of $h$ and of the active $g_j$ at $u$.
--
--   "The constraint qualification, strict complementarity and second order sufficiency conditions hold at $u$" means: CQC holds, and there are multipliers $\lambda, \mu$ satisfying (1.3), (1.4), (1.5) and (1.7) together.
--
--   These are the hypotheses of the paper's main finite-convergence theorem.
--
--   **Formalization Note** Polynomials are `MvPolynomial (Fin n) ℝ` and points are `Fin n → ℝ`; the paper's indices $1, \dots, m$ are `Fin m`. Gradients and Hessians are computed from formal partial derivatives (`MvPolynomial.pderiv`), which agree with the analytic ones for polynomials. CQC is linear independence of the indexed family (`Sum.elim`), so two equal gradients count as dependent. The multipliers of SCC and SOSC are the same ones that satisfy (1.3)–(1.4); under CQC they are unique.
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, pp. 1–3, (1.1), (1.3)–(1.5), (1.7); p. 4, §2.2 (V_ℝ(h))

import Mathlib

namespace LasserreFC.FinConv

open MvPolynomial Matrix

/-- Problem (1.1), p. 1: minimize `f` subject to `h i = 0` (`i : Fin m1`) and `g j ≥ 0` (`j : Fin m2`),
with polynomial data in `x ∈ ℝⁿ`. `m1 = 0` or `m2 = 0` is allowed. -/
structure POP (n m1 m2 : ℕ) where
  f : MvPolynomial (Fin n) ℝ
  h : Fin m1 → MvPolynomial (Fin n) ℝ
  g : Fin m2 → MvPolynomial (Fin n) ℝ

variable {n m1 m2 : ℕ}

/-- The feasible set `K` of (1.1). -/
def POP.K (P : POP n m1 m2) : Set (Fin n → ℝ) :=
  {x | (∀ i, eval x (P.h i) = 0) ∧ ∀ j, 0 ≤ eval x (P.g j)}

/-- The real variety `V_ℝ(h) = {x ∈ ℝⁿ : h₁(x) = ⋯ = h_{m₁}(x) = 0}` (§2.2, p. 4). -/
def realVariety (P : POP n m1 m2) : Set (Fin n → ℝ) :=
  {x | ∀ i, eval x (P.h i) = 0}

/-- The gradient `∇p(u)` of a polynomial, through formal partial derivatives. -/
noncomputable def grad (p : MvPolynomial (Fin n) ℝ) (u : Fin n → ℝ) : Fin n → ℝ :=
  fun k => eval u (pderiv k p)

/-- The Hessian `∇²p(u)` of a polynomial, through formal partial derivatives. -/
noncomputable def hess (p : MvPolynomial (Fin n) ℝ) (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun k s => eval u (pderiv k (pderiv s p))

/-- The constraint qualification condition (CQC), p. 2: the family
`∇h₁(u), …, ∇h_{m₁}(u), ∇g_j(u)` (`j ∈ J(u)`, the active inequality constraints) is linearly
independent (as an indexed family, so repeated gradients count as dependent). -/
def CQC (P : POP n m1 m2) (u : Fin n → ℝ) : Prop :=
  LinearIndependent ℝ (Sum.elim (fun i : Fin m1 => grad (P.h i) u)
    (fun j : {j : Fin m2 // eval u (P.g j) = 0} => grad (P.g j.1) u))

/-- Lagrange multipliers satisfying (1.3) (first order optimality condition) and (1.4)
(complementarity), p. 2. -/
def IsKKTMult (P : POP n m1 m2) (u : Fin n → ℝ) (lam : Fin m1 → ℝ) (mu : Fin m2 → ℝ) : Prop :=
  grad P.f u = ∑ i, lam i • grad (P.h i) u + ∑ j, mu j • grad (P.g j) u ∧
  (∀ j, mu j * eval u (P.g j) = 0) ∧ (∀ j, 0 ≤ mu j)

/-- The strict complementarity condition (SCC) (1.5), p. 2: `μ_j + g_j(u) > 0` for all `j`. -/
def SCC (P : POP n m1 m2) (u : Fin n → ℝ) (mu : Fin m2 → ℝ) : Prop :=
  ∀ j, 0 < mu j + eval u (P.g j)

/-- The Lagrange function of p. 3, `L(x) = f(x) − ∑ᵢ λᵢ hᵢ(x) − ∑_{j ∈ J(u)} μⱼ gⱼ(x)`. -/
noncomputable def lagr (P : POP n m1 m2) (u : Fin n → ℝ) (lam : Fin m1 → ℝ) (mu : Fin m2 → ℝ) :
    MvPolynomial (Fin n) ℝ :=
  P.f - ∑ i, C (lam i) * P.h i -
    ∑ j ∈ Finset.univ.filter (fun j => eval u (P.g j) = 0), C (mu j) * P.g j

/-- The second order sufficiency condition (SOSC) (1.7), p. 3: `vᵀ ∇²ₓL(u) v > 0` for every nonzero
`v` in the null space `G(u)^⊥` of the Jacobian of the equality and active inequality constraints. -/
def SOSC (P : POP n m1 m2) (u : Fin n → ℝ) (lam : Fin m1 → ℝ) (mu : Fin m2 → ℝ) : Prop :=
  ∀ v : Fin n → ℝ, v ≠ 0 → (∀ i, grad (P.h i) u ⬝ᵥ v = 0) →
    (∀ j, eval u (P.g j) = 0 → grad (P.g j) u ⬝ᵥ v = 0) →
    0 < v ⬝ᵥ (hess (lagr P u lam mu) u *ᵥ v)

/-- "The constraint qualification, strict complementarity and second order sufficiency conditions hold
at `u`": CQC, together with multipliers satisfying (1.3), (1.4), (1.5) and (1.7). -/
def OptCond (P : POP n m1 m2) (u : Fin n → ℝ) : Prop :=
  CQC P u ∧ ∃ (lam : Fin m1 → ℝ) (mu : Fin m2 → ℝ),
    IsKKTMult P u lam mu ∧ SCC P u mu ∧ SOSC P u lam mu

end LasserreFC.FinConv


