-- Prove2me | Definitions.Def_NashPoly_Generic_NEP
-- name    : NashPoly_Generic_NEP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:32.746985+00:00
-- url     : https://prove2.me/theorems/a1dc7b09-25ba-470b-adfc-4e2cfa5d8929
-- title:
--   (1.1)–(1.3), (2.5), pp. 1–2, 6 — Nash equilibrium problems of polynomials, feasible sets, Nash equilibria and KKT points
-- statement:
--   This file fixes the Nash equilibrium problem of polynomials (NEPP) of Nie and Tang.
--
--   **Players and strategies.** There are $N$ players. Player $i$ chooses a strategy $x_i=(x_{i,1},\dots,x_{i,n_i})\in\mathbb R^{n_i}$, and $x=(x_1,\dots,x_N)\in\mathbb R^n$, $n=n_1+\dots+n_N$, is the joint strategy. For a joint strategy $x$ and $v\in\mathbb R^{n_i}$, $(v,x_{-i})$ denotes the joint strategy in which player $i$'s block is replaced by $v$ and all other blocks are kept.
--
--   **Player $i$'s problem** (1.1). Given $x_{-i}$, player $i$ solves
--   $$F_i(x_{-i}):\quad \min_{x_i\in\mathbb R^{n_i}} f_i(x_i,x_{-i})\quad\text{s.t.}\quad g_{i,j}(x_i)=0\ (j\in E_i),\qquad g_{i,j}(x_i)\ge 0\ (j\in I_i),$$
--   where $f_i\in\mathbb R[x]$ is a polynomial in the joint strategy, $g_{i,1},\dots,g_{i,m_i}\in\mathbb R[x_i]$ are polynomials in player $i$'s own strategy, and $E_i, I_i$ are disjoint label sets with $E_i\cup I_i=[m_i]$ (either may be empty). The feasible set (1.2) is $X_i=\{x_i: g_{i,j}(x_i)=0\ (j\in E_i),\ g_{i,j}(x_i)\ge 0\ (j\in I_i)\}$, and $x$ is feasible if $x\in X=X_1\times\dots\times X_N$.
--
--   **Nash equilibria** (1.3). A joint strategy $x^*$ is a Nash equilibrium (NE) if each $x^*_i$ is a global minimizer of $F_i(x^*_{-i})$:
--   $$x^*\in X\quad\text{and}\quad f_i(x^*)\le f_i(v,x^*_{-i})\quad\text{for all } i\in[N],\ v\in X_i .$$
--   $G^*$ denotes the set of all NEs.
--
--   **KKT points** (2.5). A point $x$ is a KKT point if $x\in X$ and there are multipliers $\lambda_{i,j}\in\mathbb R$ with
--   $$\sum_{j=1}^{m_i}\lambda_{i,j}\nabla_{x_i}g_{i,j}(x_i)=\nabla_{x_i}f_i(x),\qquad 0\le\lambda_{i,j}\perp g_{i,j}(x_i)\ge 0\ (j\in I_i)$$
--   for every player $i$, where $\nabla_{x_i}$ is the gradient with respect to $x_i$ and $\lambda\perp g$ means $\lambda g=0$.
--
--   These objects are the setting of every statement of the mission.
--
--   **Formalization Note** The joint strategy is a function on the index type $\Sigma_i\,\mathrm{Fin}(n_i)$ (pairs $(i,k)$); players and constraints are indexed from $0$. $I_i$ is the complement of the finset $E_i$. Gradients are formal partial derivatives of the polynomials, which agree with the analytic ones. Feasibility $x\in X$ (in particular $g_{i,j}(x_i)=0$ for $j\in E_i$) is part of the KKT condition: display (2.5) omits it, but the paper calls (2.5) "the KKT condition for the optimization $F_i(x_{-i})$".
-- source:
--   Nie & Tang, Nash Equilibrium Problems of Polynomials, arXiv:2006.09490v2, pp. 1–2, (1.1)–(1.3); p. 6, §2.3, (2.5)

import Mathlib

namespace NashPoly.Generic

open MvPolynomial

/-- The joint strategy index `V = Σ i, Fin (n i)`: the pair `⟨i, k⟩` is the coordinate `x_{i,k}`
of player `i`'s strategy `x_i ∈ ℝ^{n_i}`. A joint strategy is `x : Var n → ℝ`, `n = n₁ + ⋯ + n_N`
coordinates in total (p. 1). -/
abbrev Var {N : ℕ} (n : Fin N → ℕ) : Type := Σ i : Fin N, Fin (n i)

/-- A Nash equilibrium problem of polynomials (NEPP), (1.1)–(1.2), pp. 1–2: `N` players; player `i`
minimizes the polynomial `f i` in the joint variable `x` over its strategy `x_i ∈ ℝ^{n_i}`, subject
to `g i j (x_i) = 0` for `j ∈ E i` and `g i j (x_i) ≥ 0` for `j ∉ E i` (the paper's `I_i`, with
`E_i ∪ I_i = [m_i]`, p. 6). Players and constraints are indexed from `0`. -/
structure NEP (N : ℕ) (n m : Fin N → ℕ) where
  /-- the objective `f_i ∈ ℝ[x]` of player `i` -/
  f : Fin N → MvPolynomial (Var n) ℝ
  /-- the constraining polynomials `g_{i,j} ∈ ℝ[x_i]`, `j ∈ [m_i]` -/
  g : (i : Fin N) → Fin (m i) → MvPolynomial (Fin (n i)) ℝ
  /-- the equality labels `E_i ⊆ [m_i]`; the complement is the inequality labels `I_i` -/
  E : (i : Fin N) → Finset (Fin (m i))

variable {N : ℕ} {n m : Fin N → ℕ}

/-- The block `x_i ∈ ℝ^{n_i}` of a joint strategy `x`. -/
def blk (x : Var n → ℝ) (i : Fin N) : Fin (n i) → ℝ := fun k => x ⟨i, k⟩

/-- The joint strategy `(v, x_{-i})`: player `i`'s block replaced by `v`, the others kept. -/
def repl (x : Var n → ℝ) (i : Fin N) (v : Fin (n i) → ℝ) : Var n → ℝ :=
  fun w => Function.update (fun (j : Fin N) (k : Fin (n j)) => x ⟨j, k⟩) i v w.1 w.2

namespace NEP

variable (P : NEP N n m)

/-- The feasible set `X_i` of player `i`, (1.2), p. 1. -/
def X (i : Fin N) : Set (Fin (n i) → ℝ) :=
  {v | (∀ j ∈ P.E i, eval v (P.g i j) = 0) ∧ ∀ j ∉ P.E i, 0 ≤ eval v (P.g i j)}

/-- `x ∈ X = X₁ × ⋯ × X_N` (p. 2). -/
def IsFeasible (x : Var n → ℝ) : Prop := ∀ i, blk x i ∈ P.X i

/-- A Nash equilibrium (1.3), p. 2: `x` is feasible and every block `x_i` is a global minimizer of
`F_i(x_{-i})`, i.e. `f_i(x) ≤ f_i(v, x_{-i})` for every `v ∈ X_i`. -/
def IsNE (x : Var n → ℝ) : Prop :=
  P.IsFeasible x ∧ ∀ i, ∀ v ∈ P.X i, eval x (P.f i) ≤ eval (repl x i v) (P.f i)

/-- `G*`, the set of all Nash equilibria. -/
def NESet : Set (Var n → ℝ) := {x | P.IsNE x}

/-- `∇_{x_i} f_i(x)`, through formal partial derivatives in the coordinates of block `i`. -/
noncomputable def gradf (i : Fin N) (x : Var n → ℝ) : Fin (n i) → ℝ :=
  fun k => eval x (pderiv ⟨i, k⟩ (P.f i))

/-- `∇_{x_i} g_{i,j}(x_i)`, through formal partial derivatives. -/
noncomputable def gradg (i : Fin N) (j : Fin (m i)) (x : Var n → ℝ) : Fin (n i) → ℝ :=
  fun k => eval (blk x i) (pderiv k (P.g i j))

/-- A KKT point (2.5), p. 6: `x ∈ X` and there are multipliers `λ_{i,j}` with
`Σ_j λ_{i,j} ∇_{x_i} g_{i,j}(x_i) = ∇_{x_i} f_i(x)` for every `i`, and
`0 ≤ λ_{i,j} ⊥ g_{i,j}(x_i) ≥ 0` for `j ∈ I_i`. Feasibility (in particular `g_{i,j}(x_i) = 0`
for `j ∈ E_i`) is part of "the KKT condition for the optimization `F_i(x_{-i})`". -/
def IsKKT (x : Var n → ℝ) : Prop :=
  P.IsFeasible x ∧ ∃ lam : (i : Fin N) → Fin (m i) → ℝ, ∀ i,
    (∀ k, ∑ j, lam i j * P.gradg i j x k = P.gradf i x k) ∧
    ∀ j ∉ P.E i, 0 ≤ lam i j ∧ lam i j * eval (blk x i) (P.g i j) = 0

/-- The set of KKT points. -/
def KKTSet : Set (Var n → ℝ) := {x | P.IsKKT x}

end NEP

end NashPoly.Generic


