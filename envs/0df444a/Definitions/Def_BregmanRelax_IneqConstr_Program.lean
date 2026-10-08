-- Prove2me | Definitions.Def_BregmanRelax_IneqConstr_Program
-- name    : BregmanRelax_IneqConstr_Program
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T09:50:22.354177+00:00
-- url     : https://prove2.me/theorems/7094c17a-74d4-41af-9838-ca4a35748bf2
-- title:
--   §2 — the function (1.4), the inequality program (2.11)–(2.13), $Z_0$, $\varphi$ and the primal–dual relaxation method
-- statement:
--   This definition file sets up the inequality-constrained program of §2 of Bregman (1967) and the method that solves it.
--
--   Let $E^p$ be the $p$-dimensional Euclidean space, $f:E^p\to\mathbb R$ and $g:E^p\to E^p$ (in the theorems, $g(x)$ is the gradient of $f$ at points of a convex set $S$). Let $A$ be an $m\times p$ matrix with rows $A_1,\dots,A_m$ and $b\in E^m$; for $u\in E^m$, $uA=\sum_i u_iA_i$.
--
--   1. **The function (1.4):** $D(x,y)=f(x)-f(y)-(g(y),x-y)$.
--   2. **The hyperplanes** $A_i=\{x\in E^p \mid (A_i,x)=b_i\}$.
--   3. **The feasible set** of problem (2.11)–(2.13), minimize $f(x)$ subject to $Ax\ge b$, $x\in\bar S$:
--   $$R=\{x\in E^p \mid Ax\ge b,\ x\in\bar S\}.$$
--   4. **The set** $Z_0=\{x\in S \mid g(x)=uA \text{ for some } u\ge 0\}$.
--   5. **Condition (2)** of Note 1: if $y^n\in S$ and $y^n\to y^*\in\bar S$, then $D(y^*,y^n)\to 0$.
--   6. **The potential** $\varphi(x,u)=f(x)-(u,Ax-b)=f(x)-\sum_i u_i\bigl((A_i,x)-b_i\bigr)$.
--   7. **One step** of the method with index $i$, from $(x,u)$ to $(x',u')$, where $x'\in S$ in every case:
--      - (a) if $(A_i,x)<b_i$: for some $\lambda$, $g(x')=g(x)+\lambda A_i$ and $(A_i,x')=b_i$ (2.14)–(2.15); $u'_i=u_i+\lambda$ and $u'_j=u_j$ for $j\ne i$;
--      - (b) if $(A_i,x)=b_i$, or $(A_i,x)>b_i$ but $u_i=0$: $x'=x$, $u'=u$;
--      - (c) if $(A_i,x)>b_i$ and $u_i>0$: with $\mu'$ determined by $g(y)=g(x)-\mu'A_i$, $(A_i,y)=b_i$ for a point $y\in S$ (2.18)–(2.19), and $\mu=\min(\mu',u_i)$ (2.17),
--      $$g(x')=g(x)-\mu A_i \quad(2.16),\qquad u'_i=u_i-\mu,\quad u'_j=u_j\ (j\ne i).$$
--   8. **A run** of the method ($m\ge 1$): sequences $x^n\in E^p$, $u^n\in E^m$ with $x^0\in\operatorname{int}S$, $u^0\ge 0$, $g(x^0)=u^0A$ (so $x^0\in Z_0\cap\operatorname{int}S$, step 2), and, for every $n$, $(x^{n+1},u^{n+1})$ obtained from $(x^n,u^n)$ by one step with the cyclic index $i_n$ (step 1).
--
--   These objects are the data of Theorem 4 and of every step of its proof.
--
--   **Formalization Note** (a) Case (a) is encoded by its defining conditions (2.14)–(2.15) with $x'\in S$, as the page does ("i.e. $x^{n+1}$ is determined from the conditions"). (b) $x'$ (and the point $y$ of case (c)) is required to lie in $S$, where $g$ is the gradient. (c) The translation's set-builder for $Z_0$ breaks off after "$u\ge 0$."; the intended set, used in proof step 1, is the one above. (d) The translation prints "and $\mu_n'=u_{i_n}^n$"; the intended reading is $\mu_n''=u_{i_n}^n$, so $\mu_n=\min(\mu_n',u_{i_n}^n)$. (e) "The vector $u^0$ is such that $g(x^0)=u^0A$" refers to the witness of $x^0\in Z_0$, so $u^0\ge 0$ is part of a run. (f) The paper's 1-based cyclic index becomes $i_n=n \bmod m$ over $\{0,\dots,m-1\}$. (g) Condition (2) is read with $y^*\in\bar S$, as every use requires. (h) $\lambda$ is called `lam` in Lean.
-- source:
--   Bregman, The relaxation method of finding the common point of convex sets and its application to the solution of problems in convex programming, USSR Comput. Math. Math. Phys. 7(3) (1967), p. 206, (1.4); p. 204, Note 1 condition (2); pp. 210–212, problem (2.11)–(2.13), the set Z_0, method steps 1–3 (2.14)–(2.19); p. 212, function φ (proof of Theorem 4, step 2)

import Mathlib
import Definitions.Def_BregmanRelax_EqConstr_Program

namespace BregmanRelax.IneqConstr

/-- The feasible set `R = {x ∈ E^p | Ax ≥ b, x ∈ S̄}` of problem (2.11)–(2.13) (p. 211). -/
def feasibleIneq {p m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin p)) (b : Fin m → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin p))) : Set (EuclideanSpace ℝ (Fin p)) :=
  {x | ∀ i, b i ≤ inner ℝ (a i) x} ∩ closure S

/-- The set `Z_0` of p. 211: the points `x ∈ S` at which the gradient is a nonnegative combination
`g(x) = uA = ∑ i, u i • a i`, `u ≥ 0`, of the rows of `A`. -/
def Z0set {p m : ℕ} (S : Set (EuclideanSpace ℝ (Fin p)))
    (g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (a : Fin m → EuclideanSpace ℝ (Fin p)) : Set (EuclideanSpace ℝ (Fin p)) :=
  {x | x ∈ S ∧ ∃ u : Fin m → ℝ, (∀ i, 0 ≤ u i) ∧ g x = ∑ i, u i • a i}

/-- The function `φ(x, u) = f(x) - (u, Ax - b)` of step 2 of the proof of Theorem 4 (p. 212). -/
noncomputable def phi {p m : ℕ} (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (a : Fin m → EuclideanSpace ℝ (Fin p)) (b : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin p)) (u : Fin m → ℝ) : ℝ :=
  f x - ∑ i, u i * (inner ℝ (a i) x - b i)

/-- One step 3 (a)–(c) (pp. 211–212) of the method for problem (2.11)–(2.13), with the index `i`,
from the pair `(x, u)` to the pair `(x', u')`:
* (a) if `(A_i, x) < b_i`: `g(x') = g(x) + λ A_i` and `(A_i, x') = b_i` for some `λ` ((2.14)–(2.15)),
  and `u'_i = u_i + λ`, `u'_j = u_j` for `j ≠ i`;
* (b) if `(A_i, x) = b_i`, or `(A_i, x) > b_i` and `u_i = 0`: `x' = x`, `u' = u`;
* (c) if `(A_i, x) > b_i` and `u_i > 0`: `μ' ` is determined by `g(y) = g(x) - μ' A_i`,
  `(A_i, y) = b_i` ((2.18)–(2.19)), `μ = min(μ', u_i)` ((2.17)), `g(x') = g(x) - μ A_i` ((2.16)),
  and `u'_i = u_i - μ`, `u'_j = u_j` for `j ≠ i`.
In every case the new point `x'` (and the point `y` of case (c)) lies in `S`, where `g` is the
gradient of `f`. -/
def IsMethodStep {p m : ℕ} (S : Set (EuclideanSpace ℝ (Fin p)))
    (g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (a : Fin m → EuclideanSpace ℝ (Fin p)) (b : Fin m → ℝ) (i : Fin m)
    (x : EuclideanSpace ℝ (Fin p)) (u : Fin m → ℝ)
    (x' : EuclideanSpace ℝ (Fin p)) (u' : Fin m → ℝ) : Prop :=
  x' ∈ S ∧
  ( -- case (a)
    (inner ℝ (a i) x < b i ∧ ∃ lam : ℝ, g x' = g x + lam • a i ∧ inner ℝ (a i) x' = b i ∧
        u' = Function.update u i (u i + lam)) ∨
    -- case (b)
    ((inner ℝ (a i) x = b i ∨ (b i < inner ℝ (a i) x ∧ u i = 0)) ∧ x' = x ∧ u' = u) ∨
    -- case (c)
    (b i < inner ℝ (a i) x ∧ 0 < u i ∧
      ∃ μ' : ℝ, ∃ y ∈ S, g y = g x - μ' • a i ∧ inner ℝ (a i) y = b i ∧
        g x' = g x - min μ' (u i) • a i ∧ u' = Function.update u i (u i - min μ' (u i))) )

/-- A run of the method of pp. 211–212 for problem (2.11)–(2.13) with `m ≥ 1` constraints:
the initial point `x 0 ∈ Z_0 ∩ int S` with the vector `u 0 ≥ 0` such that `g(x 0) = u 0 A`
(step 2), and the cyclic control `i_n = n mod m` (step 1, indices `0, …, m - 1`) in every
step 3 (a)–(c). -/
def IsMethodRun {p m : ℕ} (hm : 0 < m) (S : Set (EuclideanSpace ℝ (Fin p)))
    (g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (a : Fin m → EuclideanSpace ℝ (Fin p)) (b : Fin m → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin p)) (u : ℕ → Fin m → ℝ) : Prop :=
  x 0 ∈ interior S ∧ (∀ j, 0 ≤ u 0 j) ∧ g (x 0) = ∑ j, u 0 j • a j ∧
  ∀ n, IsMethodStep S g a b ⟨n % m, Nat.mod_lt n hm⟩ (x n) (u n) (x (n + 1)) (u (n + 1))

end BregmanRelax.IneqConstr


