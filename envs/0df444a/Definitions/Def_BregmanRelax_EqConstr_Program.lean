-- Prove2me | Definitions.Def_BregmanRelax_EqConstr_Program
-- name    : BregmanRelax_EqConstr_Program
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:52:37.455011+00:00
-- url     : https://prove2.me/theorems/6aacadeb-1059-419c-8e12-27724286efdd
-- title:
--   §2 — the function $D$ of (1.4), the hyperplanes $A_i$, the feasible set $R$, the set $Z$ and condition (2)
-- statement:
--   This definition file sets up the convex program of §2 of Bregman (1967) with linear equality constraints.
--
--   Work in the Euclidean space $E^p$ with inner product $(\cdot,\cdot)$. Let $f : E^p\to\mathbb R$ be a function and $g : E^p\to E^p$ a map (in the theorems, $g(x)$ is the gradient of $f$ at points $x$ of a convex set $S\subset E^p$). Let $A$ be an $m\times p$ matrix with rows $A_1,\dots,A_m\in E^p$ and let $b\in E^m$.
--
--   1. **The function (1.4).**
--   $$D(x,y)=f(x)-f(y)-\bigl(g(y),\,x-y\bigr).$$
--   2. **The hyperplanes.** For each row $i$,
--   $$A_i=\Bigl\{x\in E^p \;\Big|\; \sum_{j=1}^p a_{ij}x_j=b_i\Bigr\}=\{x\in E^p \mid (A_i,x)=b_i\}.$$
--   (The paper uses $A_i$ both for the $i$-th row and for this hyperplane.)
--   3. **The feasible set** of the problem "minimize $f(x)$ subject to $Ax=b$, $x\in\bar S$" ((2.1)–(2.3)):
--   $$R=\{x\in E^p \mid Ax=b,\ x\in \bar S\}.$$
--   4. **The set $Z$** (p. 209): the points $x\in S$ for which there is $u\in E^m$ with
--   $$g(x)=uA=\sum_{i=1}^m u_i A_i .$$
--   5. **Condition (2)** (Note 1, p. 204): whenever $y^n\in S$ and $y^n\to y^*\in\bar S$, one has $D(y^*,y^n)\to 0$.
--
--   These are the objects of Lemma 3 and Theorem 3: the relaxation method is run with the $D$-projections onto the hyperplanes $A_i$, and $Z$ is the set of points at which the Lagrange condition of the problem holds.
--
--   **Formalization Note** (a) The rows $A_i$ are vectors `a i` in `EuclideanSpace ℝ (Fin p)`, and $(A_i,x)$ is the real inner product; $uA$ is $\sum_i u_i A_i$ with $u : \mathrm{Fin}\,m\to\mathbb R$. (b) The gradient $g$ is explicit data; the theorems tie it to $f$ only on $S$, so values of $g$ (and of $D$) outside $S$ carry no meaning. (c) The paper prints condition (2) with "$y^n\to y^*\in S$"; every use of it (Lemma 3, applied at a feasible point $y^*\in R\subset\bar S$) needs $y^*\in\bar S$, and that is the reading taken here.
-- source:
--   Bregman, The relaxation method of finding the common point of convex sets and its application to the solution of problems in convex programming, USSR Comput. Math. Math. Phys. 7(3) (1967), p. 204, Note 1, condition (2); p. 206, (1.4); pp. 208–209, problem (2.1)–(2.3), the set R and the set Z; p. 209, Theorem 3 (the hyperplanes A_i)

import Mathlib

namespace BregmanRelax.EqConstr

/-- The function (1.4) of Bregman (1967, p. 206) built from `f` and its gradient map `g`:
`D(x, y) = f(x) - f(y) - (g(y), x - y)`. -/
noncomputable def bregmanD {p : ℕ} (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (x y : EuclideanSpace ℝ (Fin p)) : ℝ :=
  f x - f y - inner ℝ (g y) (x - y)

/-- The hyperplane `A_i = {x ∈ E^p | (A_i, x) = b_i}` of the `i`-th equation of `Ax = b`
(Theorem 3, p. 209); the row `A_i` of the matrix `A` is the vector `a i`. -/
def hyperplane {p m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin p)) (b : Fin m → ℝ) (i : Fin m) :
    Set (EuclideanSpace ℝ (Fin p)) :=
  {x | inner ℝ (a i) x = b i}

/-- The feasible set `R = {x ∈ E^p | Ax = b, x ∈ S̄}` of problem (2.1)–(2.3) (p. 208). -/
def feasibleEq {p m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin p)) (b : Fin m → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin p))) : Set (EuclideanSpace ℝ (Fin p)) :=
  {x | ∀ i, inner ℝ (a i) x = b i} ∩ closure S

/-- The set `Z` of p. 209: the points `x ∈ S` at which the gradient is a combination
`g(x) = uA = ∑ i, u i • a i` of the rows of `A`, for some `u ∈ E^m`. -/
def Zset {p m : ℕ} (S : Set (EuclideanSpace ℝ (Fin p)))
    (g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (a : Fin m → EuclideanSpace ℝ (Fin p)) : Set (EuclideanSpace ℝ (Fin p)) :=
  {x | x ∈ S ∧ ∃ u : Fin m → ℝ, g x = ∑ i, u i • a i}

/-- Condition (2) of Note 1 (p. 204), with the limit `y*` taken in the closure `S̄`:
if `y n ∈ S` and `y n → y* ∈ S̄`, then `D(y*, y n) → 0`. -/
def Cond2 {p : ℕ} (S : Set (EuclideanSpace ℝ (Fin p)))
    (D : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) → ℝ) : Prop :=
  ∀ (y : ℕ → EuclideanSpace ℝ (Fin p)) (y' : EuclideanSpace ℝ (Fin p)), (∀ n, y n ∈ S) →
    y' ∈ closure S → Filter.Tendsto y Filter.atTop (nhds y') →
    Filter.Tendsto (fun n => D y' (y n)) Filter.atTop (nhds 0)

end BregmanRelax.EqConstr


