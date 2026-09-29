-- Prove2me | Definitions.Def_LewisTorczon_BoundPS_Box
-- name    : LewisTorczon_BoundPS_Box
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:41:02.082276+00:00
-- url     : https://prove2.me/theorems/3c4a3703-a727-4aa6-9c0d-032594ba0d28
-- title:
--   The box $\Omega=\{\ell\le x\le u\}$, its projection $P$, and the level set $L_\Omega(y)$
-- statement:
--   This file fixes the feasible region of the bound constrained problem
--   $$\min f(x)\quad\text{subject to}\quad \ell\le x\le u,$$
--   where $f:\mathbb R^n\to\mathbb R$ and the bounds $\ell,u$ have entries in the extended reals, with $\ell_j<u_j$ for every coordinate $j$. An entry $\ell_j=-\infty$ or $u_j=+\infty$ means that the variable is unbounded below or above.
--
--   1. **Feasible region.** $\Omega=\{x\in\mathbb R^n : \ell_j\le x_j\le u_j \text{ for } j=1,\dots,n\}$.
--   2. **Scalar projection.** For a pair of bounds $a<b$ and $t\in\mathbb R$, $p(t)=a$ if $t<a$, $p(t)=t$ if $a\le t\le b$, and $p(t)=b$ if $t>b$; that is, $p(t)=\max\{a,\min\{b,t\}\}$. Because $a<b$, this value is always a finite real number (for instance $p(t)=t$ when $a=-\infty$ and $t<b$).
--   3. **Projection onto $\Omega$.** $P(x)=\sum_{j=1}^n p_j(x_j)\,e_j$, where $p_j$ uses the bounds $\ell_j,u_j$ and $e_j$ is the $j$-th standard basis vector.
--   4. **Feasible level set.** $L_\Omega(y)=\{x\in\Omega : f(x)\le f(y)\}$.
--
--   Points of $\mathbb R^n$ carry the Euclidean norm, as in the paper. These are the basic objects in which every convergence statement of the mission is phrased.
--
--   **Formalization Note** Points are `EuclideanSpace ℝ (Fin n)` and the bounds are functions `Fin n → EReal`; the paper's coordinates $j=1,\dots,n$ are Lean's `Fin n` indices $0,\dots,n-1$. The scalar projection is computed as `max a (min b t)` in `EReal` and converted to a real number; under $a<b$ the conversion never meets $\pm\infty$. The condition $\ell<u$ is not built into the definitions; every theorem carries it as a hypothesis.
-- source:
--   Lewis & Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report No. 96-20 (NASA CR-198306), March 1996, pp. 1–2, §1, problem (1) and Notation (Ω, p_j, P, L_Ω(y))

import Mathlib

namespace LewisTorczon.BoundPS

/-- The feasible region `Ω = { x ∈ ℝⁿ | ℓ ≤ x ≤ u }` of problem (1)
(Lewis–Torczon, ICASE 96-20, p. 1). The bounds are extended reals, so `ℓ_j = -∞` and
`u_j = +∞` are allowed, as on p. 1 ("by permitting `ℓ_j, u_j = ±∞`"). Points of `ℝⁿ` carry the
Euclidean norm. The paper's coordinate `j = 1, …, n` is Lean's `j : Fin n` (0-based). -/
def box {n : ℕ} (lo hi : Fin n → EReal) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ j, lo j ≤ ((x j : ℝ) : EReal) ∧ ((x j : ℝ) : EReal) ≤ hi j}

/-- The scalar projection `p_j(t)` of p. 2: `ℓ_j` if `t < ℓ_j`, `t` if `ℓ_j ≤ t ≤ u_j`,
`u_j` if `t > u_j`, computed as `max ℓ_j (min u_j t)` in `EReal`. When `a < b` the value is
finite (e.g. `a = -∞`, `t < b` gives `t`; `a = -∞`, `b = +∞` gives `t`), so `toReal` loses
nothing. -/
noncomputable def clampCoord (a b : EReal) (t : ℝ) : ℝ :=
  (max a (min b (t : EReal))).toReal

/-- The projection onto `Ω`, `P(x) = Σ_j p_j(x_j) e_j` (p. 2). -/
noncomputable def boxProj {n : ℕ} (lo hi : Fin n → EReal) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => clampCoord (lo j) (hi j) (x j))

/-- The feasible level set `L_Ω(y) = { x ∈ Ω | f(x) ≤ f(y) }` (p. 2). -/
def levelSet {n : ℕ} (lo hi : Fin n → EReal) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x ∈ box lo hi ∧ f x ≤ f y}

end LewisTorczon.BoundPS


