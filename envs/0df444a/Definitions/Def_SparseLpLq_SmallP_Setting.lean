-- Prove2me | Definitions.Def_SparseLpLq_SmallP_Setting
-- name    : SparseLpLq_SmallP_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:21.286927+00:00
-- url     : https://prove2.me/theorems/705c4bf5-30d4-4cdc-8120-f004578a268e
-- title:
--   §1 and Notation, pp. 1–8 — ‖x‖_p^p and ‖x‖₀, ‖·‖_q, FEA(A,b,σ,q), SOL(A,b,σ,p,q), orthants ℙ_j (2.2), Δ_k (2.5)
-- statement:
--   This file fixes the objects of the constrained $L_p$-$L_q$ problem of Yang, Chen and Xiang,
--
--   $$\min_{x\in\mathbb R^n}\ \|x\|_p^p := \sum_{i=1}^n |x_i|^p \quad \text{s.t.} \quad \|Ax-b\|_q \le \sigma, \tag{1.1}$$
--
--   where $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $\sigma\ge 0$, $0\le p\le 1$ and $1\le q\le\infty$.
--
--   1. **The objective** $\|x\|_p^p=\sum_i |x_i|^p$ for $p>0$; for $p=0$ it is $\|x\|_0$, the number of nonzero entries of $x$ (the sparsest-solution problem).
--   2. **The $\ell_q$ norm** $\|v\|_q$ of $v\in\mathbb R^m$ for $1\le q\le\infty$; in particular $\|v\|_1=\sum_i |v_i|$ and $\|v\|_\infty=\max_i |v_i|$.
--   3. **The feasible set** $\mathrm{FEA}(A,b,\sigma,q):=\{x\in\mathbb R^n : \|Ax-b\|_q\le\sigma\}$.
--   4. **The optimal solution set** $\mathrm{SOL}(A,b,\sigma,p,q)$: the set of points $x\in\mathrm{FEA}(A,b,\sigma,q)$ with $\|x\|_p^p\le\|y\|_p^p$ for every $y\in\mathrm{FEA}(A,b,\sigma,q)$ (global minimizers; it may a priori be empty).
--   5. **The closed orthants** $\mathbb P_j$ of (2.2): for a sign pattern $s\in\{+,-\}^n$, the set of $x$ with $x_i\ge 0$ where $s_i=+$ and $x_i\le 0$ where $s_i=-$. Any two vectors $x,y$ in the same orthant satisfy $x_iy_i\ge 0$ for all $i$, and $\mathbb R^n$ is the union of the $2^n$ orthants.
--   6. **The log-moment differences** of (2.5): for $a,b\in\mathbb R^n$ and $k\ge 1$,
--   $$\Delta_k(a,b) := \sum_{i:\,a_i\ne 0} (\ln|a_i|)^k - \sum_{i:\,b_i\ne 0} (\ln|b_i|)^k .$$
--
--   The paper's blanket assumptions (p. 1) — $\sigma\ge 0$, $\mathrm{FEA}(A,b,\sigma,q)\neq\emptyset$ and $\|b\|_q>\sigma$ — are not part of these definitions; every theorem of the mission states them as hypotheses. The set of extreme points $\mathrm{EXT}(\cdot)$ is Mathlib's `Set.extremePoints ℝ`.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`, so indices run over $0,\dots,n-1$. The $\ell_q$ norm is the norm of `PiLp q`, with $q\in[1,\infty]$ an extended nonnegative real ($q=\infty$ is `⊤`); the plain norm on `Fin m → ℝ` would be the sup norm and is not used. At $p=0$ the objective is defined as the support size because `Real.rpow 0 0 = 1` would otherwise make $\sum_i |x_i|^0 = n$ constant. Orthants are indexed by a sign pattern `s : Fin n → Bool` (`true` for $\ge 0$) instead of $j=1,\dots,2^n$. The paper sorts the nonzero entries before summing in (2.5); a sum does not depend on the order, so $\Delta_k$ is written over the supports directly.
-- source:
--   Yang, Chen & Xiang, Sparse solutions of a class of constrained optimization problems, arXiv:1907.00880v5, p. 1, problem (1.1) and SOL; p. 3, problem (1.4); p. 4, FEA; p. 6, Equation (2.2); p. 7, EXT; p. 8, Equation (2.5)

import Mathlib

open scoped ENNReal Matrix

namespace SparseLpLq.SmallP

/-- `‖x‖_p^p = ∑ᵢ |xᵢ|^p` for `0 < p`, and `‖x‖₀` (the number of nonzero entries) at `p = 0`.
The case `p = 0` is split off because `Real.rpow 0 0 = 1`. -/
noncomputable def lpObj {n : ℕ} (p : ℝ) (x : Fin n → ℝ) : ℝ :=
  if p = 0 then ((Finset.univ.filter (fun i => x i ≠ 0)).card : ℝ)
  else ∑ i, |x i| ^ p

/-- The `ℓ_q` norm `‖v‖_q` of `v ∈ ℝ^m`, `1 ≤ q ≤ ∞` (`q = ∞` is `⊤`), via `PiLp`. -/
noncomputable def qNorm {m : ℕ} (q : ℝ≥0∞) (v : Fin m → ℝ) : ℝ :=
  ‖(WithLp.toLp q v : PiLp q (fun _ : Fin m => ℝ))‖

/-- `FEA(A,b,σ,q) = {x ∈ ℝⁿ : ‖Ax − b‖_q ≤ σ}`, the feasible set of problem (1.1). -/
def FEA {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ) (q : ℝ≥0∞) :
    Set (Fin n → ℝ) :=
  {x | qNorm q (A *ᵥ x - b) ≤ σ}

/-- `SOL(A,b,σ,p,q)`: the set of global minimizers of `lpObj p` over `FEA(A,b,σ,q)`. -/
def SOL {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ) (p : ℝ) (q : ℝ≥0∞) :
    Set (Fin n → ℝ) :=
  {x | x ∈ FEA A b σ q ∧ ∀ y ∈ FEA A b σ q, lpObj p x ≤ lpObj p y}

/-- The closed orthant `ℙ_s` with sign pattern `s` (`true`: `xᵢ ≥ 0`, `false`: `xᵢ ≤ 0`). -/
def orthant {n : ℕ} (s : Fin n → Bool) : Set (Fin n → ℝ) :=
  {x | ∀ i, if s i then 0 ≤ x i else x i ≤ 0}

/-- `∑_{i : aᵢ ≠ 0} (ln |aᵢ|)^k`. -/
noncomputable def logMoment {n : ℕ} (k : ℕ) (a : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => a i ≠ 0), (Real.log |a i|) ^ k

/-- `Δ_k(a,b)` of (2.5): `∑_{aᵢ ≠ 0} (ln |aᵢ|)^k − ∑_{bᵢ ≠ 0} (ln |bᵢ|)^k`. -/
noncomputable def Delta {n : ℕ} (k : ℕ) (a b : Fin n → ℝ) : ℝ :=
  logMoment k a - logMoment k b

end SparseLpLq.SmallP


