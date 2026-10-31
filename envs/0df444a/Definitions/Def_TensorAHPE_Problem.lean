-- Prove2me | Definitions.Def_TensorAHPE_Problem
-- name    : TensorAHPE_Problem
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:26:01.523934+00:00
-- url     : https://prove2.me/theorems/3c6cbce9-8367-4594-a270-ded130769fc0
-- title:
--   Problem (1.1) under the $d$-th order oracle model: $\min f+h$, $\nabla^d f$ $L_d$-Lipschitz
-- statement:
--   The **composite problem** (1.1) of the paper is
--
--   $$\min_{x\in\mathbb R^n} F(x) := f(x) + h(x),$$
--
--   where
--
--   1. $f:\mathbb R^n\to\mathbb R$ is convex and $d$ times differentiable, and its $d$-th derivative tensor is Lipschitz with constant $L_d \ge 0$: $\|\nabla^d f(x)-\nabla^d f(y)\| \le L_d\|x-y\|$ for all $x,y$, the left side being the tensor operator norm (2.2);
--   2. $h:\mathbb R^n\to(-\infty,+\infty]$ is proper closed convex.
--
--   The definition also records the **optimal set** $X_* = \{x : F(x)\le F(y)\ \forall y\}$ of minimizers of $F$, and the objective $F = f+h$.
--
--   These are the standing assumptions of every result of the mission.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. "d times differentiable with Lipschitz $\nabla^d f$" is `ContDiff ℝ d f` together with the Lipschitz bound on `iteratedFDeriv ℝ d f` in the operator norm of multilinear maps, which equals the paper's tensor norm. $F$ takes values in `EReal`. The order $d$ is a parameter; the theorems assume $d\ge1$.
-- source:
--   Jiang, Wang & Zhang, An Optimal High-Order Tensor Method for Convex Optimization, arXiv:1812.06557v3, Eq. (1.1), p.2; Eq. (2.2), p.5; §2, p.6; X_* from Lemma 3.1, p.7

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex

namespace TensorAHPE

/-- **The composite objective `F = f + h`.**
Jiang, Wang & Zhang, arXiv:1812.06557v3, Eq. (1.1), p.2: "min_{x∈ℝⁿ} F(x) := f(x) + h(x)".

**Formalization Note.** `f` is real-valued and `h` is `EReal`-valued, so `F x = f x + h x` is
computed in `EReal`; it is `+∞` exactly where `h` is. -/
noncomputable def compositeObj {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (h : EuclideanSpace ℝ (Fin n) → EReal) (x : EuclideanSpace ℝ (Fin n)) : EReal :=
  (f x : EReal) + h x

/-- **The optimal set `X_*`.** Jiang, Wang & Zhang, arXiv:1812.06557v3, Lemma 3.1, p.7: "the set
of optimal value points X_*": the minimizers of `F` over `ℝⁿ`. -/
def minSet {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EReal) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ y, F x ≤ F y}

/-- **Problem (1.1) under the d-th order oracle model.**
Jiang, Wang & Zhang, arXiv:1812.06557v3, Eq. (1.1), p.2: "min_{x∈ℝⁿ} F(x) := f(x) + h(x), where f
is differentiable and convex, and h is convex but possibly non-smooth"; Eq. (2.2), p.5: "f is d
times Lipschitz-continuous and differentiable with Lipschitz constant L_d for d-th order derivative
tensor; i.e. ‖∇ᵈf(x) − ∇ᵈf(y)‖ ≤ L_d‖x − y‖ ∀x, y ∈ ℝⁿ, where the left side is the d-th order
tensor operator norm"; §2, p.6: h is "a proper closed convex function".

Fields: the smooth part `f`, the nonsmooth part `h`, the Lipschitz constant `L = L_d`; `f` convex
on `ℝⁿ`; `f` is `d` times continuously differentiable; `∇ᵈf` is `L`-Lipschitz; `L ≥ 0`; `h` proper
closed convex.

**Formalization Note.** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`. "d times differentiable with a
Lipschitz d-th derivative" is `ContDiff ℝ d f` (the d-th derivative is then continuous, which a
Lipschitz one is anyway) together with the Lipschitz bound on `iteratedFDeriv ℝ d f` in Mathlib's
operator norm of continuous multilinear maps. The paper's tensor operator norm is the maximum of
`|T[u₁,…,u_d]|` over unit vectors; the sign of one argument can be flipped, so it is the same norm.
`0 ≤ L` is the meaning of "Lipschitz constant". The order `d` is a parameter; the statements that
use the model require `1 ≤ d`, which makes `f` differentiable as (1.1) requires. -/
structure Problem (n d : ℕ) where
  /-- The smooth convex part `f`. -/
  f : EuclideanSpace ℝ (Fin n) → ℝ
  /-- The proper closed convex, possibly nonsmooth part `h`. -/
  h : EuclideanSpace ℝ (Fin n) → EReal
  /-- The Lipschitz constant `L_d` of `∇ᵈf`. -/
  L : ℝ
  convex_f : ConvexOn ℝ Set.univ f
  contDiff_f : ContDiff ℝ d f
  lipschitz_deriv : ∀ x y, ‖iteratedFDeriv ℝ d f x - iteratedFDeriv ℝ d f y‖ ≤ L * ‖x - y‖
  L_nonneg : 0 ≤ L
  proper_h : IsProperClosedConvex h

/-- The objective `F = f + h` of problem (1.1). -/
noncomputable def Problem.F {n d : ℕ} (P : Problem n d) : EuclideanSpace ℝ (Fin n) → EReal :=
  compositeObj P.f P.h

end TensorAHPE


