-- Prove2me | Definitions.Def_StrictCQ_CAKKT_Conditions
-- name    : StrictCQ_CAKKT_Conditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T23:32:11.712154+00:00
-- url     : https://prove2.me/theorems/de60e6b6-c1db-4107-abe0-b315668d9ff9
-- title:
--   (4.12)–(4.17), Definition 4.2, pp. 8–9 — CAKKT, its x*-form, K_C(x, r) and CAKKT-regularity
-- statement:
--   Fix a constraint system $h,g$ as in (1.1) and a feasible point $x^*$ with active set $J(x^*)$.
--
--   1. **CAKKT (4.12)–(4.13).** An objective $f$ satisfies the Complementary AKKT condition at $x^*$ if there are sequences $x^k\to x^*$, $\lambda^k\in\mathbb R^m$, $\mu^k\in\mathbb R^p_+$ with
--   $$\lim_{k\to\infty}\nabla f(x^k)+\sum_{i=1}^m\lambda_i^k\nabla h_i(x^k)+\sum_{j=1}^p\mu_j^k\nabla g_j(x^k)=0,\qquad \lim_{k\to\infty}\sum_{i=1}^m|\lambda_i^kh_i(x^k)|+\sum_{j=1}^p|\mu_j^kg_j(x^k)|=0.$$
--   2. **The $x^*$-form (4.14)–(4.15).** The same, with additionally $\mu_j^k=0$ for $j\notin J(x^*)$ (the sums then run over $J(x^*)$).
--   3. **The sets $K_C(x,r)$ (4.16).** For $x\in\mathbb R^n$ and $r\ge 0$,
--   $$K_C(x,r)=\Big\{\sum_{i=1}^m\lambda_i\nabla h_i(x)+\sum_{j\in J(x^*)}\mu_j\nabla g_j(x):\ \sum_{i=1}^m|\lambda_ih_i(x)|+\sum_{j\in J(x^*)}|\mu_jg_j(x)|\le r,\ \lambda_i\in\mathbb R,\ \mu_j\ge 0\Big\}.$$
--   Note that $J(x^*)$ is fixed by $x^*$ even when $x\neq x^*$.
--   4. **CAKKT-regularity (Definition 4.2, (4.17)).** $x^*$ is CAKKT-regular if the map $(x,r)\in\mathbb R^n\times\mathbb R_+\rightrightarrows K_C(x,r)$ is outer semicontinuous at $(x^*,0)$:
--   $$\limsup_{(x,r)\to(x^*,0)}K_C(x,r)\subseteq K_C(x^*,0).$$
--
--   CAKKT is a sequential optimality condition satisfied by every local minimizer; CAKKT-regularity is the paper's candidate for the weakest constraint qualification under which CAKKT implies KKT.
--
--   **Formalization Note** The page's (4.12)–(4.13) do not mention $x^*$; the condition $x^k\to x^*$ is part of the encoding (p. 1: sequential conditions "are formulated in terms of the sequences that converge to $x^*$", and (4.14)–(4.15) contain it). Feasibility of $x^*$ is a separate hypothesis of every theorem. Sums over $J(x^*)$ are written over all $j$ with $\mu_j=0$ off $J(x^*)$. The outer limit is taken over pairs $(x,r)$ with $r\ge 0$ ($K_C(x,r)$ is empty for $r<0$ anyway). The identity $K_C(x^*,0)=L_\Omega(x^*)^\circ$ printed at the end of (4.17) is not part of the definition; it is a separate milestone.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), pp. 8–9, (4.12)–(4.17), Definition 4.2

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting

open Filter Topology

namespace StrictCQ.CAKKT

namespace Constraints

variable {n m p : ℕ} (C : Constraints n m p)

/-- Complementary AKKT (4.12)–(4.13) at `xs` for the objective `f`, with `x k → xs`
(feasibility of `xs` is a separate hypothesis). -/
def IsCAKKT (f : EuclideanSpace ℝ (Fin n) → ℝ) (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ (x : ℕ → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Fin m → ℝ) (mu : ℕ → Fin p → ℝ),
    (∀ k j, 0 ≤ mu k j) ∧ Tendsto x atTop (𝓝 xs) ∧
    Tendsto (fun k => gradient f (x k) + ∑ i, lam k i • gradient (C.h i) (x k) +
      ∑ j, mu k j • gradient (C.g j) (x k)) atTop (𝓝 0) ∧
    Tendsto (fun k => ∑ i, |lam k i * C.h i (x k)| + ∑ j, |mu k j * C.g j (x k)|) atTop (𝓝 0)

/-- The form (4.14)–(4.15) of CAKKT: multipliers vanish off `J(xs)`, `x k → xs`. Sums over all `j`
with `mu k j = 0` for `gⱼ(xs) ≠ 0` are the page's sums over `J(xs)`. -/
def IsCAKKTAt (f : EuclideanSpace ℝ (Fin n) → ℝ) (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ (x : ℕ → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Fin m → ℝ) (mu : ℕ → Fin p → ℝ),
    (∀ k j, 0 ≤ mu k j) ∧ (∀ k j, C.g j xs ≠ 0 → mu k j = 0) ∧ Tendsto x atTop (𝓝 xs) ∧
    Tendsto (fun k => gradient f (x k) + ∑ i, lam k i • gradient (C.h i) (x k) +
      ∑ j, mu k j • gradient (C.g j) (x k)) atTop (𝓝 0) ∧
    Tendsto (fun k => ∑ i, |lam k i * C.h i (x k)| + ∑ j, |mu k j * C.g j (x k)|) atTop (𝓝 0)

/-- The set `K_C(x, r)` of (4.16): combinations `∑ λᵢ ∇hᵢ(x) + ∑_{j ∈ J(xs)} μⱼ ∇gⱼ(x)` with
`μ ≥ 0` and `∑ |λᵢ hᵢ(x)| + ∑_{j ∈ J(xs)} |μⱼ gⱼ(x)| ≤ r`. -/
def KC (xs x : EuclideanSpace ℝ (Fin n)) (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {w | ∃ (lam : Fin m → ℝ) (mu : Fin p → ℝ), (∀ j, 0 ≤ mu j) ∧ (∀ j, C.g j xs ≠ 0 → mu j = 0) ∧
    ∑ i, |lam i * C.h i x| + ∑ j, |mu j * C.g j x| ≤ r ∧
    w = ∑ i, lam i • gradient (C.h i) x + ∑ j, mu j • gradient (C.g j) x}

/-- CAKKT-regularity (Definition 4.2, (4.17)): `(x, r) ∈ ℝⁿ × ℝ₊ ⇉ K_C(x, r)` is outer
semicontinuous at `(xs, 0)`. -/
def CAKKTRegular (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  StrictCQ.AGP.outerLimitWithin (fun q : EuclideanSpace ℝ (Fin n) × ℝ => C.KC xs q.1 q.2) {q | 0 ≤ q.2} (xs, 0)
    ⊆ C.KC xs xs 0

end Constraints

end StrictCQ.CAKKT


