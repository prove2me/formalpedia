-- Prove2me | Definitions.Def_ExactModKL_KLIneq
-- name    : ExactModKL_KLIneq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:55:52.781769+00:00
-- url     : https://prove2.me/theorems/3cb338b1-989d-41ea-b635-496dc7fbf3cc
-- title:
--   Inequality (7) of the generalized concave KL property w.r.t. $U$, $\eta$, $\varphi$
-- statement:
--   Let $f:\mathbb R^n\to(-\infty,\infty]$, $\bar x\in\mathbb R^n$, $U\subseteq\mathbb R^n$, $\eta\in(0,\infty]$ and $\varphi:[0,\eta)\to\mathbb R$. Write $\partial f$ for the limiting subdifferential and $[0<f-f(\bar x)<\eta]=\{x:0<f(x)-f(\bar x)<\eta\}$. The function $f$ satisfies inequality (7) with respect to $U$, $\eta$ and $\varphi$ if for every $x\in U\cap[0<f-f(\bar x)<\eta]$,
--   $$
--   \varphi'_-\big(f(x)-f(\bar x)\big)\cdot\operatorname{dist}\big(0,\partial f(x)\big)\ge1 .
--   $$
--   When $\varphi$ is moreover concave and in $\Phi_\eta$, $f$ has the generalized concave KL property at $\bar x$ with respect to $U$, $\eta$ and $\varphi$ (Definition 3.2(i)), and $\varphi$ is called a concave desingularizing function of $f$ at $\bar x$ with respect to $U$ and $\eta$.
--
--   **Formalization Note** $f$ takes values in the extended reals and $\eta$ may be $\infty$. The inequality is written as $1\le\varphi'_-(f(x)-f(\bar x))\,\|v\|$ for every $v\in\partial f(x)$. For $\varphi'_->0$ (every concave $\varphi\in\Phi_\eta$) this is the printed inequality with the paper's convention $\operatorname{dist}(0,\emptyset)=\infty$; at a point with $\partial f(x)=\emptyset$ it holds trivially.
-- source:
--   Wang–Wang, arXiv:2008.13257v5, Definition 3.2(i) and (7), p.9

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_ExactModKL_leftDeriv

open scoped ENNReal

namespace ExactModKL

open NonconvexSplitting.Shared

/-- Inequality (7) of the generalized concave KL property of `f` at `x̄` with respect to `U`,
`η` and `ϕ` (Wang–Wang, arXiv:2008.13257v5 (preprint), Definition 3.2(i), (7), p.9): for all
`x ∈ U ∩ [0 < f − f(x̄) < η]`,
`ϕ′_−(f(x) − f(x̄)) · dist(0, ∂f(x)) ≥ 1`,
with `∂f` the limiting subdifferential.

**Formalization Note.** Values of `f` are in `EReal` and `η : ℝ≥0∞` (`η = ∞` allowed); the
band `0 < f x − f x̄ < η` is computed in `EReal`. The inequality is written in the form
`∀ v ∈ ∂f(x), 1 ≤ ϕ′_−(f(x) − f(x̄)) · ‖v‖`. When `ϕ′_− > 0` (every concave `ϕ ∈ Φ_η`, Lemma
3.1(ii)) this is the printed inequality with `dist(0, ∅) = ∞` (p.2); at a point with
`∂f(x) = ∅` it holds trivially. `f(x) − f(x̄)` is passed to `ϕ′_−` as a real number via
`EReal.toReal`; on the band it is finite. -/
def KLIneq {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (xbar : EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) (η : ℝ≥0∞) (ϕ : ℝ → ℝ) : Prop :=
  ∀ x ∈ U, 0 < f x - f xbar → f x - f xbar < (η : EReal) →
    ∀ v ∈ LimitingSubdiff f x, 1 ≤ leftDeriv ϕ (f x - f xbar).toReal * ‖v‖

end ExactModKL


