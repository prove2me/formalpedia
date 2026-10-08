-- Prove2me | Definitions.Def_NonsmoothLojasiewicz_Traj_Slope
-- name    : NonsmoothLojasiewicz_Traj_Slope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:10:43.462244+00:00
-- url     : https://prove2.me/theorems/f4cf0fad-a55f-41f4-9a46-9f206e07312d
-- title:
--   Nonsmooth slope $m_f$, critical points, Łojasiewicz inequality and Łojasiewicz exponent
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ and let $\partial f(x)$ be its limiting subdifferential at $x$ (Definition 2.10).
--
--   1. The **nonsmooth slope** of $f$ is
--   $$m_f(x)=\inf\{\|x^*\|:\ x^*\in\partial f(x)\}\in[0,+\infty],$$
--   with $m_f(x)=+\infty$ whenever $\partial f(x)=\emptyset$ (equation (4)).
--   2. The set of (generalized) **critical points** is $\operatorname{crit} f=\{x\in\mathbb R^n:\ 0\in\partial f(x)\}$ (Definition 2.11).
--   3. The **Łojasiewicz inequality holds around** $a$ with exponent $\theta$ if the function
--   $$x\ \mapsto\ \frac{|f(x)-f(a)|^{\theta}}{m_f(x)}$$
--   is bounded on a neighbourhood of $a$, with the conventions $0^0=1$, $\infty/\infty=0/0=0$ and $\lambda/0=+\infty$ for $\lambda>0$ (display (8) and the conventions of Section 1).
--   4. A **Łojasiewicz exponent** of $f$ at a point $a$ of its domain is any $\theta\in[0,1)$ for which the Łojasiewicz inequality holds around $a$ (Section 4).
--
--   These are the quantities in which the convergence rates of Theorem 4.7 are expressed.
--
--   **Formalization Note** $m_f$ is valued in $[0,+\infty]$ (`ℝ≥0∞`), the empty infimum being $+\infty$. The bounded ratio is encoded as: there are $C$ and a neighbourhood $U$ of $a$ with $|f(x)-f(a)|^\theta\le C\|v\|$ for all $x\in U$ and all $v\in\partial f(x)$. At points with $\partial f(x)=\emptyset$ the ratio is $0$ under the paper's conventions and nothing is required; where $\partial f(x)\neq\emptyset$, $f(x)$ is finite, so the real value of $f(x)$ is the paper's value, and "ratio $\le C$" is exactly "$\le C\|v\|$ for every subgradient $v$". The power is `Real.rpow` on a nonnegative base, with $0^0=1$ as on the page. The domain condition $f(a)<+\infty$ is part of the definition of a Łojasiewicz exponent. The limiting subdifferential is the published definition `NonconvexSplitting.Shared.LimitingSubdiff`.
-- source:
--   Bolte, Daniilidis & Lewis, The Łojasiewicz inequality for nonsmooth subanalytic functions with applications to subgradient dynamical systems, SIAM J. Optim. 17 (2007) 1205–1223, p. 1211, equation (4) and Definition 2.11; p. 1213, display (8) and its conventions; p. 1205, conventions after (1); p. 1221, definition of a Łojasiewicz exponent

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonsmoothLojasiewicz_Continuous_LojIneqAt
import Definitions.Def_NonsmoothLojasiewicz_Continuous_slope

open Topology
open scoped ENNReal NNReal

namespace NonsmoothLojasiewicz.Traj

open NonconvexSplitting.Shared

/-- Section 4 (p. 1221): a *Łojasiewicz exponent* of `f` at a point `a` of its domain is any
`θ ∈ [0, 1)` for which the Łojasiewicz inequality holds around `a`. -/
def IsLojExponent {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (a : EuclideanSpace ℝ (Fin n))
    (θ : ℝ) : Prop :=
  f a ≠ ⊤ ∧ 0 ≤ θ ∧ θ < 1 ∧ NonsmoothLojasiewicz.Continuous.LojIneqAt f a θ

end NonsmoothLojasiewicz.Traj


