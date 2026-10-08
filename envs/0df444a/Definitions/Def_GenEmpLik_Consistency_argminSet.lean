-- Prove2me | Definitions.Def_GenEmpLik_Consistency_argminSet
-- name    : GenEmpLik_Consistency_argminSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:52:42.610311+00:00
-- url     : https://prove2.me/theorems/163e0cee-86a9-44bd-8e9b-7b0662eb6258
-- title:
--   Solution set $\operatorname{argmin}_{x\in\mathcal X} F(x)$
-- statement:
--   For a set $\mathcal X$ and a real function $F$, the **solution set**
--
--   $$
--   \operatorname*{argmin}_{x\in\mathcal X}F(x)=\{x\in\mathcal X : F(x)\le F(y)\ \text{for all } y\in\mathcal X\}
--   $$
--
--   is the set of points of $\mathcal X$ at which $F$ attains its minimum over $\mathcal X$; it is empty when the minimum is not attained. With $F(x)=E_{P_0}[\ell(x;\xi)]$ it is $S^\star_{P_0}$, and with the robust objective $\widehat F_n$ it is $S^\star_{\widehat P_n}$ (display (23)).
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 16, (23)

import Mathlib

namespace GenEmpLik.Consistency

/-- The solution set `argmin_{x ∈ X} F(x)` (arXiv:1610.03425v3, (23), p. 16): all points of
`X` at which `F` attains its minimum over `X` (empty if the minimum is not attained). -/
def argminSet {E : Type*} (X : Set E) (F : E → ℝ) : Set E :=
  {x | x ∈ X ∧ ∀ y ∈ X, F x ≤ F y}

end GenEmpLik.Consistency


