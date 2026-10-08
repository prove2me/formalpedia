-- Prove2me | Definitions.Def_GenEmpLik_Expansion_huber
-- name    : GenEmpLik_Expansion_huber
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:01:53.585017+00:00
-- url     : https://prove2.me/theorems/c6f115ad-4194-499c-a64e-df96d55efa3d
-- title:
--   Huber function $h_\epsilon$
-- statement:
--   For $\epsilon>0$ the **Huber function** is
--
--   $$
--   h_\epsilon(t)=\inf_y\Big\{\tfrac12(t-y)^2+\epsilon|y|\Big\}=\begin{cases}\tfrac12t^2 & |t|\le\epsilon,\\ \epsilon|t|-\tfrac12\epsilon^2 & |t|>\epsilon.\end{cases}
--   $$
--
--   It is quadratic near $0$ and grows linearly, and it is the lower comparison function for $f(t+1)$ in the sandwich (30).
--
--   **Formalization Note** The definition is the closed form on the right. It is a total function of $(\epsilon,t)$; every statement that uses it assumes $\epsilon>0$.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 31, App. A.1 (Huber function)

import Mathlib

namespace GenEmpLik.Expansion

/-- The Huber function `h_ε` (Duchi, Glynn & Namkoong, arXiv:1610.03425v3, p. 31, App. A.1),
in its closed form: `h_ε(t) = t²/2` if `|t| ≤ ε` and `h_ε(t) = ε|t| − ε²/2` if `|t| > ε`.
The paper defines it for `ε > 0` (equivalently as `inf_y {½(t − y)² + ε|y|}`); every statement
using it assumes `0 < ε`. -/
noncomputable def huber (ε t : ℝ) : ℝ :=
  if |t| ≤ ε then t ^ 2 / 2 else ε * |t| - ε ^ 2 / 2

end GenEmpLik.Expansion


