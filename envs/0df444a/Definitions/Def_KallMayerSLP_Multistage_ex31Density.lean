-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_ex31Density
-- name    : KallMayerSLP_Multistage_ex31Density
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:03.348181+00:00
-- url     : https://prove2.me/theorems/7dc8cb72-7a8b-459d-ae69-8d104f87c3a1
-- title:
--   Example 3.1: the joint density $f(\xi_2,\xi_3)$
-- statement:
--   The density of Example 3.1, for a constant $\varepsilon\in(-1,1)$:
--   $$
--   f(\xi_2,\xi_3)=\begin{cases}1+\varepsilon&0\le\xi_2,\xi_3\le0.5\\1+\varepsilon&0.5\le\xi_2,\xi_3\le1\\1-\varepsilon&0\le\xi_2<0.5<\xi_3\le1\\1-\varepsilon&0\le\xi_3<0.5<\xi_2\le1\\0&\text{else.}\end{cases}
--   $$
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Example 3.1, p.257 (PDF 266)

import Mathlib

namespace KallMayerSLP.Multistage

/-- The joint density `f(ξ_2, ξ_3)` of Example 3.1 (Kall & Mayer, *Stochastic Linear Programming*
(2005), Chapter 3, Example 3.1, p.257, PDF 266): `1 + ε` for `0 ≤ ξ_2, ξ_3 ≤ 0.5` and for
`0.5 ≤ ξ_2, ξ_3 ≤ 1`; `1 − ε` for `0 ≤ ξ_2 < 0.5 < ξ_3 ≤ 1` and for `0 ≤ ξ_3 < 0.5 < ξ_2 ≤ 1`;
`0` otherwise. -/
noncomputable def ex31Density (ε x y : ℝ) : ℝ :=
  open Classical in
  if (0 ≤ x ∧ x ≤ 1 / 2 ∧ 0 ≤ y ∧ y ≤ 1 / 2) ∨ (1 / 2 ≤ x ∧ x ≤ 1 ∧ 1 / 2 ≤ y ∧ y ≤ 1) then 1 + ε
  else if (0 ≤ x ∧ x < 1 / 2 ∧ 1 / 2 < y ∧ y ≤ 1) ∨ (0 ≤ y ∧ y < 1 / 2 ∧ 1 / 2 < x ∧ x ≤ 1) then
    1 - ε
  else 0

end KallMayerSLP.Multistage


