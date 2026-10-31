-- Prove2me | Definitions.Def_TechBreakthrough_discountedAt
-- name    : TechBreakthrough_discountedAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:47.603047+00:00
-- url     : https://prove2.me/theorems/db089896-ff6a-475b-8335-84d349cd7871
-- title:
--   First times and the discounted value at a random time
-- statement:
--   For a set $A\subset[0,\infty)$, $\inf A$ is taken in $[0,\infty]$, with $\inf\emptyset=\infty$. For $r\in\mathbb R$, a function $g$ of time and $\tau\in[0,\infty]$, the discounted value is
--
--   $$e^{-r\tau}g(\tau)\quad\text{if }\tau<\infty,\qquad 0\quad\text{if }\tau=\infty.$$
--
--   This is the paper's Footnote 2: "we let $f(X_\tau)\equiv0$ over $\{\tau=\infty\}$ for any Borel function $f$ and any random time $\tau$". Every payoff of the mission is built from it.
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, Footnote 2, p.9; inf ∅ = ∞, p.14

import Mathlib

open scoped NNReal

namespace TechBreakthrough

/-- The infimum of a set of times, with `inf ∅ = ∞`, arXiv:2106.05112v1, p.9 and p.14. -/
noncomputable def firstTime (A : Set ℝ≥0) : WithTop ℝ≥0 := ⨅ t ∈ A, (t : WithTop ℝ≥0)

/-- `e^{−rτ} g(τ)`, with value `0` when `τ = ∞`: Footnote 2 of arXiv:2106.05112v1, p.9, "we let
`f(X_τ) ≡ 0` over `{τ = ∞}` for any Borel function `f` and any random time `τ`". -/
noncomputable def discountedAt (r : ℝ) (g : ℝ≥0 → ℝ) (τ : WithTop ℝ≥0) : ℝ :=
  if τ = ⊤ then 0 else Real.exp (-r * (τ.untopD 0 : ℝ≥0)) * g (τ.untopD 0)

end TechBreakthrough


