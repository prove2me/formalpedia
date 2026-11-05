-- Prove2me | Definitions.Def_LiquidWelfareFPA_cfun
-- name    : LiquidWelfareFPA_cfun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:30:56.303775+00:00
-- url     : https://prove2.me/theorems/f20c7af7-c58d-44af-95c0-212065e1af2d
-- title:
--   The constant $c(\lambda)=-1/\ln(1-\lambda)$
-- statement:
--   For $\lambda\in(0,1)$ let
--
--   $$c(\lambda)=\frac{-1}{\ln(1-\lambda)}>0 .$$
--
--   It normalizes the density $c(\lambda)/(1-\mu)$ on $[0,\lambda]$ used to draw a random shading multiplier in Lemma 4.1.
--
--   **Formalization Note** $\ln$ is the natural logarithm. Outside $(0,1)$ the value is Lean's default and is never used.
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, Lemma 4.1, p.7

import Mathlib

namespace LiquidWelfareFPA

/-- **The constant `c(λ) = −1/ln(1−λ)`.**
Fikioris & Tardos, arXiv:2210.07502v4, Lemma 4.1, p.7: "Let c(λ) = −1/ln(1−λ)."

It is positive for `λ ∈ (0,1)`, the only range where it is used; `c(λ)/(1−μ)` on `[0,λ]` is a
probability density.

**Formalization Note** `Real.log` is the natural logarithm. Outside `(0,1)` the value is Lean's
(`Real.log` of a nonpositive number is `log |x|`, and `x/0 = 0`); no statement uses it there. -/
noncomputable def cfun (lam : ℝ) : ℝ := -1 / Real.log (1 - lam)

end LiquidWelfareFPA


