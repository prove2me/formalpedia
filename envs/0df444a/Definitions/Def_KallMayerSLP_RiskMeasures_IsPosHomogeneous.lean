-- Prove2me | Definitions.Def_KallMayerSLP_RiskMeasures_IsPosHomogeneous
-- name    : KallMayerSLP_RiskMeasures_IsPosHomogeneous
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:06.649665+00:00
-- url     : https://prove2.me/theorems/e7c793b2-a59c-48ca-af36-40eef23d8c94
-- title:
--   Positive homogeneity of a function on a linear space
-- statement:
--   Let $X$ be a real linear space. A function $g:X\to\mathbb R$ is **positive homogeneous** if
--   $$
--   g(\lambda x)=\lambda\,g(x)\qquad\text{for every }\lambda\ge0\text{ and }x\in X.
--   $$
--   The case $\lambda=0$ is included, so $g(0)=0$.
--
--   Together with subadditivity this is the sublinearity used throughout Section 7 to obtain convexity of risk measures and of their evaluation functions.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7, p.181 (PDF 191), definition before Proposition 7.1

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Positive homogeneity.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7, p.181 (PDF 191): a function `g : X → ℝ` on a linear space `X` is *positive
homogeneous* if `g(λx) = λ g(x)` for every `λ ≥ 0` and `x ∈ X`.

**Formalization Note.** `λ = 0` is included, as on the page, so `g 0 = 0`. -/
def IsPosHomogeneous {X : Type*} [AddCommGroup X] [Module ℝ X] (g : X → ℝ) : Prop :=
  ∀ c : ℝ, 0 ≤ c → ∀ x : X, g (c • x) = c * g x

end KallMayerSLP.RiskMeasures


