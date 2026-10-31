-- Prove2me | Definitions.Def_KallMayerSLP_RiskMeasures_IsSubadditive
-- name    : KallMayerSLP_RiskMeasures_IsSubadditive
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:02.97789+00:00
-- url     : https://prove2.me/theorems/d94af150-94c2-413f-a00f-bd302719f6c2
-- title:
--   Subadditivity of a function on a linear space
-- statement:
--   Let $X$ be a real linear space. A function $g:X\to\mathbb R$ is **subadditive** if
--   $$
--   g(x+y)\le g(x)+g(y)\qquad\text{for all }x,y\in X.
--   $$
--
--   This is axiom (A1)/(D1) of coherent risk measures and deviation measures, and, with positive homogeneity, it is equivalent to convexity (Proposition 7.1).
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7, p.181 (PDF 191), definition before Proposition 7.1

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Subadditivity.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7, p.181 (PDF 191): a function `g : X → ℝ` on a linear space `X` is *subadditive* if
`g(x + y) ≤ g(x) + g(y)` for all `x, y ∈ X`. -/
def IsSubadditive {X : Type*} [AddCommGroup X] [Module ℝ X] (g : X → ℝ) : Prop :=
  ∀ x y : X, g (x + y) ≤ g x + g y

end KallMayerSLP.RiskMeasures


