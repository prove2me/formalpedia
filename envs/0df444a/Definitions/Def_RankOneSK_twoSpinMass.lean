-- Prove2me | Definitions.Def_RankOneSK_twoSpinMass
-- name    : RankOneSK_twoSpinMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:34.783666+00:00
-- url     : https://prove2.me/theorems/8a06ca31-561f-4b79-99e6-570c6405b9cb
-- title:
--   Two-spin Ising measure $\mu_{J,a,b}$
-- statement:
--   For $J,a,b\in\mathbb R$ the two-spin Ising measure on $\{\pm1\}^2$ is
--   $$\mu_{J,a,b}(x,y)=\frac1Z\exp(Jxy+ax+by),\qquad Z=\sum_{x,y\in\{\pm1\}}\exp(Jxy+ax+by).$$
--   At $J=0$ it is the product measure with means $\bar X_0=\tanh a$, $\bar Y_0=\tanh b$.
--
--   Conditioning the SK measure on all spins except $i,j$ gives $\mu_{J_{ij},a,b}$ with $a,b$ the local fields from the other spins; §3–§5 analyse this measure uniformly in $a,b$.
--
--   **Formalization Note** The two spins are Booleans read as $\pm1$; $J$ is the raw interaction (not $\bar J=\tanh J$) and $a,b$ are the fields.
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, §2.2, p.11

import Mathlib
import Definitions.Def_SKHighTemperature

open OAI.SKGap

namespace RankOneSK

/-- The two-spin Ising measure `µ_{J,a,b}(x, y) = Z⁻¹ exp(Jxy + ax + by)` on `{±1}²`, with
`Z = Σ_{x,y∈{±1}} exp(Jxy + ax + by)`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, §2.2, p.11.

**Formalization Note** The two spins are `Bool` values read as ±1 through `OAI.SKGap.spinValue`
(`true ↦ 1`, `false ↦ −1`); the first is `x` (the paper's `X`), the second `y` (`Y`). `J` is the raw
interaction (not `J̄ = tanh J`), `a`, `b` are the fields. -/
noncomputable def twoSpinMass (J a b : ℝ) (x y : Bool) : ℝ :=
  Real.exp (J * spinValue x * spinValue y + a * spinValue x + b * spinValue y) /
    ∑ x' : Bool, ∑ y' : Bool,
      Real.exp (J * spinValue x' * spinValue y' + a * spinValue x' + b * spinValue y')

end RankOneSK


