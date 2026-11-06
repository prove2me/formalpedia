-- Prove2me | Definitions.Def_RankOneSK_condGivenY
-- name    : RankOneSK_condGivenY
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:52.570195+00:00
-- url     : https://prove2.me/theorems/ee8017dd-8a9c-492a-a346-b90fd995def5
-- title:
--   Conditional expectation $\mathbb E_{\mu_{J,a,b}}[F\mid Y=y]$
-- statement:
--   For $F:\{\pm1\}^2\to\mathbb R$ and $y\in\{\pm1\}$,
--   $$\mathbb E_{\mu_{J,a,b}}[F\mid Y=y]=\frac{\sum_x e^{Jxy+ax+by}F(x,y)}{\sum_x e^{Jxy+ax+by}}.$$
--
--   It defines $\bar X(y)=\mathbb E[X\mid y]$ and $L_Xf=f-\mathbb E[f\mid Y]$.
--
--   **Formalization Note** The two spins are Booleans read as $\pm1$; $J$ is the raw interaction (not $\bar J=\tanh J$) and $a,b$ are the fields.
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, §2.2, p.11 and §4, p.24

import Mathlib
import Definitions.Def_SKHighTemperature

open OAI.SKGap

namespace RankOneSK

/-- The conditional expectation `E_{µ_{J,a,b}}[F | Y = y]` of `F(X, Y)` given the second spin:
`Σ_x e^{Jxy+ax+by} F(x, y) / Σ_x e^{Jxy+ax+by}`, a function of `y`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, §2.2, p.11 (`X̄(y) = E[X | y]`) and §4, p.24 (`L_X f = f − E[f | Y]`).

**Formalization Note** The two spins are `Bool` values read as ±1 through `OAI.SKGap.spinValue`
(`true ↦ 1`, `false ↦ −1`); the first is `x` (the paper's `X`), the second `y` (`Y`). `J` is the raw
interaction (not `J̄ = tanh J`), `a`, `b` are the fields. The denominator is a sum of exponentials, hence positive. -/
noncomputable def condGivenY (J a b : ℝ) (F : Bool → Bool → ℝ) (y : Bool) : ℝ :=
  (∑ x : Bool, Real.exp (J * spinValue x * spinValue y + a * spinValue x + b * spinValue y) * F x y) /
    ∑ x : Bool, Real.exp (J * spinValue x * spinValue y + a * spinValue x + b * spinValue y)

end RankOneSK


