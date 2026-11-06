-- Prove2me | Definitions.Def_RankOneSK_condGivenX
-- name    : RankOneSK_condGivenX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:44.106417+00:00
-- url     : https://prove2.me/theorems/87f7b78e-9e3e-4180-aff6-7f00b7e5c62b
-- title:
--   Conditional expectation $\mathbb E_{\mu_{J,a,b}}[F\mid X=x]$
-- statement:
--   For $F:\{\pm1\}^2\to\mathbb R$ and $x\in\{\pm1\}$,
--   $$\mathbb E_{\mu_{J,a,b}}[F\mid X=x]=\frac{\sum_y e^{Jxy+ax+by}F(x,y)}{\sum_y e^{Jxy+ax+by}}.$$
--
--   It defines $\bar Y(x)=\mathbb E[Y\mid x]$ and $L_Yf=f-\mathbb E[f\mid X]$.
--
--   **Formalization Note** The two spins are Booleans read as $\pm1$; $J$ is the raw interaction (not $\bar J=\tanh J$) and $a,b$ are the fields.
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, §2.2, p.11 and §4, p.24

import Mathlib
import Definitions.Def_SKHighTemperature

open OAI.SKGap

namespace RankOneSK

/-- The conditional expectation `E_{µ_{J,a,b}}[F | X = x]` of `F(X, Y)` given the first spin:
`Σ_y e^{Jxy+ax+by} F(x, y) / Σ_y e^{Jxy+ax+by}`, a function of `x`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, §2.2, p.11 (`Ȳ(x) = E[Y | x]`) and §4, p.24 (`L_Y f = f − E[f | X]`).

**Formalization Note** The two spins are `Bool` values read as ±1 through `OAI.SKGap.spinValue`
(`true ↦ 1`, `false ↦ −1`); the first is `x` (the paper's `X`), the second `y` (`Y`). `J` is the raw
interaction (not `J̄ = tanh J`), `a`, `b` are the fields. The denominator is a sum of exponentials, hence positive. -/
noncomputable def condGivenX (J a b : ℝ) (F : Bool → Bool → ℝ) (x : Bool) : ℝ :=
  (∑ y : Bool, Real.exp (J * spinValue x * spinValue y + a * spinValue x + b * spinValue y) * F x y) /
    ∑ y : Bool, Real.exp (J * spinValue x * spinValue y + a * spinValue x + b * spinValue y)

end RankOneSK


