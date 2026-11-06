-- Prove2me | Definitions.Def_RankOneSK_twoSpinExp
-- name    : RankOneSK_twoSpinExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:38.316227+00:00
-- url     : https://prove2.me/theorems/c9d7d827-26d9-46ee-bebd-fdf31339e8f9
-- title:
--   Expectation under the two-spin Ising measure
-- statement:
--   For $F:\{\pm1\}^2\to\mathbb R$,
--   $$\mathbb E_{\mu_{J,a,b}}[F]=\sum_{x,y\in\{\pm1\}}\mu_{J,a,b}(x,y)\,F(x,y).$$
--   The case $J=0$ is the expectation $\mathbb E_{\mu_{0,a,b}}$ under the product measure.
--
--   **Formalization Note** The two spins are Booleans read as $\pm1$; $J$ is the raw interaction (not $\bar J=\tanh J$) and $a,b$ are the fields.
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, §2.2, p.11

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_RankOneSK_twoSpinMass

open OAI.SKGap

namespace RankOneSK

/-- The expectation `E_{µ_{J,a,b}}[F] = Σ_{x,y∈{±1}} µ_{J,a,b}(x, y) F(x, y)` under the two-spin
Ising measure. `E_{µ_{0,a,b}}` is the case `J = 0` (the product measure).

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, §2.2, p.11.

**Formalization Note** The two spins are `Bool` values read as ±1 through `OAI.SKGap.spinValue`
(`true ↦ 1`, `false ↦ −1`); the first is `x` (the paper's `X`), the second `y` (`Y`). `J` is the raw
interaction (not `J̄ = tanh J`), `a`, `b` are the fields. -/
noncomputable def twoSpinExp (J a b : ℝ) (F : Bool → Bool → ℝ) : ℝ :=
  ∑ x : Bool, ∑ y : Bool, twoSpinMass J a b x y * F x y

end RankOneSK


