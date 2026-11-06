-- Prove2me | Definitions.Def_RankOneSK_twoSpinLY
-- name    : RankOneSK_twoSpinLY
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:08.788894+00:00
-- url     : https://prove2.me/theorems/32772dc2-6f52-4eea-8133-28d0813bc858
-- title:
--   Operator $L_Yf=f-\mathbb E[f\mid X]$
-- statement:
--   For the two-spin measure $\mu_{J,a,b}$ and $f:\{\pm1\}^2\to\mathbb R$,
--   $$L_Yf(x,y)=f(x,y)-\mathbb E_{\mu_{J,a,b}}[f(X,Y)\mid X=x].$$
--   It is the two-spin version of $L_j$ (resampling the second spin).
--
--   **Formalization Note** The two spins are Booleans read as $\pm1$; $J$ is the raw interaction (not $\bar J=\tanh J$) and $a,b$ are the fields.
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, §3, p.19 and §4, p.24

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_RankOneSK_condGivenX

open OAI.SKGap

namespace RankOneSK

/-- The operator `L_Y f = f − E[f | X]` of the two-spin Ising measure `µ_{J,a,b}`:
`L_Y f(x, y) = f(x, y) − E_{µ_{J,a,b}}[f(X, Y) | X = x]` (it resamples the second spin).

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, §3, p.19 and §4, p.24.

**Formalization Note** The two spins are `Bool` values read as ±1 through `OAI.SKGap.spinValue`
(`true ↦ 1`, `false ↦ −1`); the first is `x` (the paper's `X`), the second `y` (`Y`). `J` is the raw
interaction (not `J̄ = tanh J`), `a`, `b` are the fields. -/
noncomputable def twoSpinLY (J a b : ℝ) (f : Bool → Bool → ℝ) (x y : Bool) : ℝ :=
  f x y - condGivenX J a b f x

end RankOneSK


