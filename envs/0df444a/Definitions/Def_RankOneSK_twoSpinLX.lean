-- Prove2me | Definitions.Def_RankOneSK_twoSpinLX
-- name    : RankOneSK_twoSpinLX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:48.051878+00:00
-- url     : https://prove2.me/theorems/51762b27-e157-4399-aeaf-aa92ef5e178b
-- title:
--   Operator $L_Xf=f-\mathbb E[f\mid Y]$
-- statement:
--   For the two-spin measure $\mu_{J,a,b}$ and $f:\{\pm1\}^2\to\mathbb R$,
--   $$L_Xf(x,y)=f(x,y)-\mathbb E_{\mu_{J,a,b}}[f(X,Y)\mid Y=y].$$
--   It is the two-spin version of $L_i$ (resampling the first spin).
--
--   **Formalization Note** The two spins are Booleans read as $\pm1$; $J$ is the raw interaction (not $\bar J=\tanh J$) and $a,b$ are the fields.
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, §3, p.19 and §4, p.24

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_RankOneSK_condGivenY

open OAI.SKGap

namespace RankOneSK

/-- The operator `L_X f = f − E[f | Y]` of the two-spin Ising measure `µ_{J,a,b}`:
`L_X f(x, y) = f(x, y) − E_{µ_{J,a,b}}[f(X, Y) | Y = y]` (it resamples the first spin).

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, §3, p.19 (`L_X, L_Y` "defined accordingly") and §4, p.24.

**Formalization Note** The two spins are `Bool` values read as ±1 through `OAI.SKGap.spinValue`
(`true ↦ 1`, `false ↦ −1`); the first is `x` (the paper's `X`), the second `y` (`Y`). `J` is the raw
interaction (not `J̄ = tanh J`), `a`, `b` are the fields. -/
noncomputable def twoSpinLX (J a b : ℝ) (f : Bool → Bool → ℝ) (x y : Bool) : ℝ :=
  f x y - condGivenY J a b f y

end RankOneSK


