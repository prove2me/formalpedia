-- Prove2me | Definitions.Def_RankOneSK_resY
-- name    : RankOneSK_resY
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:32:05.64626+00:00
-- url     : https://prove2.me/theorems/4790d8ba-739d-4054-a09b-be700264d3ff
-- title:
--   $R_Y(x)=(Y-\bar Y(x))/\sigma_{Y_0}$
-- statement:
--   For the two-spin measure $\mu_{J,a,b}$,
--   $$R_Y(x)=L_Y\varphi(Y)=\frac{Y-\bar Y(x)}{\sigma_{Y_0}},\qquad \sigma_{Y_0}=\sqrt{1-\tanh^2b}.$$
--
--   **Formalization Note** The two spins are Booleans read as $\pm1$; $J$ is the raw interaction (not $\bar J=\tanh J$) and $a,b$ are the fields.
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, display (39), p.24

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_RankOneSK_magY

open OAI.SKGap

namespace RankOneSK

/-- `R_Y(x) = L_Y φ(Y) = (Y − Ȳ(x))/σ_{Y₀}`, with `Ȳ(x) = E_{µ_{J,a,b}}[Y | x]` and
`σ_{Y₀} = √(1 − tanh² b)`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, §4, display (39), p.24.

**Formalization Note** The two spins are `Bool` values read as ±1 through `OAI.SKGap.spinValue`
(`true ↦ 1`, `false ↦ −1`); the first is `x` (the paper's `X`), the second `y` (`Y`). `J` is the raw
interaction (not `J̄ = tanh J`), `a`, `b` are the fields. -/
noncomputable def resY (J a b : ℝ) (x y : Bool) : ℝ :=
  (spinValue y - magY J a b x) / Real.sqrt (1 - Real.tanh b ^ 2)

end RankOneSK


