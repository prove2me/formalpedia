-- Prove2me | Definitions.Def_RankOneSK_resX
-- name    : RankOneSK_resX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:31.185785+00:00
-- url     : https://prove2.me/theorems/ac43477b-22f0-4d05-a55c-2780834664bb
-- title:
--   $R_X(y)=(X-\bar X(y))/\sigma_{X_0}$
-- statement:
--   For the two-spin measure $\mu_{J,a,b}$,
--   $$R_X(y)=L_X\varphi(X)=\frac{X-\bar X(y)}{\sigma_{X_0}},\qquad \sigma_{X_0}=\sqrt{1-\tanh^2a}.$$
--
--   **Formalization Note** The two spins are Booleans read as $\pm1$; $J$ is the raw interaction (not $\bar J=\tanh J$) and $a,b$ are the fields.
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, display (39), p.24

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_RankOneSK_magX

open OAI.SKGap

namespace RankOneSK

/-- `R_X(y) = L_X φ(X) = (X − X̄(y))/σ_{X₀}`, with `X̄(y) = E_{µ_{J,a,b}}[X | y]` and
`σ_{X₀} = √(1 − tanh² a)`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, §4, display (39), p.24.

**Formalization Note** The two spins are `Bool` values read as ±1 through `OAI.SKGap.spinValue`
(`true ↦ 1`, `false ↦ −1`); the first is `x` (the paper's `X`), the second `y` (`Y`). `J` is the raw
interaction (not `J̄ = tanh J`), `a`, `b` are the fields. -/
noncomputable def resX (J a b : ℝ) (x y : Bool) : ℝ :=
  (spinValue x - magX J a b y) / Real.sqrt (1 - Real.tanh a ^ 2)

end RankOneSK


