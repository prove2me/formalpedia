-- Prove2me | Definitions.Def_RankOneSK_magX
-- name    : RankOneSK_magX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:23.221206+00:00
-- url     : https://prove2.me/theorems/12675b86-4998-46c3-9ba7-a2becac8dcc3
-- title:
--   Conditional mean $\bar X(y)=\mathbb E[X\mid y]$
-- statement:
--   For the two-spin measure $\mu_{J,a,b}$, $\bar X(y)=\mathbb E_{\mu_{J,a,b}}[X\mid Y=y]$. By Lemma 2.3 it equals $(\bar X_0+\bar Jy)/(1+\bar X_0\bar Jy)$ with $\bar X_0=\tanh a$, $\bar J=\tanh J$.
--
--   **Formalization Note** The two spins are Booleans read as $\pm1$; $J$ is the raw interaction (not $\bar J=\tanh J$) and $a,b$ are the fields.
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, §2.2, p.11

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_RankOneSK_condGivenY

open OAI.SKGap

namespace RankOneSK

/-- The conditional mean `X̄(y) = E_{µ_{J,a,b}}[X | Y = y]` of the first spin given the second.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, §2.2, p.11.

**Formalization Note** The two spins are `Bool` values read as ±1 through `OAI.SKGap.spinValue`
(`true ↦ 1`, `false ↦ −1`); the first is `x` (the paper's `X`), the second `y` (`Y`). `J` is the raw
interaction (not `J̄ = tanh J`), `a`, `b` are the fields. -/
noncomputable def magX (J a b : ℝ) (y : Bool) : ℝ :=
  condGivenY J a b (fun x _ => spinValue x) y

end RankOneSK


