-- Prove2me | Definitions.Def_RankOneSK_magY
-- name    : RankOneSK_magY
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:21.322994+00:00
-- url     : https://prove2.me/theorems/548d0fa0-0299-408d-a7e3-e5418306efc5
-- title:
--   Conditional mean $\bar Y(x)=\mathbb E[Y\mid x]$
-- statement:
--   For the two-spin measure $\mu_{J,a,b}$, $\bar Y(x)=\mathbb E_{\mu_{J,a,b}}[Y\mid X=x]$. By Lemma 2.3 it equals $(\bar Y_0+\bar Jx)/(1+\bar Y_0\bar Jx)$ with $\bar Y_0=\tanh b$.
--
--   **Formalization Note** The two spins are Booleans read as $\pm1$; $J$ is the raw interaction (not $\bar J=\tanh J$) and $a,b$ are the fields.
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, §2.2, p.11

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_RankOneSK_condGivenX

open OAI.SKGap

namespace RankOneSK

/-- The conditional mean `Ȳ(x) = E_{µ_{J,a,b}}[Y | X = x]` of the second spin given the first.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, §2.2, p.11.

**Formalization Note** The two spins are `Bool` values read as ±1 through `OAI.SKGap.spinValue`
(`true ↦ 1`, `false ↦ −1`); the first is `x` (the paper's `X`), the second `y` (`Y`). `J` is the raw
interaction (not `J̄ = tanh J`), `a`, `b` are the fields. -/
noncomputable def magY (J a b : ℝ) (x : Bool) : ℝ :=
  condGivenX J a b (fun _ y => spinValue y) x

end RankOneSK


