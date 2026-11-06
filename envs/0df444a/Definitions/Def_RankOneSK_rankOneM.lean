-- Prove2me | Definitions.Def_RankOneSK_rankOneM
-- name    : RankOneSK_rankOneM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:21.701801+00:00
-- url     : https://prove2.me/theorems/7061befb-cea2-48b6-aba3-48d5d3b675c9
-- title:
--   Rank-one weight $M(x,y)=(x+s\bar X(y))(y+s\bar Y(x))$
-- statement:
--   For the two-spin measure $\mu_{J,a,b}$ and a real parameter $s$,
--   $$M(x,y)=\big(x+s\bar X(y)\big)\big(y+s\bar Y(x)\big),$$
--   with $\bar X(y)=\mathbb E[X\mid y]$ and $\bar Y(x)=\mathbb E[Y\mid x]$. It is the two-spin version of $M_{ij}$ in Lemma 3.2.
--
--   **Formalization Note** The two spins are Booleans read as $\pm1$; $J$ is the raw interaction (not $\bar J=\tanh J$) and $a,b$ are the fields. The bars in Theorem 3.1 are the conditional means $\bar X(y)$, $\bar Y(x)$ (bold in the source), as (51) on p.29 shows.
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, Theorem 3.1, p.19 and (51), p.29

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_RankOneSK_magX
import Definitions.Def_RankOneSK_magY

open OAI.SKGap

namespace RankOneSK

/-- The rank-one weight `M(x, y) = (x + sX̄(y))(y + sȲ(x))` of the two-spin measure `µ_{J,a,b}`,
where `X̄(y) = E[X | y]` and `Ȳ(x) = E[Y | x]`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, Theorem 3.1, p.19 (`M(x, y) = (x + sX̄)(y + sȲ)`) and (51), p.29
(`M(J̄, x, y) = (x + sX̄(y))(y + sȲ(x))`).

**Formalization Note** The two spins are `Bool` values read as ±1 through `OAI.SKGap.spinValue`
(`true ↦ 1`, `false ↦ −1`); the first is `x` (the paper's `X`), the second `y` (`Y`). `J` is the raw
interaction (not `J̄ = tanh J`), `a`, `b` are the fields. The bars in Theorem 3.1 are the conditional means `X̄(y)`,
`Ȳ(x)` (bold in the PDF), as (51) confirms; they are the two-spin version of `X̄_i(x_{−i})` in
`M_ij` of Lemma 3.2. -/
noncomputable def rankOneM (J a b s : ℝ) (x y : Bool) : ℝ :=
  (spinValue x + s * magX J a b y) * (spinValue y + s * magY J a b x)

end RankOneSK


