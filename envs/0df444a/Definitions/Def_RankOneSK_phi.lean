-- Prove2me | Definitions.Def_RankOneSK_phi
-- name    : RankOneSK_phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:35.910986+00:00
-- url     : https://prove2.me/theorems/2a63915f-8041-42b5-9ccb-b7bfeb29d5f5
-- title:
--   Normalized spin $\varphi(X)=(X-\bar X_0)/\sigma_{X_0}$
-- statement:
--   For a field $a\in\mathbb R$ and a spin $x\in\{\pm1\}$,
--   $$\varphi(x)=\frac{x-\bar X_0}{\sigma_{X_0}},\qquad \bar X_0=\tanh a,\quad \sigma_{X_0}=\sqrt{1-\bar X_0^2},$$
--   the spin centred and scaled by its mean and standard deviation under the product measure $\mu_{0,a,b}$. With $b$ in place of $a$ it is $\varphi(Y)$. The functions $1,\varphi(X),\varphi(Y),\varphi(X)\varphi(Y)$ are an orthonormal basis of functions on $\{\pm1\}^2$ for $\mu_{0,a,b}$.
--
--   **Formalization Note** $\sigma_{X_0}=\operatorname{sech}a>0$ for every real $a$, so the division is never by zero.
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, §4, p.23; §2.2, p.11

import Mathlib
import Definitions.Def_SKHighTemperature

open OAI.SKGap

namespace RankOneSK

/-- The normalized spin `φ(X) = (X − X̄₀)/σ_{X₀}` with `X̄₀ = tanh a` and
`σ_{X₀} = √(1 − X̄₀²)`: mean and standard deviation of `X` under the product measure
`µ_{0,a,b}`. With the field `b` in place of `a` it is `φ(Y) = (Y − Ȳ₀)/σ_{Y₀}`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, §4, p.23 (`φ`), and §2.2, p.11 (`X̄₀ = tanh a`, `σ_{X₀} = √(1 − X̄₀²)`).

**Formalization Note** The spin is a `Bool` read as ±1 through `OAI.SKGap.spinValue`.
`σ_{X₀} = sech a > 0` for every real `a`, so the division is never by zero. -/
noncomputable def phi (a : ℝ) (x : Bool) : ℝ :=
  (spinValue x - Real.tanh a) / Real.sqrt (1 - Real.tanh a ^ 2)

end RankOneSK


