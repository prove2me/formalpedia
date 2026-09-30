-- Prove2me | Definitions.Def_ChatterjeeSamuelson_UniformEfficiency_sellerExAnte
-- name    : ChatterjeeSamuelson_UniformEfficiency_sellerExAnte
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T08:21:52.855986+00:00
-- url     : https://prove2.me/theorems/506d8bf2-c4ad-4bb7-8f7c-ba936d48dd81
-- title:
--   The seller's ex ante expected profit $\pi_s(k)$
-- statement:
--   Under the sealed-offer **Bargaining Rule** with parameter $k$, the seller offers $s = S(v_s)$ and the buyer offers $b = B(v_b)$; if $b \ge s$ the good is sold at price $P = kb + (1-k)s$ and the seller earns $P - v_s$, otherwise both earn zero.
--
--   Let $v_s$ and $v_b$ be independent and uniform on $[0, \bar v]$. The seller's **ex ante expected profit**, computed before either reservation price is drawn, is
--
--   $$
--   \pi_s = \mathbb E\Bigl[\mathbf 1\{S(v_s) \le B(v_b)\}\,\bigl(k B(v_b) + (1-k) S(v_s) - v_s\bigr)\Bigr].
--   $$
--
--   **Formalization Note** The expectation is the integral over the product of the two uniform laws on pairs $(v_s, v_b)$. It is not conditional on the seller's own value (that interim profit is a different quantity). Ties trade.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), DOI 10.1287/opre.31.5.835, p. 838 [PDF 4] Bargaining Rule and profits; p. 842 [PDF 8] Example 1(c)(i); p. 843 [PDF 9] ("ex ante profit")

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_Shared_unif

open MeasureTheory

namespace ChatterjeeSamuelson.UniformEfficiency

/-- The seller's ex ante expected profit `π_s(k)` (Chatterjee & Samuelson, *Bargaining under
Incomplete Information*, Oper. Res. 31(5) 1983, §3, Example 1(c)(i), p. 842 [PDF 8]; p. 843
[PDF 9]: "part c describes each player's ex ante profit prior to the 'draw' of either
reservation price"; profits as on p. 838 [PDF 4]: "P − v_s for the seller", zero without
agreement).

With `(v_s, v_b)` independent and uniform on `[0, v̄]`, offers `s = S(v_s)`, `b = B(v_b)`, a
sale when `b ≥ s` at price `P = k b + (1 − k) s`:
`sellerExAnte k v̄ S B = E[ 1{S(v_s) ≤ B(v_b)} · (k B(v_b) + (1 − k) S(v_s) − v_s) ]`.

*Formalization Note.* Pairs are ordered `(v_s, v_b)`. Ties trade. The expectation is the
Bochner integral over `unif v̄ ⊗ unif v̄`; it is taken before either value is drawn (ex ante),
not conditional on the seller's own value. -/
noncomputable def sellerExAnte (k vbar : ℝ) (S B : ℝ → ℝ) : ℝ :=
  ∫ p, (if S p.1 ≤ B p.2 then k * B p.2 + (1 - k) * S p.1 - p.1 else 0)
    ∂((Shared.unif vbar).prod (Shared.unif vbar))

end ChatterjeeSamuelson.UniformEfficiency


