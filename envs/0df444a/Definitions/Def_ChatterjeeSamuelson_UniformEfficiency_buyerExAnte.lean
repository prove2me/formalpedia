-- Prove2me | Definitions.Def_ChatterjeeSamuelson_UniformEfficiency_buyerExAnte
-- name    : ChatterjeeSamuelson_UniformEfficiency_buyerExAnte
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T08:30:02.851808+00:00
-- url     : https://prove2.me/theorems/786a7989-dd0e-492d-b147-4452114e1ef0
-- title:
--   The buyer's ex ante expected profit $\pi_b(k)$
-- statement:
--   Under the sealed-offer **Bargaining Rule** with parameter $k$, the seller offers $s = S(v_s)$ and the buyer offers $b = B(v_b)$; if $b \ge s$ the good is sold at price $P = kb + (1-k)s$ and the buyer earns $v_b - P$, otherwise both earn zero.
--
--   Let $v_s$ and $v_b$ be independent and uniform on $[0, \bar v]$. The buyer's **ex ante expected profit**, computed before either reservation price is drawn, is
--
--   $$
--   \pi_b = \mathbb E\Bigl[\mathbf 1\{S(v_s) \le B(v_b)\}\,\bigl(v_b - k B(v_b) - (1-k) S(v_s)\bigr)\Bigr].
--   $$
--
--   **Formalization Note** The expectation is the integral over the product of the two uniform laws on pairs $(v_s, v_b)$. It is not conditional on the buyer's own value. Ties trade.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), DOI 10.1287/opre.31.5.835, p. 838 [PDF 4] Bargaining Rule and profits; p. 842 [PDF 8] Example 1(c)(ii); p. 843 [PDF 9] ("ex ante profit")

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_Shared_unif

open MeasureTheory

namespace ChatterjeeSamuelson.UniformEfficiency

/-- The buyer's ex ante expected profit `π_b(k)` (Chatterjee & Samuelson, *Bargaining under
Incomplete Information*, Oper. Res. 31(5) 1983, §3, Example 1(c)(ii), p. 842 [PDF 8]; p. 843
[PDF 9]: "part c describes each player's ex ante profit prior to the 'draw' of either
reservation price"; profits as on p. 838 [PDF 4]: "v_b − P for the buyer", zero without
agreement).

With `(v_s, v_b)` independent and uniform on `[0, v̄]`, offers `s = S(v_s)`, `b = B(v_b)`, a
sale when `b ≥ s` at price `P = k b + (1 − k) s`:
`buyerExAnte k v̄ S B = E[ 1{S(v_s) ≤ B(v_b)} · (v_b − k B(v_b) − (1 − k) S(v_s)) ]`.

*Formalization Note.* Pairs are ordered `(v_s, v_b)`. Ties trade. The expectation is the
Bochner integral over `unif v̄ ⊗ unif v̄`; it is taken before either value is drawn (ex ante),
not conditional on the buyer's own value. -/
noncomputable def buyerExAnte (k vbar : ℝ) (S B : ℝ → ℝ) : ℝ :=
  ∫ p, (if S p.1 ≤ B p.2 then p.2 - (k * B p.2 + (1 - k) * S p.1) else 0)
    ∂((Shared.unif vbar).prod (Shared.unif vbar))

end ChatterjeeSamuelson.UniformEfficiency


