-- Prove2me | Definitions.Def_ChatterjeeSamuelson_UniformEfficiency_tradeProb
-- name    : ChatterjeeSamuelson_UniformEfficiency_tradeProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T08:13:47.47381+00:00
-- url     : https://prove2.me/theorems/ac633583-7149-4c8b-96d3-04793fae7cb9
-- title:
--   Probability that a bargain is reached
-- statement:
--   Under the sealed-offer **Bargaining Rule** the seller and buyer submit offers $s$ and $b$; if $b \ge s$ a bargain is enacted.
--
--   Let the reservation prices $v_s$ (seller) and $v_b$ (buyer) be independent and uniformly distributed on $[0, \bar v]$, and let the players use offer strategies $S$ and $B$. The **probability that a bargain is reached** is
--
--   $$
--   \Pr\bigl[\,S(v_s) \le B(v_b)\,\bigr],
--   $$
--
--   computed under the product of the two uniform laws on pairs $(v_s, v_b)$.
--
--   **Formalization Note** Pairs are ordered $(v_s, v_b)$. Ties trade. The measure of the event is converted to a real number; if $S$ or $B$ is not measurable the event's outer measure is used. The rule parameter $k$ does not enter the event, so it is not an argument.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), DOI 10.1287/opre.31.5.835, p. 838 [PDF 4] Bargaining Rule; p. 842 [PDF 8] Example 1(b)

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_Shared_unif

open MeasureTheory

namespace ChatterjeeSamuelson.UniformEfficiency

/-- The probability that a bargain is reached (Chatterjee & Samuelson, *Bargaining under
Incomplete Information*, Oper. Res. 31(5) 1983, §3, Example 1(b), p. 842 [PDF 8]; Bargaining
Rule, p. 838 [PDF 4]: "If b ≥ s, a bargain is enacted").

The reservation prices `(v_s, v_b)` are drawn independently, each uniform on `[0, v̄]`; the
seller offers `S(v_s)`, the buyer offers `B(v_b)`, and a bargain is reached when
`S(v_s) ≤ B(v_b)`. `tradeProb v̄ S B` is the probability of that event under the product
measure `unif v̄ ⊗ unif v̄`.

*Formalization Note.* Pairs are ordered `(v_s, v_b)`: `p.1` is the seller's value, `p.2` the
buyer's. Ties `b = s` trade. The probability is real-valued via `ENNReal.toReal` (a
probability, hence finite for `0 < v̄`). The event need not be measurable for arbitrary
`S, B`; the measure is then the outer measure. -/
noncomputable def tradeProb (vbar : ℝ) (S B : ℝ → ℝ) : ℝ :=
  (((Shared.unif vbar).prod (Shared.unif vbar)) {p : ℝ × ℝ | S p.1 ≤ B p.2}).toReal

end ChatterjeeSamuelson.UniformEfficiency


