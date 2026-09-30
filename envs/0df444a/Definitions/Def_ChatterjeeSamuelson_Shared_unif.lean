-- Prove2me | Definitions.Def_ChatterjeeSamuelson_Shared_unif
-- name    : ChatterjeeSamuelson_Shared_unif
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:05:39.688416+00:00
-- url     : https://prove2.me/theorems/805daa27-a545-4ef2-8d20-2faba8067ba1
-- title:
--   The uniform belief on $[0, \bar v]$
-- statement:
--   In Example 1 of Chatterjee and Samuelson both reservation prices lie in $[0, \bar v]$ and both players' beliefs about the opponent's reservation price are uniform: $F_s(v) = F_b(v) = v/\bar v$.
--
--   For $\bar v > 0$, the **uniform belief** $U_{\bar v}$ is the probability measure on $\mathbb R$ obtained by conditioning Lebesgue measure on $[0, \bar v]$:
--
--   $$
--   U_{\bar v}(A) = \frac{\lambda(A \cap [0, \bar v])}{\bar v}.
--   $$
--
--   Its distribution function is $0$ below $0$, $v/\bar v$ on $[0, \bar v]$, and $1$ above $\bar v$.
--
--   In Example 1 this one measure is both the buyer's belief about the seller's value and the seller's belief about the buyer's value.
--
--   This definition is shared by two missions of this series: 2 (the linear equilibrium of the uniform example, Example 1(a), p. 842 [PDF 8], and the check against equations (3a), (3b), pp. 842–843 [PDF 8–9]) and 3 (trade probability and ex ante profits of the uniform example, Example 1(b) and 1(c), p. 842 [PDF 8], with p. 843 [PDF 9]).
--
--   **Formalization Note** Defined as Mathlib's conditional measure `volume[|Icc 0 v̄]`. For $\bar v \le 0$ it is not a probability measure; every statement that uses it assumes $\bar v > 0$.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), https://doi.org/10.1287/opre.31.5.835, p. 842 [PDF 8], §3 Example 1 ("F_s(v) = F_b(v) = v/v̄")

import Mathlib

open MeasureTheory ProbabilityTheory Set

namespace ChatterjeeSamuelson.Shared

/-- The uniform belief on `[0, v̄]` (Chatterjee & Samuelson, *Bargaining under Incomplete
Information*, Oper. Res. 31(5) 1983, §3, Example 1, p. 842 [PDF 8]: "Suppose the parties
bargain under the sealed offer rule with F_s(v) = F_b(v) = v/v̄").

`unif v̄` is Lebesgue measure on `ℝ` conditioned on the interval `[0, v̄]`, i.e.
`(1/v̄) · Lebesgue` restricted to `[0, v̄]`. For `0 < v̄` it is a probability measure whose
distribution function is `v ↦ v / v̄` on `[0, v̄]` (`0` below, `1` above).

*Formalization Note.* In Example 1 both players' beliefs are this measure: the buyer's
belief about the seller's value (`F_b`) and the seller's belief about the buyer's value
(`F_s`). It is Mathlib's conditional measure `volume[|Icc 0 v̄]`
(`ProbabilityTheory.cond`); for `v̄ ≤ 0` it is not a probability measure, and every
statement using it assumes `0 < v̄`. -/
noncomputable def unif (vbar : ℝ) : Measure ℝ :=
  volume[|Icc (0 : ℝ) vbar]

end ChatterjeeSamuelson.Shared


