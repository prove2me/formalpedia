-- Prove2me | Definitions.Def_TwoWayCVQKD_asymRateDR
-- name    : TwoWayCVQKD_asymRateDR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:51:29.746004+00:00
-- url     : https://prove2.me/theorems/32e81665-3bcc-4e42-b545-c877eec0ff5a
-- title:
--   Asymptotic direct-reconciliation rate ($V\to\infty$)
-- statement:
--   The direct-reconciliation rate in the limit of large modulation,
--   $$
--   R^{\blacktriangleright}_\infty(T,W)=\lim_{V\to+\infty}R^{\blacktriangleright}(V,T,W),
--   $$
--   which is the rate behind the security thresholds of Figs. 2 and 3.
--
--   **Formalization Note** Lean's `limUnder` is the limit when it exists. The goal theorem concludes that every such limit exists.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, p.2, 'large modulation limit' (p.1) and Figs. 2–3

import Mathlib
import Definitions.Def_TwoWayCVQKD_rateDR
open Filter

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, p.2 and Figs. 2–3: the rate
`R▶` of a protocol in the limit of large modulation `V → +∞`, as a function of `W` at fixed `T`.

**Formalization Note** `limUnder` returns an arbitrary value when the limit does not exist. The goal
theorem concludes the convergence of every rate, so no default value enters its comparisons. -/
noncomputable def asymRateDR (p : Protocol) (T W : ℝ) : ℝ :=
  limUnder atTop (fun V : ℝ => rateDR p V T W)

end TwoWayCVQKD


