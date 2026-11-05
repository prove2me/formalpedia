-- Prove2me | Definitions.Def_TwoWayCVQKD_asymRateRR
-- name    : TwoWayCVQKD_asymRateRR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:50:16.570995+00:00
-- url     : https://prove2.me/theorems/7186ced4-2f0c-4a78-83ad-67344ec9d9f5
-- title:
--   Asymptotic reverse-reconciliation rate ($V\to\infty$)
-- statement:
--   The reverse-reconciliation rate in the limit of large modulation,
--   $$
--   R^{\blacktriangleleft}_\infty(T,W)=\lim_{V\to+\infty}R^{\blacktriangleleft}(V,T,W),
--   $$
--   which is the rate behind the security thresholds of Figs. 2 and 3.
--
--   **Formalization Note** Lean's `limUnder` is the limit when it exists. The goal theorem concludes that every such limit exists.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, p.2, 'large modulation limit' (p.1) and Figs. 2–3

import Mathlib
import Definitions.Def_TwoWayCVQKD_rateRR
open Filter

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, p.2 and Figs. 2–3: the rate
`R◀` of a protocol in the limit of large modulation `V → +∞`, as a function of `W` at fixed `T`.

**Formalization Note** `limUnder` returns an arbitrary value when the limit does not exist. The goal
theorem concludes the convergence of every rate, so no default value enters its comparisons. -/
noncomputable def asymRateRR (p : Protocol) (T W : ℝ) : ℝ :=
  limUnder atTop (fun V : ℝ => rateRR p V T W)

end TwoWayCVQKD


