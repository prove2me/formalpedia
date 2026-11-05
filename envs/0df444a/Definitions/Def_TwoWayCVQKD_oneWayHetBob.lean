-- Prove2me | Definitions.Def_TwoWayCVQKD_oneWayHetBob
-- name    : TwoWayCVQKD_oneWayHetBob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:46:54.786098+00:00
-- url     : https://prove2.me/theorems/fef66e25-94df-44c7-acc5-b0d3ebb81884
-- title:
--   Bob's variable $X_B=\{Q_B,P_B\}$ in $Het$
-- statement:
--   In the protocol $Het$ Bob performs heterodyne detection, and his output variables are
--   $$
--   \{Q_B,P_B\}=2^{-1/2}\{\hat Q_B+\hat Q_0,\ \hat P_B-\hat P_0\},
--   $$
--   where $\hat Q_0,\hat P_0$ are the quadratures of a vacuum mode.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eq. (32), p.7

import Mathlib
import Definitions.Def_TwoWayCVQKD_oneWayBob

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eq. (32), p.7: in `Het`, Bob's
variables are `{Q_B, P_B} = 2^{-1/2} {Q̂_B + Q̂₀, P̂_B - P̂₀}`, with `Q̂₀, P̂₀` belonging to the
vacuum mode `0` of the sources. -/
noncomputable def oneWayHetBob (T : ℝ) : Fin 2 → OneWaySrc → ℝ :=
  ![(Real.sqrt 2)⁻¹ • (oneWayBob T (0, 0) +
      Pi.single (Sum.inr (Sum.inr (Sum.inr (0, 0)))) 1),
    (Real.sqrt 2)⁻¹ • (oneWayBob T (0, 1) -
      Pi.single (Sum.inr (Sum.inr (Sum.inr (0, 1)))) 1)]

end TwoWayCVQKD


