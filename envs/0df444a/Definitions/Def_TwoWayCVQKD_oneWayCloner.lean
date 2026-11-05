-- Prove2me | Definitions.Def_TwoWayCVQKD_oneWayCloner
-- name    : TwoWayCVQKD_oneWayCloner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:45:02.024012+00:00
-- url     : https://prove2.me/theorems/099a926d-33c1-4d0f-8383-fb1e279f6cea
-- title:
--   The entangling cloner acting on Alice's signal
-- statement:
--   Alice's signal mode has quadratures $\hat Q_A=Q_A+\hat Q_A|Q_A$ and $\hat P_A=P_A+\hat P_A|P_A$. Eve mixes it with her mode $E$ in an entangling cloner of transmission $T$. This definition gives, for each of the two quadratures, the two beam-splitter outputs: the mode $B$ received by Bob and the mode $E'$ kept by Eve.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, p.7 and Fig. 1 (p.2)

import Mathlib
import Definitions.Def_TwoWayCVQKD_cloner
import Definitions.Def_TwoWayCVQKD_aliceVar
import Definitions.Def_TwoWayCVQKD_OneWaySrc

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, p.7: quadrature `k` of the
entangling cloner of the one-way attack. Its input is Alice's signal `Q̂_A = Q_A + Q̂_A|Q_A`
(`P̂_A = P_A + P̂_A|P_A`) and Eve's mode `E`. The outputs are the modes `B` and `E'`. -/
noncomputable def oneWayCloner (T : ℝ) (k : Fin 2) : (OneWaySrc → ℝ) × (OneWaySrc → ℝ) :=
  cloner T (aliceVar k + Pi.single (Sum.inr (Sum.inl (0, k))) 1)
    (Pi.single (Sum.inr (Sum.inr (Sum.inl (0, k)))) 1)

end TwoWayCVQKD


