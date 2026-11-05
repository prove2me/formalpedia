-- Prove2me | Definitions.Def_TwoWayCVQKD_rateDR
-- name    : TwoWayCVQKD_rateDR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:49:41.752506+00:00
-- url     : https://prove2.me/theorems/0b8e5175-7646-4856-985e-990886cd7dfa
-- title:
--   Secret-key rate $R^{\blacktriangleright}$ in direct reconciliation
-- statement:
--   For each individual protocol, at modulation $V$ and under a one-mode Gaussian attack with transmission $T$ and EPR variance $W$, the secret-key rate in direct reconciliation is
--   $$
--   R^{\blacktriangleright}:=I(X_A:X_B)-I(X_A:E).
--   $$
--   Each term is computed from the covariances of the protocol's model: the sources, the entangling cloners, Bob's decoder, and Eve's modes. The two-way protocols use identical resources $\bar V=V-1$.
--
--   **Formalization Note** The arguments are in the order protocol, $V$, $T$, $W$. Rates are in nats.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eq. (6), p.6

import Mathlib
import Definitions.Def_TwoWayCVQKD_Protocol
import Definitions.Def_TwoWayCVQKD_classicalMI
import Definitions.Def_TwoWayCVQKD_holevoInfo
import Definitions.Def_TwoWayCVQKD_aliceQ
import Definitions.Def_TwoWayCVQKD_oneWaySourceCov
import Definitions.Def_TwoWayCVQKD_oneWayEve
import Definitions.Def_TwoWayCVQKD_oneWayHomBob
import Definitions.Def_TwoWayCVQKD_oneWayHetBob
import Definitions.Def_TwoWayCVQKD_twoWaySourceCov
import Definitions.Def_TwoWayCVQKD_twoWayEve
import Definitions.Def_TwoWayCVQKD_twoWayHomBob
import Definitions.Def_TwoWayCVQKD_twoWayHetBob

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eq. (6), p.6: the secret-key
rate in direct reconciliation, `R▶ := I(X_A : X_B) - I(X_A : E)`, of each individual protocol under
a one-mode Gaussian attack `(T, W)` at modulation `V`.

**Formalization Note** `rateDR p V T W`. Each rate is computed from the covariances of the model,
never from a closed form. The two-way protocols use `Vbar = V - 1` (p.9). Rates are in nats.
For `V ≤ 1` the value has no meaning; only `V → ∞` is used. -/
noncomputable def rateDR : Protocol → ℝ → ℝ → ℝ → ℝ
  | .hom, V, T, W =>
      classicalMI (oneWaySourceCov V W) aliceQ (oneWayHomBob T) -
        holevoInfo (oneWaySourceCov V W) (oneWayEve T) aliceQ
  | .het, V, T, W =>
      classicalMI (oneWaySourceCov V W) aliceVar (oneWayHetBob T) -
        holevoInfo (oneWaySourceCov V W) (oneWayEve T) aliceVar
  | .hom2, V, T, W =>
      classicalMI (twoWaySourceCov (V - 1) V W) aliceQ (twoWayHomBob T) -
        holevoInfo (twoWaySourceCov (V - 1) V W) (twoWayEve T) aliceQ
  | .het2, V, T, W =>
      classicalMI (twoWaySourceCov (V - 1) V W) aliceVar (twoWayHetBob T) -
        holevoInfo (twoWaySourceCov (V - 1) V W) (twoWayEve T) aliceVar

end TwoWayCVQKD


