-- Prove2me | Definitions.Def_TwoWayCVQKD_rateRR
-- name    : TwoWayCVQKD_rateRR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:49:10.481522+00:00
-- url     : https://prove2.me/theorems/b04e6d29-20d4-4826-b70c-5629a30ebb57
-- title:
--   Secret-key rate $R^{\blacktriangleleft}$ in reverse reconciliation
-- statement:
--   For each individual protocol, at modulation $V$ and under a one-mode Gaussian attack with transmission $T$ and EPR variance $W$, the secret-key rate in reverse reconciliation is
--   $$
--   R^{\blacktriangleleft}:=I(X_A:X_B)-I(X_B:E),\qquad I(X_B:E)=H(E)-H(E|X_B).
--   $$
--   Each term is computed from the covariances of the protocol's model, and Eve's state is conditioned on Bob's variable $X_B$.
--
--   **Formalization Note** The arguments are in the order protocol, $V$, $T$, $W$. Rates are in nats.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eqs. (7), (35), pp.6, 8

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

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eq. (7), p.6: the secret-key
rate in reverse reconciliation, `R◀ := I(X_A : X_B) - I(X_B : E)`, of each individual protocol
under a one-mode Gaussian attack `(T, W)` at modulation `V`.

**Formalization Note** `rateRR p V T W`, computed as `rateDR` with Eve's conditioning variable
`X_B` (Eq. (35)). -/
noncomputable def rateRR : Protocol → ℝ → ℝ → ℝ → ℝ
  | .hom, V, T, W =>
      classicalMI (oneWaySourceCov V W) aliceQ (oneWayHomBob T) -
        holevoInfo (oneWaySourceCov V W) (oneWayEve T) (oneWayHomBob T)
  | .het, V, T, W =>
      classicalMI (oneWaySourceCov V W) aliceVar (oneWayHetBob T) -
        holevoInfo (oneWaySourceCov V W) (oneWayEve T) (oneWayHetBob T)
  | .hom2, V, T, W =>
      classicalMI (twoWaySourceCov (V - 1) V W) aliceQ (twoWayHomBob T) -
        holevoInfo (twoWaySourceCov (V - 1) V W) (twoWayEve T) (twoWayHomBob T)
  | .het2, V, T, W =>
      classicalMI (twoWaySourceCov (V - 1) V W) aliceVar (twoWayHetBob T) -
        holevoInfo (twoWaySourceCov (V - 1) V W) (twoWayEve T) (twoWayHetBob T)

end TwoWayCVQKD


