-- Prove2me | Definitions.Def_TwoWayCVQKD_oneWayHomBob
-- name    : TwoWayCVQKD_oneWayHomBob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:46:58.464235+00:00
-- url     : https://prove2.me/theorems/d1cf88e3-18ed-4459-978c-7d7833627cea
-- title:
--   Bob's variable $X_B=Q_B$ in $Hom$
-- statement:
--   In the protocol $Hom$ Bob performs homodyne detection and his output variable is $X_B=Q_B=\hat Q_B$.
--
--   **Formalization Note** The paper lets Bob measure $\hat Q$ or $\hat P$; the alternative gives the same rates, by the symmetry of the model between $Q$ and $P$.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, p.7, below Eq. (31), and p.1

import Mathlib
import Definitions.Def_TwoWayCVQKD_oneWayBob

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, p.7: in `Hom`, Bob's output
variable is `Q_B = Q̂_B`.

**Formalization Note** The paper's alternative quadrature `P̂` gives the same rates by the `Q`/`P`
symmetry of the model. -/
noncomputable def oneWayHomBob (T : ℝ) : Fin 1 → OneWaySrc → ℝ :=
  fun _ => oneWayBob T (0, 0)

end TwoWayCVQKD


