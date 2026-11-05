-- Prove2me | Definitions.Def_TwoWayCVQKD_aliceQ
-- name    : TwoWayCVQKD_aliceQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:45.073056+00:00
-- url     : https://prove2.me/theorems/2bc8f6cd-e36c-4e40-af09-4b8b834610b4
-- title:
--   Alice's variable $X_A=Q_A$ of the homodyne protocols
-- statement:
--   In the protocols $Hom$ and $Hom^2$ Alice's variable is the single quadrature value $X_A=Q_A$. The variable $P_A$ is still modulated, but it is not part of $X_A$.
--
--   **Formalization Note** The paper's alternative choice $X_A=P_A$ gives the same rates, by the symmetry of the model between $Q$ and $P$.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, p.1 and p.7

import Mathlib
import Definitions.Def_TwoWayCVQKD_aliceVar

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, p.1 and p.7: `X_A = Q_A` in
the protocols `Hom` and `Hom²`, as a one-component family.

**Formalization Note** The paper's alternative `X_A = P_A` gives the same rates by the `Q`/`P`
symmetry of the model. -/
def aliceQ {R : Type*} [DecidableEq R] : Fin 1 → Fin 2 ⊕ R → ℝ :=
  fun _ => aliceVar 0

end TwoWayCVQKD


