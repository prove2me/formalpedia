-- Prove2me | Definitions.Def_TwoWayCVQKD_aliceVar
-- name    : TwoWayCVQKD_aliceVar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:44.411218+00:00
-- url     : https://prove2.me/theorems/8cb1f5c7-1d19-48ba-9d23-e5ae0d14403f
-- title:
--   Alice's classical variables $Q_A,P_A$
-- statement:
--   Alice encodes two independent classical Gaussian variables $Q_A,P_A$. In both the one-way and the two-way model they are the first two source variables. The pair $X_A=\{Q_A,P_A\}$ is Alice's variable in the protocols $Het$ and $Het^2$.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, p.7 (one-way) and p.8 (two-way)

import Mathlib

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, p.7 and p.8: Alice's two
classical Gaussian variables `{Q_A, P_A}` (`0` for `Q_A`, `1` for `P_A`), the `Fin 2` block of the
source variables of both models. This is `X_A` of the heterodyne protocols. -/
def aliceVar {R : Type*} [DecidableEq R] (k : Fin 2) : Fin 2 ⊕ R → ℝ :=
  Pi.single (Sum.inl k) 1

end TwoWayCVQKD


