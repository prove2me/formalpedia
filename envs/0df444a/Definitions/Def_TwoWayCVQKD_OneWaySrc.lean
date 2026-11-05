-- Prove2me | Definitions.Def_TwoWayCVQKD_OneWaySrc
-- name    : TwoWayCVQKD_OneWaySrc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:55.1534+00:00
-- url     : https://prove2.me/theorems/f9796c20-5f20-4e01-91e1-947fb5d02247
-- title:
--   Source variables of the one-way model
-- statement:
--   The one-way model has four independent Gaussian sources: Alice's classical pair $\{Q_A,P_A\}$, the quantum shot noise of her signal mode $A$, Eve's EPR pair on the modes $E,E''$, and the vacuum mode $0$ that Bob's heterodyne detector mixes in, Eq. (32). This definition is the index set of their quadratures.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, p.7, Fig. 1 (p.2) and Eq. (32)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, p.7 and Fig. 1: the source
variables of the one-way protocols, in order: Alice's classical `{Q_A, P_A}`; the shot noise
`Q̂_A|Q_A, P̂_A|P_A` of her signal mode; Eve's EPR modes `E, E''`; Bob's heterodyne vacuum mode `0`
of Eq. (32). -/
abbrev OneWaySrc : Type :=
  Fin 2 ⊕ QuadratureIndex 1 ⊕ QuadratureIndex 2 ⊕ QuadratureIndex 1

end TwoWayCVQKD


