-- Prove2me | Definitions.Def_TwoWayCVQKD_TwoWaySrc
-- name    : TwoWayCVQKD_TwoWaySrc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:51.352937+00:00
-- url     : https://prove2.me/theorems/9e9b7823-8869-417a-86e8-cadb9b8adad2
-- title:
--   Source variables of the two-way model
-- statement:
--   The two-way model has six independent Gaussian sources: Alice's classical pair $\{Q_A,P_A\}$, Bob's EPR pair on the modes $B_1,C_1$, the EPR pairs $E_1,E_1''$ and $E_2,E_2''$ of Eve's two independent entangling cloners, and the vacuum modes $0$ and $0'$ of Bob's two heterodyne detections, Eqs. (67)–(68). This definition is the index set of their quadratures.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, p.8, Fig. 5 (p.4) and Eqs. (67)–(68), p.9

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, p.8 and Fig. 5 (p.4): the
source variables of the two-way protocols, in order: Alice's classical `{Q_A, P_A}`; Bob's EPR
modes `B₁, C₁`; the EPR modes `E₁, E₁''` of the first cloner; the EPR modes `E₂, E₂''` of the second
cloner; the heterodyne vacuum modes `0` and `0'` of Eqs. (67)–(68). -/
abbrev TwoWaySrc : Type :=
  Fin 2 ⊕ QuadratureIndex 2 ⊕ QuadratureIndex 2 ⊕ QuadratureIndex 2 ⊕ QuadratureIndex 1 ⊕
    QuadratureIndex 1

end TwoWayCVQKD


