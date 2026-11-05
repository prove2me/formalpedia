-- Prove2me | Definitions.Def_TwoWayCVQKD_Protocol
-- name    : TwoWayCVQKD_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:45.210958+00:00
-- url     : https://prove2.me/theorems/314b16bf-8ace-4281-8e16-f39ca77c1775
-- title:
--   The four individual protocols $Hom,Het,Hom^2,Het^2$
-- statement:
--   The four individual protocols compared in the paper: the one-way protocols $Hom$ and $Het$ with homodyne and heterodyne detection, and their two-way extensions $Hom^2$ and $Het^2$.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, p.6, 'General expressions for the secret-key rates'

import Mathlib

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, p.6: the individual protocols
`Hom`, `Het` (one-way) and `Hom²`, `Het²` (two-way). -/
inductive Protocol
  | hom
  | het
  | hom2
  | het2

end TwoWayCVQKD


