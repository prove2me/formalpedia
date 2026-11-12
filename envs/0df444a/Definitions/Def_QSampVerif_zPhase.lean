-- Prove2me | Definitions.Def_QSampVerif_zPhase
-- name    : QSampVerif_zPhase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:27:06.757285+00:00
-- url     : https://prove2.me/theorems/113d285f-ed9a-4de5-9624-6d0937a402ba
-- title:
--   The phase set $\mathcal Z=\{1,i,-1,-i\}$
-- statement:
--   The phase set $\mathcal Z=\{1,i,-1,-i\}$ of the polarization identities, enumerated as $z_k=i^k$ for $k=0,1,2,3$.
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), (391), p.142 (PDF 143); §13.9, p.178 (PDF 179)

import Mathlib

set_option autoImplicit false

namespace QSampVerif

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), (391)
p.142 and §13.9 p.178: the phase set `Z = {1, i, −1, −i}`, enumerated as `z_k = i^k`,
`k = 0, 1, 2, 3`. -/
noncomputable def zPhase (k : Fin 4) : ℂ := Complex.I ^ (k : ℕ)

end QSampVerif


