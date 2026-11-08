-- Prove2me | Definitions.Def_SpencerEight_d8
-- name    : SpencerEight_d8
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:00.064216+00:00
-- url     : https://prove2.me/theorems/bc24065e-9384-4b02-aec0-2b8caf36b307
-- title:
--   Coding reserve $d_8$
-- statement:
--   $$d_8(q):=\frac{q^2}{2}+\frac{q^4}{12}+\frac{q^6}{30}+\frac{q^8}{56},$$ the reserve that the entropy series supplies: $\log2-h((1-q)/2)>d_8(q)$ for $0<q<1$.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 8.14, p.105 (PDF p.105)

import Mathlib

namespace SpencerEight

/-- The coding reserve `d₈(q) := q²/2 + q⁴/12 + q⁶/30 + q⁸/56` (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 8.14, p.105 (PDF p.105)). -/
noncomputable def d8 (q : ℝ) : ℝ := q ^ 2 / 2 + q ^ 4 / 12 + q ^ 6 / 30 + q ^ 8 / 56

end SpencerEight


