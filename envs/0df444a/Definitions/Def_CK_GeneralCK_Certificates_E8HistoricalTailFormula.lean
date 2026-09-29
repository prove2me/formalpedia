-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8HistoricalTailFormula
-- name    : CK_GeneralCK_Certificates_E8HistoricalTailFormula
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:20:18.727796+00:00
-- url     : https://prove2.me/theorems/4d488a6a-ec02-4370-b09d-51dbec9aff35
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8HistoricalTailFormula` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8HistoricalTailFormula` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8HistoricalTailFormula` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8HistoricalTailFormula (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8HistoricalTailFormula.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8RegularizedLog1p

-- ===== source module GeneralCK.Certificates.E8HistoricalTailFormula =====
section

/-!
# Exact `(v,u)` formula used by the historical E8 tail certificate

This is a literal algebraic transcription of `cert_theta_tail.cpp`, with
`log (1 + u) / u` replaced by its sound removable extension.  The old C++
code used a total-order-three centred jet to reduce interval wrapping.  For
a Lean replay one may instead evaluate the expressions below directly from
the value/first-derivative box in `E8RegularizedLog1p`: only the first partial
derivatives of `E` enter `Dalpha E`.
-/

namespace GeneralCK.Certificates.E8HistoricalTailFormula

open E8RegularizedLog1p

noncomputable def r (u : ℝ) : ℝ := (1 - u) / (1 + u)
noncomputable def rPrime (u : ℝ) : ℝ := -2 / (1 + u) ^ 2

noncomputable def B (v u : ℝ) : ℝ :=
  1 + v * u * regLog1p u

noncomputable def Bv (_v u : ℝ) : ℝ := u * regLog1p u
noncomputable def Bu (v u : ℝ) : ℝ :=
  v * (regLog1p u + u * regLog1pPrime u)

noncomputable def G (v u : ℝ) : ℝ :=
  v * regLog1p u + 2 / (1 + u)

noncomputable def Gv (_v u : ℝ) : ℝ := regLog1p u
noncomputable def Gu (v u : ℝ) : ℝ :=
  v * regLog1pPrime u - 2 / (1 + u) ^ 2

noncomputable def qhDen (v u : ℝ) : ℝ := (1 + u) ^ 2 * G v u
noncomputable def qh (v u : ℝ) : ℝ := 4 / qhDen v u

noncomputable def qhV (v u : ℝ) : ℝ :=
  -4 * ((1 + u) ^ 2 * Gv v u) / qhDen v u ^ 2

noncomputable def qhU (v u : ℝ) : ℝ :=
  -4 * (2 * (1 + u) * G v u + (1 + u) ^ 2 * Gu v u) /
    qhDen v u ^ 2

noncomputable def C (v u : ℝ) : ℝ :=
  2 * B v u - v * r u ^ 2

noncomputable def Cv (v u : ℝ) : ℝ :=
  2 * Bv v u - r u ^ 2

noncomputable def Cu (v u : ℝ) : ℝ :=
  2 * Bu v u - 2 * v * r u * rPrime u

/-- Historical `E = (log (Y'/X'))'`. -/
noncomputable def E (v u : ℝ) : ℝ :=
  -3 * qh v u + 2 * v * r u ^ 3 / C v u + 4 * r u -
    3 * v * r u / B v u

noncomputable def Ev (v u : ℝ) : ℝ :=
  -3 * qhV v u +
    (2 * r u ^ 3 / C v u -
      2 * v * r u ^ 3 * Cv v u / C v u ^ 2) -
    3 * r u / B v u +
    3 * v * r u * Bv v u / B v u ^ 2

noncomputable def Eu (v u : ℝ) : ℝ :=
  -3 * qhU v u +
    2 * v * (3 * r u ^ 2 * rPrime u / C v u -
      r u ^ 3 * Cu v u / C v u ^ 2) +
    4 * rPrime u -
    3 * v * (rPrime u / B v u - r u * Bu v u / B v u ^ 2)

/-- `d/da = -v² d/dv - 2u d/du` under `v=1/a`, `u=exp(-2a)`. -/
noncomputable def Ealpha (v u : ℝ) : ℝ :=
  -(v ^ 2) * Ev v u - 2 * u * Eu v u

/-- Historical `X = (log X')'`. -/
noncomputable def X (v u : ℝ) : ℝ :=
  v * r u / B v u - 2 * r u + 2 * qh v u

/-- The exact tail scalar checked by `cert_theta_tail.cpp`. -/
noncomputable def L (v u : ℝ) : ℝ :=
  E v u ^ 2 - Ealpha v u + E v u * X v u

end GeneralCK.Certificates.E8HistoricalTailFormula

end


