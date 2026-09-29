-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree6Checks2
-- name    : CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree6Checks2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T06:24:01.000671+00:00
-- url     : https://prove2.me/theorems/46e8a197-781a-4df5-a745-c53245e33020
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Checks2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Checks2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Checks2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Checks2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionSmallBiasContactDegree6Checks2.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree6Data

-- ===== source module GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Checks2 =====
section

namespace GeneralCK.Reflection.SmallBiasContactDegrees

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasHalfSumPowers SmallBiasBivariateBase SmallBiasBivariateInverse

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem body6_degree22 : equalityCheck (finePart 22 body6_raw) (finePart 22 body6) = true := by
  decide +kernel

theorem body6_degree23 : equalityCheck (finePart 23 body6_raw) (finePart 23 body6) = true := by
  decide +kernel

theorem body6_degree24 : equalityCheck (finePart 24 body6_raw) (finePart 24 body6) = true := by
  decide +kernel

theorem body6_degree25 : equalityCheck (finePart 25 body6_raw) (finePart 25 body6) = true := by
  decide +kernel

theorem body6_degree26 : equalityCheck (finePart 26 body6_raw) (finePart 26 body6) = true := by
  decide +kernel

theorem body6_degree27 : equalityCheck (finePart 27 body6_raw) (finePart 27 body6) = true := by
  decide +kernel

theorem body6_degree28 : equalityCheck (finePart 28 body6_raw) (finePart 28 body6) = true := by
  decide +kernel

theorem body6_degree29 : equalityCheck (finePart 29 body6_raw) (finePart 29 body6) = true := by
  decide +kernel

theorem body6_degree30 : equalityCheck (finePart 30 body6_raw) (finePart 30 body6) = true := by
  decide +kernel

theorem body6_degree31 : equalityCheck (finePart 31 body6_raw) (finePart 31 body6) = true := by
  decide +kernel

theorem body6_degree32 : equalityCheck (finePart 32 body6_raw) (finePart 32 body6) = true := by
  decide +kernel

theorem body6_degree33 : equalityCheck (finePart 33 body6_raw) (finePart 33 body6) = true := by
  decide +kernel

theorem body6_degree34 : equalityCheck (finePart 34 body6_raw) (finePart 34 body6) = true := by
  decide +kernel

theorem body6_degree35 : equalityCheck (finePart 35 body6_raw) (finePart 35 body6) = true := by
  decide +kernel

theorem body6_degree36 : equalityCheck (finePart 36 body6_raw) (finePart 36 body6) = true := by
  decide +kernel

theorem body6_degree37 : equalityCheck (finePart 37 body6_raw) (finePart 37 body6) = true := by
  decide +kernel

theorem body6_degree38 : equalityCheck (finePart 38 body6_raw) (finePart 38 body6) = true := by
  decide +kernel

theorem body6_degree39 : equalityCheck (finePart 39 body6_raw) (finePart 39 body6) = true := by
  decide +kernel

theorem body6_degree40 : equalityCheck (finePart 40 body6_raw) (finePart 40 body6) = true := by
  decide +kernel

theorem body6_degree41 : equalityCheck (finePart 41 body6_raw) (finePart 41 body6) = true := by
  decide +kernel

theorem body6_degree42 : equalityCheck (finePart 42 body6_raw) (finePart 42 body6) = true := by
  decide +kernel

theorem body6_degree43 : equalityCheck (finePart 43 body6_raw) (finePart 43 body6) = true := by
  decide +kernel

theorem body6_degree44 : equalityCheck (finePart 44 body6_raw) (finePart 44 body6) = true := by
  decide +kernel

theorem body6_degree45 : equalityCheck (finePart 45 body6_raw) (finePart 45 body6) = true := by
  decide +kernel


end GeneralCK.Reflection.SmallBiasContactDegrees

end


