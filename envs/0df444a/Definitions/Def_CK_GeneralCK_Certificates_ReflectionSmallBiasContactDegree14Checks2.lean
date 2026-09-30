-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree14Checks2
-- name    : CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree14Checks2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:20:32.737061+00:00
-- url     : https://prove2.me/theorems/37d9cd29-003c-44fe-bcd4-f8da9207cfec
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree14Checks2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree14Checks2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree14Checks2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionSmallBiasContactDegree14Checks2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionSmallBiasContactDegree14Checks2.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree14Data

-- ===== source module GeneralCK.Certificates.ReflectionSmallBiasContactDegree14Checks2 =====
section

namespace GeneralCK.Reflection.SmallBiasContactDegrees

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasHalfSumPowers SmallBiasBivariateBase SmallBiasBivariateInverse

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem group14_raw_bound : fineBound 48 group14_raw = true := by
  decide +kernel

theorem group14_result_bound : fineBound 48 group14 = true := by
  decide +kernel

theorem group14_degree0 : equalityCheck (finePart 0 group14_raw) (finePart 0 group14) = true := by
  decide +kernel

theorem group14_degree1 : equalityCheck (finePart 1 group14_raw) (finePart 1 group14) = true := by
  decide +kernel

theorem group14_degree2 : equalityCheck (finePart 2 group14_raw) (finePart 2 group14) = true := by
  decide +kernel

theorem group14_degree3 : equalityCheck (finePart 3 group14_raw) (finePart 3 group14) = true := by
  decide +kernel

theorem group14_degree4 : equalityCheck (finePart 4 group14_raw) (finePart 4 group14) = true := by
  decide +kernel

theorem group14_degree5 : equalityCheck (finePart 5 group14_raw) (finePart 5 group14) = true := by
  decide +kernel

theorem group14_degree6 : equalityCheck (finePart 6 group14_raw) (finePart 6 group14) = true := by
  decide +kernel

theorem group14_degree7 : equalityCheck (finePart 7 group14_raw) (finePart 7 group14) = true := by
  decide +kernel

theorem group14_degree8 : equalityCheck (finePart 8 group14_raw) (finePart 8 group14) = true := by
  decide +kernel

theorem group14_degree9 : equalityCheck (finePart 9 group14_raw) (finePart 9 group14) = true := by
  decide +kernel

theorem group14_degree10 : equalityCheck (finePart 10 group14_raw) (finePart 10 group14) = true := by
  decide +kernel

theorem group14_degree11 : equalityCheck (finePart 11 group14_raw) (finePart 11 group14) = true := by
  decide +kernel

theorem group14_degree12 : equalityCheck (finePart 12 group14_raw) (finePart 12 group14) = true := by
  decide +kernel

theorem group14_degree13 : equalityCheck (finePart 13 group14_raw) (finePart 13 group14) = true := by
  decide +kernel

theorem group14_degree14 : equalityCheck (finePart 14 group14_raw) (finePart 14 group14) = true := by
  decide +kernel

theorem group14_degree15 : equalityCheck (finePart 15 group14_raw) (finePart 15 group14) = true := by
  decide +kernel

theorem group14_degree16 : equalityCheck (finePart 16 group14_raw) (finePart 16 group14) = true := by
  decide +kernel

theorem group14_degree17 : equalityCheck (finePart 17 group14_raw) (finePart 17 group14) = true := by
  decide +kernel

theorem group14_degree18 : equalityCheck (finePart 18 group14_raw) (finePart 18 group14) = true := by
  decide +kernel

theorem group14_degree19 : equalityCheck (finePart 19 group14_raw) (finePart 19 group14) = true := by
  decide +kernel

theorem group14_degree20 : equalityCheck (finePart 20 group14_raw) (finePart 20 group14) = true := by
  decide +kernel

theorem group14_degree21 : equalityCheck (finePart 21 group14_raw) (finePart 21 group14) = true := by
  decide +kernel

theorem group14_degree22 : equalityCheck (finePart 22 group14_raw) (finePart 22 group14) = true := by
  decide +kernel

theorem group14_degree23 : equalityCheck (finePart 23 group14_raw) (finePart 23 group14) = true := by
  decide +kernel

theorem group14_degree24 : equalityCheck (finePart 24 group14_raw) (finePart 24 group14) = true := by
  decide +kernel

theorem group14_degree25 : equalityCheck (finePart 25 group14_raw) (finePart 25 group14) = true := by
  decide +kernel

theorem group14_degree26 : equalityCheck (finePart 26 group14_raw) (finePart 26 group14) = true := by
  decide +kernel

theorem group14_degree27 : equalityCheck (finePart 27 group14_raw) (finePart 27 group14) = true := by
  decide +kernel

theorem group14_degree28 : equalityCheck (finePart 28 group14_raw) (finePart 28 group14) = true := by
  decide +kernel

theorem group14_degree29 : equalityCheck (finePart 29 group14_raw) (finePart 29 group14) = true := by
  decide +kernel

theorem group14_degree30 : equalityCheck (finePart 30 group14_raw) (finePart 30 group14) = true := by
  decide +kernel

theorem group14_degree31 : equalityCheck (finePart 31 group14_raw) (finePart 31 group14) = true := by
  decide +kernel

theorem group14_degree32 : equalityCheck (finePart 32 group14_raw) (finePart 32 group14) = true := by
  decide +kernel

theorem group14_degree33 : equalityCheck (finePart 33 group14_raw) (finePart 33 group14) = true := by
  decide +kernel

theorem group14_degree34 : equalityCheck (finePart 34 group14_raw) (finePart 34 group14) = true := by
  decide +kernel

theorem group14_degree35 : equalityCheck (finePart 35 group14_raw) (finePart 35 group14) = true := by
  decide +kernel

theorem group14_degree36 : equalityCheck (finePart 36 group14_raw) (finePart 36 group14) = true := by
  decide +kernel

theorem group14_degree37 : equalityCheck (finePart 37 group14_raw) (finePart 37 group14) = true := by
  decide +kernel

theorem group14_degree38 : equalityCheck (finePart 38 group14_raw) (finePart 38 group14) = true := by
  decide +kernel

theorem group14_degree39 : equalityCheck (finePart 39 group14_raw) (finePart 39 group14) = true := by
  decide +kernel

theorem group14_degree40 : equalityCheck (finePart 40 group14_raw) (finePart 40 group14) = true := by
  decide +kernel

theorem group14_degree41 : equalityCheck (finePart 41 group14_raw) (finePart 41 group14) = true := by
  decide +kernel

theorem group14_degree42 : equalityCheck (finePart 42 group14_raw) (finePart 42 group14) = true := by
  decide +kernel

theorem group14_degree43 : equalityCheck (finePart 43 group14_raw) (finePart 43 group14) = true := by
  decide +kernel

theorem group14_degree44 : equalityCheck (finePart 44 group14_raw) (finePart 44 group14) = true := by
  decide +kernel

theorem group14_degree45 : equalityCheck (finePart 45 group14_raw) (finePart 45 group14) = true := by
  decide +kernel

theorem group14_degree46 : equalityCheck (finePart 46 group14_raw) (finePart 46 group14) = true := by
  decide +kernel

theorem group14_degree47 : equalityCheck (finePart 47 group14_raw) (finePart 47 group14) = true := by
  decide +kernel


end GeneralCK.Reflection.SmallBiasContactDegrees

end


