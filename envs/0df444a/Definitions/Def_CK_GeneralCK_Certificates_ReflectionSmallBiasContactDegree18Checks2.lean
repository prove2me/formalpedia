-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree18Checks2
-- name    : CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree18Checks2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T06:53:12.693363+00:00
-- url     : https://prove2.me/theorems/889ea89c-bc96-422b-b87b-9850b3296138
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree18Checks2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree18Checks2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree18Checks2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionSmallBiasContactDegree18Checks2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionSmallBiasContactDegree18Checks2.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree18Data

-- ===== source module GeneralCK.Certificates.ReflectionSmallBiasContactDegree18Checks2 =====
section

namespace GeneralCK.Reflection.SmallBiasContactDegrees

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasHalfSumPowers SmallBiasBivariateBase SmallBiasBivariateInverse

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem group18_raw_bound : fineBound 48 group18_raw = true := by
  decide +kernel

theorem group18_result_bound : fineBound 48 group18 = true := by
  decide +kernel

theorem group18_degree0 : equalityCheck (finePart 0 group18_raw) (finePart 0 group18) = true := by
  decide +kernel

theorem group18_degree1 : equalityCheck (finePart 1 group18_raw) (finePart 1 group18) = true := by
  decide +kernel

theorem group18_degree2 : equalityCheck (finePart 2 group18_raw) (finePart 2 group18) = true := by
  decide +kernel

theorem group18_degree3 : equalityCheck (finePart 3 group18_raw) (finePart 3 group18) = true := by
  decide +kernel

theorem group18_degree4 : equalityCheck (finePart 4 group18_raw) (finePart 4 group18) = true := by
  decide +kernel

theorem group18_degree5 : equalityCheck (finePart 5 group18_raw) (finePart 5 group18) = true := by
  decide +kernel

theorem group18_degree6 : equalityCheck (finePart 6 group18_raw) (finePart 6 group18) = true := by
  decide +kernel

theorem group18_degree7 : equalityCheck (finePart 7 group18_raw) (finePart 7 group18) = true := by
  decide +kernel

theorem group18_degree8 : equalityCheck (finePart 8 group18_raw) (finePart 8 group18) = true := by
  decide +kernel

theorem group18_degree9 : equalityCheck (finePart 9 group18_raw) (finePart 9 group18) = true := by
  decide +kernel

theorem group18_degree10 : equalityCheck (finePart 10 group18_raw) (finePart 10 group18) = true := by
  decide +kernel

theorem group18_degree11 : equalityCheck (finePart 11 group18_raw) (finePart 11 group18) = true := by
  decide +kernel

theorem group18_degree12 : equalityCheck (finePart 12 group18_raw) (finePart 12 group18) = true := by
  decide +kernel

theorem group18_degree13 : equalityCheck (finePart 13 group18_raw) (finePart 13 group18) = true := by
  decide +kernel

theorem group18_degree14 : equalityCheck (finePart 14 group18_raw) (finePart 14 group18) = true := by
  decide +kernel

theorem group18_degree15 : equalityCheck (finePart 15 group18_raw) (finePart 15 group18) = true := by
  decide +kernel

theorem group18_degree16 : equalityCheck (finePart 16 group18_raw) (finePart 16 group18) = true := by
  decide +kernel

theorem group18_degree17 : equalityCheck (finePart 17 group18_raw) (finePart 17 group18) = true := by
  decide +kernel

theorem group18_degree18 : equalityCheck (finePart 18 group18_raw) (finePart 18 group18) = true := by
  decide +kernel

theorem group18_degree19 : equalityCheck (finePart 19 group18_raw) (finePart 19 group18) = true := by
  decide +kernel

theorem group18_degree20 : equalityCheck (finePart 20 group18_raw) (finePart 20 group18) = true := by
  decide +kernel

theorem group18_degree21 : equalityCheck (finePart 21 group18_raw) (finePart 21 group18) = true := by
  decide +kernel

theorem group18_degree22 : equalityCheck (finePart 22 group18_raw) (finePart 22 group18) = true := by
  decide +kernel

theorem group18_degree23 : equalityCheck (finePart 23 group18_raw) (finePart 23 group18) = true := by
  decide +kernel

theorem group18_degree24 : equalityCheck (finePart 24 group18_raw) (finePart 24 group18) = true := by
  decide +kernel

theorem group18_degree25 : equalityCheck (finePart 25 group18_raw) (finePart 25 group18) = true := by
  decide +kernel

theorem group18_degree26 : equalityCheck (finePart 26 group18_raw) (finePart 26 group18) = true := by
  decide +kernel

theorem group18_degree27 : equalityCheck (finePart 27 group18_raw) (finePart 27 group18) = true := by
  decide +kernel

theorem group18_degree28 : equalityCheck (finePart 28 group18_raw) (finePart 28 group18) = true := by
  decide +kernel

theorem group18_degree29 : equalityCheck (finePart 29 group18_raw) (finePart 29 group18) = true := by
  decide +kernel

theorem group18_degree30 : equalityCheck (finePart 30 group18_raw) (finePart 30 group18) = true := by
  decide +kernel

theorem group18_degree31 : equalityCheck (finePart 31 group18_raw) (finePart 31 group18) = true := by
  decide +kernel

theorem group18_degree32 : equalityCheck (finePart 32 group18_raw) (finePart 32 group18) = true := by
  decide +kernel

theorem group18_degree33 : equalityCheck (finePart 33 group18_raw) (finePart 33 group18) = true := by
  decide +kernel

theorem group18_degree34 : equalityCheck (finePart 34 group18_raw) (finePart 34 group18) = true := by
  decide +kernel

theorem group18_degree35 : equalityCheck (finePart 35 group18_raw) (finePart 35 group18) = true := by
  decide +kernel

theorem group18_degree36 : equalityCheck (finePart 36 group18_raw) (finePart 36 group18) = true := by
  decide +kernel

theorem group18_degree37 : equalityCheck (finePart 37 group18_raw) (finePart 37 group18) = true := by
  decide +kernel

theorem group18_degree38 : equalityCheck (finePart 38 group18_raw) (finePart 38 group18) = true := by
  decide +kernel

theorem group18_degree39 : equalityCheck (finePart 39 group18_raw) (finePart 39 group18) = true := by
  decide +kernel

theorem group18_degree40 : equalityCheck (finePart 40 group18_raw) (finePart 40 group18) = true := by
  decide +kernel

theorem group18_degree41 : equalityCheck (finePart 41 group18_raw) (finePart 41 group18) = true := by
  decide +kernel

theorem group18_degree42 : equalityCheck (finePart 42 group18_raw) (finePart 42 group18) = true := by
  decide +kernel

theorem group18_degree43 : equalityCheck (finePart 43 group18_raw) (finePart 43 group18) = true := by
  decide +kernel

theorem group18_degree44 : equalityCheck (finePart 44 group18_raw) (finePart 44 group18) = true := by
  decide +kernel

theorem group18_degree45 : equalityCheck (finePart 45 group18_raw) (finePart 45 group18) = true := by
  decide +kernel

theorem group18_degree46 : equalityCheck (finePart 46 group18_raw) (finePart 46 group18) = true := by
  decide +kernel

theorem group18_degree47 : equalityCheck (finePart 47 group18_raw) (finePart 47 group18) = true := by
  decide +kernel


end GeneralCK.Reflection.SmallBiasContactDegrees

end


