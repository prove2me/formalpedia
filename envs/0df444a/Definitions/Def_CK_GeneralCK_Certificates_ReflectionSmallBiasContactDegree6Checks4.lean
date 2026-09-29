-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree6Checks4
-- name    : CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree6Checks4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T06:23:47.466101+00:00
-- url     : https://prove2.me/theorems/0f518ae3-19c7-44d0-a6c2-b1b5027e2d36
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Checks4` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Checks4` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Checks4` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Checks4 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionSmallBiasContactDegree6Checks4.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree6Data

-- ===== source module GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Checks4 =====
section

namespace GeneralCK.Reflection.SmallBiasContactDegrees

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasHalfSumPowers SmallBiasBivariateBase SmallBiasBivariateInverse

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem group6_degree20 : equalityCheck (finePart 20 group6_raw) (finePart 20 group6) = true := by
  decide +kernel

theorem group6_degree21 : equalityCheck (finePart 21 group6_raw) (finePart 21 group6) = true := by
  decide +kernel

theorem group6_degree22 : equalityCheck (finePart 22 group6_raw) (finePart 22 group6) = true := by
  decide +kernel

theorem group6_degree23 : equalityCheck (finePart 23 group6_raw) (finePart 23 group6) = true := by
  decide +kernel

theorem group6_degree24 : equalityCheck (finePart 24 group6_raw) (finePart 24 group6) = true := by
  decide +kernel

theorem group6_degree25 : equalityCheck (finePart 25 group6_raw) (finePart 25 group6) = true := by
  decide +kernel

theorem group6_degree26 : equalityCheck (finePart 26 group6_raw) (finePart 26 group6) = true := by
  decide +kernel

theorem group6_degree27 : equalityCheck (finePart 27 group6_raw) (finePart 27 group6) = true := by
  decide +kernel

theorem group6_degree28 : equalityCheck (finePart 28 group6_raw) (finePart 28 group6) = true := by
  decide +kernel

theorem group6_degree29 : equalityCheck (finePart 29 group6_raw) (finePart 29 group6) = true := by
  decide +kernel

theorem group6_degree30 : equalityCheck (finePart 30 group6_raw) (finePart 30 group6) = true := by
  decide +kernel

theorem group6_degree31 : equalityCheck (finePart 31 group6_raw) (finePart 31 group6) = true := by
  decide +kernel

theorem group6_degree32 : equalityCheck (finePart 32 group6_raw) (finePart 32 group6) = true := by
  decide +kernel

theorem group6_degree33 : equalityCheck (finePart 33 group6_raw) (finePart 33 group6) = true := by
  decide +kernel

theorem group6_degree34 : equalityCheck (finePart 34 group6_raw) (finePart 34 group6) = true := by
  decide +kernel

theorem group6_degree35 : equalityCheck (finePart 35 group6_raw) (finePart 35 group6) = true := by
  decide +kernel

theorem group6_degree36 : equalityCheck (finePart 36 group6_raw) (finePart 36 group6) = true := by
  decide +kernel

theorem group6_degree37 : equalityCheck (finePart 37 group6_raw) (finePart 37 group6) = true := by
  decide +kernel

theorem group6_degree38 : equalityCheck (finePart 38 group6_raw) (finePart 38 group6) = true := by
  decide +kernel

theorem group6_degree39 : equalityCheck (finePart 39 group6_raw) (finePart 39 group6) = true := by
  decide +kernel

theorem group6_degree40 : equalityCheck (finePart 40 group6_raw) (finePart 40 group6) = true := by
  decide +kernel

theorem group6_degree41 : equalityCheck (finePart 41 group6_raw) (finePart 41 group6) = true := by
  decide +kernel

theorem group6_degree42 : equalityCheck (finePart 42 group6_raw) (finePart 42 group6) = true := by
  decide +kernel

theorem group6_degree43 : equalityCheck (finePart 43 group6_raw) (finePart 43 group6) = true := by
  decide +kernel


end GeneralCK.Reflection.SmallBiasContactDegrees

end


