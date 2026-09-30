-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree6Checks3
-- name    : CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree6Checks3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:47:28.826203+00:00
-- url     : https://prove2.me/theorems/13dee06c-28da-44bd-8661-83758fe5936d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Checks3` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Checks3` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Checks3` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Checks3 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionSmallBiasContactDegree6Checks3.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree6Data

-- ===== source module GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Checks3 =====
section

namespace GeneralCK.Reflection.SmallBiasContactDegrees

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasHalfSumPowers SmallBiasBivariateBase SmallBiasBivariateInverse

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem body6_degree46 : equalityCheck (finePart 46 body6_raw) (finePart 46 body6) = true := by
  decide +kernel

theorem body6_degree47 : equalityCheck (finePart 47 body6_raw) (finePart 47 body6) = true := by
  decide +kernel

theorem group6_raw_bound : fineBound 48 group6_raw = true := by
  decide +kernel

theorem group6_result_bound : fineBound 48 group6 = true := by
  decide +kernel

theorem group6_degree0 : equalityCheck (finePart 0 group6_raw) (finePart 0 group6) = true := by
  decide +kernel

theorem group6_degree1 : equalityCheck (finePart 1 group6_raw) (finePart 1 group6) = true := by
  decide +kernel

theorem group6_degree2 : equalityCheck (finePart 2 group6_raw) (finePart 2 group6) = true := by
  decide +kernel

theorem group6_degree3 : equalityCheck (finePart 3 group6_raw) (finePart 3 group6) = true := by
  decide +kernel

theorem group6_degree4 : equalityCheck (finePart 4 group6_raw) (finePart 4 group6) = true := by
  decide +kernel

theorem group6_degree5 : equalityCheck (finePart 5 group6_raw) (finePart 5 group6) = true := by
  decide +kernel

theorem group6_degree6 : equalityCheck (finePart 6 group6_raw) (finePart 6 group6) = true := by
  decide +kernel

theorem group6_degree7 : equalityCheck (finePart 7 group6_raw) (finePart 7 group6) = true := by
  decide +kernel

theorem group6_degree8 : equalityCheck (finePart 8 group6_raw) (finePart 8 group6) = true := by
  decide +kernel

theorem group6_degree9 : equalityCheck (finePart 9 group6_raw) (finePart 9 group6) = true := by
  decide +kernel

theorem group6_degree10 : equalityCheck (finePart 10 group6_raw) (finePart 10 group6) = true := by
  decide +kernel

theorem group6_degree11 : equalityCheck (finePart 11 group6_raw) (finePart 11 group6) = true := by
  decide +kernel

theorem group6_degree12 : equalityCheck (finePart 12 group6_raw) (finePart 12 group6) = true := by
  decide +kernel

theorem group6_degree13 : equalityCheck (finePart 13 group6_raw) (finePart 13 group6) = true := by
  decide +kernel

theorem group6_degree14 : equalityCheck (finePart 14 group6_raw) (finePart 14 group6) = true := by
  decide +kernel

theorem group6_degree15 : equalityCheck (finePart 15 group6_raw) (finePart 15 group6) = true := by
  decide +kernel

theorem group6_degree16 : equalityCheck (finePart 16 group6_raw) (finePart 16 group6) = true := by
  decide +kernel

theorem group6_degree17 : equalityCheck (finePart 17 group6_raw) (finePart 17 group6) = true := by
  decide +kernel

theorem group6_degree18 : equalityCheck (finePart 18 group6_raw) (finePart 18 group6) = true := by
  decide +kernel

theorem group6_degree19 : equalityCheck (finePart 19 group6_raw) (finePart 19 group6) = true := by
  decide +kernel


end GeneralCK.Reflection.SmallBiasContactDegrees

end


