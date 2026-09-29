-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree6Checks5
-- name    : CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree6Checks5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T06:22:25.204766+00:00
-- url     : https://prove2.me/theorems/13e0c494-d0df-4999-a671-0ee664ae0aed
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Checks5` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Checks5` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Checks5` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Checks5 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionSmallBiasContactDegree6Checks5.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree6Data

-- ===== source module GeneralCK.Certificates.ReflectionSmallBiasContactDegree6Checks5 =====
section

namespace GeneralCK.Reflection.SmallBiasContactDegrees

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasHalfSumPowers SmallBiasBivariateBase SmallBiasBivariateInverse

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem group6_degree44 : equalityCheck (finePart 44 group6_raw) (finePart 44 group6) = true := by
  decide +kernel

theorem group6_degree45 : equalityCheck (finePart 45 group6_raw) (finePart 45 group6) = true := by
  decide +kernel

theorem group6_degree46 : equalityCheck (finePart 46 group6_raw) (finePart 46 group6) = true := by
  decide +kernel

theorem group6_degree47 : equalityCheck (finePart 47 group6_raw) (finePart 47 group6) = true := by
  decide +kernel


end GeneralCK.Reflection.SmallBiasContactDegrees

end


