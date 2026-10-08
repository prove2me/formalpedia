-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBias
-- name    : CK_GeneralCK_ReflectionSmallBias
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T04:53:42.072793+00:00
-- url     : https://prove2.me/theorems/1247c5c9-e5f7-4d2b-a63a-0a053315344e
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBias` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBias` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBias` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBias (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBias.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasDifferenceJet
import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasRealAgreement

-- ===== source module GeneralCK.ReflectionSmallBias =====
section

/-! The complete reflection small-bias triangle. -/

namespace GeneralCK.Reflection

theorem curvature_nonneg_small_bias (a b : ℝ) (hb : 0 < b) (hba : b < a) (ha : a ≤ 3/20) :
    0 ≤ curvature a b := by
  have hh := SmallBiasCurvatureAssembly.curvature_nonneg_of_order24
    SmallBiasDifferenceJet.remainder_order24 hb hba ha
  rwa [SmallBiasRealAgreement.deriv2_difference_eq_curvature hb hba ha] at hh

end GeneralCK.Reflection


end


