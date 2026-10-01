-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailSeparationQuotient
-- name    : CK_GeneralCK_PureGapDoubleCapLowTailSeparationQuotient
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T19:24:33.25267+00:00
-- url     : https://prove2.me/theorems/bcbdd2c2-06f8-40a1-92d2-16017eb2aa9e
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapLowTailSeparationQuotient` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapLowTailSeparationQuotient` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapLowTailSeparationQuotient` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapLowTailSeparationQuotient (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapLowTailSeparationQuotient.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailSeparation

-- ===== source module GeneralCK.PureGapDoubleCapLowTailSeparationQuotient =====
section

/-! Quotient form of the checked true-contact separation inequality. -/

namespace GeneralCK

open Reflection Certificates.Reflection

theorem doubleCapLowTail_bias_separation_quotient {m : ℝ}
    (hm : 0 < m) (hmq : m ≤ 1 / 4) :
    doubleCapLowTailY m - doubleCapLowTailC m ≤
      ((doubleCapLowTailY m - (1 - 2 * m)) *
        (doubleCapLowTailC m) ^ 2 * biasE (doubleCapLowTailY m)) /
        ((1 - 2 * m) ^ 2 * biasB (doubleCapLowTailC m)) := by
  have hk : 0 < 1 - 2 * m := by linarith
  have hbetween := doubleCapLowTailC_between hm hmq
  have hc : 0 < doubleCapLowTailC m := hk.trans hbetween.1
  have hc1 : doubleCapLowTailC m < 1 := by
    have hmem := regularContact_mem
      ((1 - 2 * m) / biasE (doubleCapLowTailY m))
    simpa only [doubleCapLowTailC] using hmem.2
  have hB : 0 < biasB (doubleCapLowTailC m) :=
    biasB_pos_wide (by linarith [hc]) hc1
  have hden : 0 < (1 - 2 * m) ^ 2 * biasB (doubleCapLowTailC m) :=
    mul_pos (sq_pos_of_pos hk) hB
  apply (le_div_iff₀ hden).mpr
  have hpoly := doubleCapLowTail_bias_separation hm hmq
  nlinarith only [hpoly]

#print axioms doubleCapLowTail_bias_separation_quotient

end GeneralCK

end


