-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailLinearSeparation
-- name    : CK_GeneralCK_PureGapDoubleCapLowTailLinearSeparation
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T01:22:46.0291+00:00
-- url     : https://prove2.me/theorems/2689a5a3-c251-408c-a37a-ae80f5d66280
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapLowTailLinearSeparation` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapLowTailLinearSeparation` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapLowTailLinearSeparation` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapLowTailLinearSeparation (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapLowTailLinearSeparation.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailSeparationQuotient

-- ===== source module GeneralCK.PureGapDoubleCapLowTailLinearSeparation =====
section

/-! The checked coupled contact separation is proportional to the low-cap
mean-bias displacement `2m`. The low-slope sign still needs an independent
cancellation estimate. -/

namespace GeneralCK

open Reflection Certificates.Reflection

theorem doubleCapLowTail_bias_separation_linear {m : ℝ}
    (hm : 0 < m) (hmq : m ≤ 1 / 4) :
    doubleCapLowTailY m - doubleCapLowTailC m ≤
      (2 * m * (doubleCapLowTailC m) ^ 2 *
        biasE (doubleCapLowTailY m)) /
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
  have hh : 0 < H (2 * m) / 2 :=
    div_pos (H_pos (by linarith) (by linarith)) two_pos
  have hh1 : H (2 * m) / 2 < 1 :=
    (doubleCapLowFloor_lt_entropyCap hm hmq).trans_le (H_le_one m)
  have hy1 : doubleCapLowTailY m < 1 := by
    dsimp [doubleCapLowTailY]
    linarith [entropyInverse_pos hh hh1.le]
  have hEy : 0 < biasE (doubleCapLowTailY m) := by
    rw [doubleCapLowTailY_entropy hm hmq]
    exact mul_pos log_two_pos hh
  have hgap : doubleCapLowTailY m - (1 - 2 * m) ≤ 2 * m := by linarith
  have hnum :
      (doubleCapLowTailY m - (1 - 2 * m)) *
      (doubleCapLowTailC m) ^ 2 * biasE (doubleCapLowTailY m) ≤
        2 * m * (doubleCapLowTailC m) ^ 2 *
          biasE (doubleCapLowTailY m) := by
    have hcSq : 0 ≤ (doubleCapLowTailC m) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hgap
      (mul_nonneg hcSq hEy.le)]
  exact (doubleCapLowTail_bias_separation_quotient hm hmq).trans
    (div_le_div_of_nonneg_right hnum hden.le)

#print axioms doubleCapLowTail_bias_separation_linear

end GeneralCK

end


