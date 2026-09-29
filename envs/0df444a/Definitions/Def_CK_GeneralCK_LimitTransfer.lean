-- Prove2me | Definitions.Def_CK_GeneralCK_LimitTransfer
-- name    : CK_GeneralCK_LimitTransfer
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:23:33.149762+00:00
-- url     : https://prove2.me/theorems/0aec3e41-4d02-4e09-8fce-d53dc800c567
-- title:
--   Courtade–Kumar proof module `GeneralCK.LimitTransfer` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.LimitTransfer` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.LimitTransfer` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.LimitTransfer (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/LimitTransfer.lean)

import Definitions.Def_CK_GeneralCK_Regularization
import Definitions.Def_GeneralCK_limit_transfer

namespace GeneralCK.LimitTransfer
open scoped BigOperators














theorem regularizedEntropyBound_implies_CK (hBound : RegularizedEntropyBound) :
    GeneralCourtadeKumar := by
  apply Regularization.CK_of_open_lower_half
  intro n f p hp hp'
  have hleft : Continuous (fun eps : ℝ => H (eps + p - 2 * eps * p)) := by
    apply H_continuous.comp
    fun_prop
  have hright : Continuous (fun eps : ℝ =>
      Information.cubeWeight n * (∑ y, H (regularizedPosterior f p eps y)) +
        1 - H (regularizedMean f eps)) := by
    apply Continuous.sub
    · apply Continuous.add _ continuous_const
      apply Continuous.const_mul
      apply continuous_finsetSum
      intro y _
      apply H_continuous.comp
      unfold regularizedPosterior
      fun_prop
    · apply H_continuous.comp
      unfold regularizedMean
      fun_prop
  have hz : (0 : ℝ) ∈ closure (Set.Ioo 0 (1 / 2 : ℝ)) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1 / 2)]
    exact ⟨le_rfl, by norm_num⟩
  have hlim := ContinuousWithinAt.closure_le hz hleft.continuousAt.continuousWithinAt
    hright.continuousAt.continuousWithinAt
    (fun eps heps => hBound n f eps p heps.1 heps.2 hp hp')
  simp only [regularizedPosterior, regularizedMean, mul_zero, zero_mul, sub_zero,
    one_mul, zero_add] at hlim
  rw [Information.mutualInformation_eq]
  linarith

end GeneralCK.LimitTransfer


