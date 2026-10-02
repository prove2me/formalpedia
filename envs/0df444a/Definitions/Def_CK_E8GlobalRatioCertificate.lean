-- Prove2me | Definitions.Def_CK_E8GlobalRatioCertificate
-- name    : CK_E8GlobalRatioCertificate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:56:17.524877+00:00
-- url     : https://prove2.me/theorems/4eb14f7f-07bf-4e6a-809d-5d73f4c50105
-- title:
--   Courtade–Kumar proof module `E8GlobalRatioCertificate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `E8GlobalRatioCertificate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `E8GlobalRatioCertificate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module E8GlobalRatioCertificate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/E8GlobalRatioCertificate.lean)

import Definitions.Def_CK_E8MiddleCertificate
import Definitions.Def_CK_E8PadeTail

-- ===== source module E8GlobalRatioCertificate =====
section

namespace GeneralCK.E8RatioMonotonicity

open Set Certificates.E8HistoricalLogConvexityBridge

/-- The initial analytic interval, 28 checked middle cells, and the Padé tail
cover the entire positive stable parameter axis. -/
theorem stableL_nonnegative {a : ℝ} (ha : 0 < a) : 0 ≤ stableL a := by
  by_cases hsmall : a ≤ 1 / 4
  · linarith [stableL_ge_three_initial ha hsmall]
  · by_cases hmiddle : a ≤ 3 / 2
    · exact (MiddleCertificate.stableL_pos_middle (le_of_not_ge hsmall) hmiddle).le
    · exact stableL_nonneg_of_three_halves (le_of_not_ge hmiddle)

theorem e8RatioMonotone : MonotoneOn ratio (Ioi 0) :=
  ratio_monotone_iff_stableL_nonneg.mpr (fun _ ha => stableL_nonnegative ha)

theorem e8ReciprocalConvex : ConvexOn ℝ (Ioi 0) reciprocal :=
  reciprocal_convex_iff_ratio_monotone.mpr e8RatioMonotone

theorem e8Theta_ratio_monotone :
    MonotoneOn (fun u : ℝ => -deriv (deriv e8Theta) u / (deriv e8Theta u) ^ 2)
      (Ioi 0) := e8RatioMonotone

theorem e8Theta_reciprocal_convex :
    ConvexOn ℝ (Ioi 0) (fun u : ℝ => 1 / deriv e8Theta u) := by
  have hf : (fun u : ℝ => 1 / deriv e8Theta u) = reciprocal := by
    funext u
    simp only [one_div, reciprocal]
  rw [hf]
  exact e8ReciprocalConvex

theorem e8StableJetNumeratorNonnegative : E8StableLogDerivativeJetNumeratorNonnegative :=
  stable_numerator_nonnegative_iff_ratio_monotone.mpr e8RatioMonotone

theorem e8LargeSStructureCertified : E8LargeSStructure :=
  largeSStructure_of_ratio_monotone e8RatioMonotone

theorem e8LargeSCertified : E8PositiveOn (fun s _ => (63 / 20 : ℝ) ≤ s) :=
  largeS_of_ratio_monotone e8RatioMonotone

#print axioms stableL_nonnegative
#print axioms e8RatioMonotone
#print axioms e8ReciprocalConvex
#print axioms e8Theta_ratio_monotone
#print axioms e8Theta_reciprocal_convex
#print axioms e8StableJetNumeratorNonnegative
#print axioms e8LargeSStructureCertified
#print axioms e8LargeSCertified

end GeneralCK.E8RatioMonotonicity

end


