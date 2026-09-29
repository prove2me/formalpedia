-- Prove2me | Definitions.Def_CK_GeneralCK_RemainingBellman
-- name    : CK_GeneralCK_RemainingBellman
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:22:41.110097+00:00
-- url     : https://prove2.me/theorems/1d305a5e-fdbf-47c3-abee-95892f2f1db3
-- title:
--   Courtade–Kumar proof module `GeneralCK.RemainingBellman` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.RemainingBellman` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.RemainingBellman` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.RemainingBellman (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/RemainingBellman.lean)

import Definitions.Def_CK_GeneralCK_SmallMeanRegion
import Definitions.Def_CK_GeneralCK_LowInformationRegion
import Definitions.Def_CK_GeneralCK_ConditionalCK
import Definitions.Def_CK_GeneralCK_EqualMean

namespace GeneralCK

/-- Exact remaining regional premises after removing equal means and the two proved psi regions.
The unequal-mean phi theorem and remaining psi region are explicit hypotheses. -/
theorem finiteHybridBellman_of_remaining_regions
    (hphi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b → μ.a+μ.b ≤ 1 →
      candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost)
    (hpsi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b → μ.a+μ.b ≤ 1 →
      1/16 < μ.a+μ.b → 1/100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost) :
    FiniteHybridBellman := by
  apply finiteHybridBellman_of_canonical
  intro k μ hab hsum
  rcases hab.eq_or_lt with heq | hab'
  · exact μ.equal_mean_hybrid heq
  by_cases hphiActive : psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy
  · exact (hybrid_gap_le_phi hphiActive).trans (hphi k μ hab' hsum)
  have hactive := lt_of_not_ge hphiActive
  by_cases hsmall : μ.a+μ.b ≤ 1/16
  · exact small_mean_hybrid_of_active_psi μ hab hsmall hactive.le
  · by_cases hlow : μ.information ≤ 1/100
    · exact low_information_hybrid_of_active_psi μ hlow hactive.le
    · exact hpsi k μ hab' hsum (lt_of_not_ge hsmall) (lt_of_not_ge hlow) hactive

/-- The approved all-dimensions CK target from the still-open phi and residual psi inputs.
This is a conditional theorem, not an unconditional proof of general CK. -/
theorem generalCourtadeKumar_of_remaining_regions
    (hphi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b → μ.a+μ.b ≤ 1 →
      candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost)
    (hpsi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b → μ.a+μ.b ≤ 1 →
      1/16 < μ.a+μ.b → 1/100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost) :
    GeneralCourtadeKumar :=
  generalCourtadeKumar_of_finiteHybridBellman (finiteHybridBellman_of_remaining_regions hphi hpsi)

end GeneralCK


