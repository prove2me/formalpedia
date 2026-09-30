-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8LargeSStableCriterion
-- name    : CK_GeneralCK_PureGapE8LargeSStableCriterion
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T09:01:10.127981+00:00
-- url     : https://prove2.me/theorems/565b63e3-ab45-4cd7-9d21-b6e1cc5e0b91
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8LargeSStableCriterion` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8LargeSStableCriterion` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8LargeSStableCriterion` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8LargeSStableCriterion (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8LargeSStableCriterion.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8LargeSJetCriterion
import Definitions.Def_CK_GeneralCK_PureGapE8StableParameterSurjective

-- ===== source module GeneralCK.PureGapE8LargeSStableCriterion =====
section

/-!
# Stable-parameter certificate interface for E8 logarithmic convexity

This is the final adapter expected by the finite `[0,20]` and analytic-tail
`[20,∞)` certificate: it is enough to establish the jet numerator sign at
`Y a` for every positive stable parameter `a`.
-/

namespace GeneralCK

open Certificates.E8TAxisDeltaDirectionalJet
open Certificates.E8TAxisStableScalar

/-- The exact statement emitted by an alpha-space certificate. -/
def E8StableLogDerivativeJetNumeratorNonnegative : Prop :=
  ∀ a : ℝ, 0 < a → 0 ≤ e8LogDerivativeJetNumerator (Y a)

theorem e8LogDerivativeJetNumeratorNonnegative_of_stable
    (h : E8StableLogDerivativeJetNumeratorNonnegative) :
    E8LogDerivativeJetNumeratorNonnegative := by
  intro y hy
  obtain ⟨a, ha, rfl⟩ := e8SlopeRange_exists_stable_parameter hy
  exact h a ha

theorem e8LargeSStructure_of_stable_jet_numerator
    (h : E8StableLogDerivativeJetNumeratorNonnegative) :
    E8LargeSStructure :=
  e8LargeSStructure_of_jet_numerator
    (e8LogDerivativeJetNumeratorNonnegative_of_stable h)

theorem e8_largeS_of_stable_jet_numerator
    (h : E8StableLogDerivativeJetNumeratorNonnegative) :
    E8PositiveOn (fun s _ => (63 / 20 : ℝ) ≤ s) :=
  e8_largeS_of_jet_numerator
    (e8LogDerivativeJetNumeratorNonnegative_of_stable h)

#print axioms e8LogDerivativeJetNumeratorNonnegative_of_stable
#print axioms e8LargeSStructure_of_stable_jet_numerator
#print axioms e8_largeS_of_stable_jet_numerator

end GeneralCK

end


