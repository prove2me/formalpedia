-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInCurveComponent
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInCurveComponent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:44.749789+00:00
-- url     : https://prove2.me/theorems/eabd5a7a-fa1d-49f4-b637-ac1fee4e0a23
-- title:
--   St Branch In Curve Component
-- statement:
--   Definitions and structural lemmas for St Branch In Curve Component, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StBranchInCurveComponent.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchNormalisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets Filter Topology
noncomputable section
def BranchInCurveComponent.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c : VarBranch I 1 q),
    ringKrullDim (curveLocalRing I q) = 1 →
      ∃ J ∈ I.minimalPrimes, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) ∧
        ∀ᶠ t in 𝓝 (0 : Fin 1 → ℂ), c.toFun t ∈ zeroSet J
end
end GroundTheory.Heights₂.Heights


