-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchImageNhdOffCentre
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchImageNhdOffCentre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:20.055348+00:00
-- url     : https://prove2.me/theorems/6d445c2f-2412-4aaa-8041-f1a87b2b85e5
-- title:
--   St Branch Image Nhd Off Centre
-- statement:
--   Definitions and structural lemmas for St Branch Image Nhd Off Centre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StBranchImageNhdOffCentre.lean

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
def BranchImageNhdOffCentre.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    ringKrullDim (curveLocalRing I q) = 1 →
      ∃ N ∈ 𝓝 q, ∀ c : VarBranch I 1 q, ∀ x ∈ c.image ∩ N, x ≠ q →
        ∃ U ∈ 𝓝 x, zeroSet I ∩ U ⊆ c.image
end
end GroundTheory.Heights₂.Heights


