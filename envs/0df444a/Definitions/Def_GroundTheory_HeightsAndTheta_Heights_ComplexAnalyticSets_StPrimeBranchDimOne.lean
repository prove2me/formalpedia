-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeBranchDimOne
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeBranchDimOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:55.535499+00:00
-- url     : https://prove2.me/theorems/5e5f0f8c-73bd-4188-85f7-e590fa71af29
-- title:
--   St Prime Branch Dim One
-- statement:
--   Definitions and structural lemmas for St Prime Branch Dim One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPrimeBranchDimOne.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeBranchPlace
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
open MvPolynomial ComplexSets
def PrimeBranchDimOne.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c : VarBranch J 1 q),
    J.IsPrime → ringKrullDim (curveLocalRing J q) ≤ 1 →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ)
end GroundTheory.Heights₂.Heights


