-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLeadIdealDim
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLeadIdealDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:03.266814+00:00
-- url     : https://prove2.me/theorems/d3d6b667-b2b8-47f9-a70b-96b7f0e33c5b
-- title:
--   St Lead Ideal Dim
-- statement:
--   Definitions and structural lemmas for St Lead Ideal Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLeadIdealDim.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsConeAvoid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
def LeadIdealDim.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ leadIdeal J) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J)
end
end GroundTheory.Heights₂.Heights.ComplexSets


