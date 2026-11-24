-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHomogDimZeroPow
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHomogDimZeroPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:01.898032+00:00
-- url     : https://prove2.me/theorems/99aeeaf6-0746-40e5-af3e-56af3c7dd86d
-- title:
--   St Homog Dim Zero Pow
-- statement:
--   Definitions and structural lemmas for St Homog Dim Zero Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StHomogDimZeroPow.lean

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
attribute [local instance] MvPolynomial.gradedAlgebra
def HomogDimZeroPow.Statement : Prop :=
  ∀ (n : ℕ) (K : Ideal (MvPolynomial (Fin n) ℂ)),
    K.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ K) ≤ 0 → ∃ N : ℕ, originIdeal n ^ N ≤ K
end
end GroundTheory.Heights₂.Heights.ComplexSets


