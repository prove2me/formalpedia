-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearFormCut
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearFormCut
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:05.603528+00:00
-- url     : https://prove2.me/theorems/c590f30c-0b3f-43e1-8342-6fba8510e615
-- title:
--   St Linear Form Cut
-- statement:
--   Definitions and structural lemmas for St Linear Form Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLinearFormCut.lean

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
def LinearFormCut.Statement : Prop :=
  ∀ (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
      ∃ B : Matrix (Fin 1) (Fin n) ℂ,
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (I ⊔ linIdeal B)) ≤ (e : WithBot ℕ∞)
end
end GroundTheory.Heights₂.Heights.ComplexSets


