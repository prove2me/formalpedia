-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSectionHyperplaneAvoid
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSectionHyperplaneAvoid
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:59.762667+00:00
-- url     : https://prove2.me/theorems/7a90468d-cbd2-4215-a199-cecbdcc1ebe8
-- title:
--   St Section Hyperplane Avoid
-- statement:
--   Definitions and structural lemmas for St Section Hyperplane Avoid, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSectionHyperplaneAvoid.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
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
open MvPolynomial
noncomputable section
def SectionHyperplaneAvoid.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    IsProjPrime J → ∃ ℓ : Fin n → ℂ, linForm ℓ ∉ J ∧ ∀ W ∈ (divCycle J u).support, linForm ℓ ∉ W
end
end GroundTheory.Heights₂.Heights


