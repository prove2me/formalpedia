-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeAvoidsOpen
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeAvoidsOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:43.988663+00:00
-- url     : https://prove2.me/theorems/ca0b54f9-5cd2-41d7-8afa-349767503195
-- title:
--   St Cone Avoids Open
-- statement:
--   Definitions and structural lemmas for St Cone Avoids Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StConeAvoidsOpen.lean

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
def ConeAvoidsOpen.Statement : Prop :=
  ∀ (n d N : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    IsZariskiOpen {A : Matrix (Fin d) (Fin n) ℂ | ConeAvoids J A N}
end
end GroundTheory.Heights₂.Heights.ComplexSets


