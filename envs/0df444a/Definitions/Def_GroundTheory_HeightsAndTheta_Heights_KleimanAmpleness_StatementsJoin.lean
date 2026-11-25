-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T05:53:15.606808+00:00
-- url     : https://prove2.me/theorems/7fbf402b-6824-4505-8859-bec7109363b8
-- title:
--   Statements Join
-- statement:
--   Definitions and structural lemmas for Statements Join, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsJoin.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
def VeryAmpleTwistGenerated.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (L G : SubSystem k x Ω),
    (∀ I, ∃ L' : Submodule (chartRing k x I) Ω, L.sub I * L' = 1) →
    (∀ I, ∃ G' : Submodule (chartRing k x I) Ω, G.sub I * G' = 1) →
    IsVeryAmple L → G.Generated → IsVeryAmple (L.twist G)
section Hypotheses
variable (k : Type u) [Field k]
end Hypotheses
end
end GroundTheory.Heights₂.Heights.Kleiman


