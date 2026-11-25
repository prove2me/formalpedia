-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:22:33.672992+00:00
-- url     : https://prove2.me/theorems/fa4c804e-ada3-578c-b800-ba95f4d2d3e9
-- title:
--   Generated Twist Sys Zero
-- statement:
--   Definitions and structural lemmas for Generated Twist Sys Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/GeneratedTwistSysZero.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
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
def GraphClosed.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (G H : LineBundle k x), G.toSubSystem.Generated → IsVeryAmple H.toSubSystem →
    IsVeryAmple (G.toSubSystem.twist H.toSubSystem)
def PointGenerated.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Q : LineBundle k x), IsSubvar x (primeOf (S := k) x) 0 → Q.toSubSystem.Generated
section Hypotheses
variable (k : Type u) [Field k]
end Hypotheses
end
end GroundTheory.Heights₂.Heights.Kleiman


