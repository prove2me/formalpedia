-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleEmbedSectionsSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleEmbedSectionsSt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:15:40.12784+00:00
-- url     : https://prove2.me/theorems/a23d39cd-fec2-4ffc-bda5-eade4dccd5ba
-- title:
--   Very Ample Embed Sections St
-- statement:
--   Definitions and structural lemmas for Very Ample Embed Sections St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/VeryAmpleEmbedSectionsSt.lean

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
open MvPolynomial Filter
noncomputable section
universe u v w
def VeryAmpleEmbed.Sections.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (y : Fin (N + 1) → Ω)
    (Q : LineBundle k y) (r : ℕ) (h : Fin (r + 1) → Ω), y ≠ 0 → IsVeryAmpleBy Q.toSubSystem h →
    ∀ m : ℕ, (Q.toSubSystem.pow m).secs = (twistSys k h (m : ℤ)).secs
end
end GroundTheory.Heights₂.Heights.Kleiman


