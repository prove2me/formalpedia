-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleSecsSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleSecsSt
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T05:56:25.30367+00:00
-- url     : https://prove2.me/theorems/b5c2f0c9-b33f-480c-8295-c077a47ab426
-- title:
--   Very Ample Secs St
-- statement:
--   Definitions and structural lemmas for Very Ample Secs St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/VeryAmpleSecsSt.lean

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
noncomputable section
universe u w
def VeryAmpleSecs.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Nb : LineBundle k x) (r : ℕ) (h : Fin (r + 1) → Ω), IsVeryAmpleBy Nb.toSubSystem h →
    ∀ n : ℕ, (Nb.toSubSystem.pow n).secs = ((twistSys k h 1).pow n).secs
end
end GroundTheory.Heights₂.Heights.Kleiman


