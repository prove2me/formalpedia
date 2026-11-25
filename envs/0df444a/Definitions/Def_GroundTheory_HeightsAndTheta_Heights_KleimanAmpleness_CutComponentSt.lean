-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutComponentSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutComponentSt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:22:13.42956+00:00
-- url     : https://prove2.me/theorems/3011da14-a666-4f03-bbc5-ad4d3e2ef415
-- title:
--   Cut Component St
-- statement:
--   Definitions and structural lemmas for Cut Component St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CutComponentSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
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
def CutComponent.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : LineBundle k x) (s : Ω), IsSubvar x pp (n + 1) →
    IsVeryAmple L.toSubSystem → s ∈ L.secs → (∃ I, s ∉ (L.twist (idealSys x pp)).sub I) →
    ∃ qq ∈ (pp ⊔ zeroIdeal L.toSubSystem s).minimalPrimes, IsSubvar x qq n
end
end GroundTheory.Heights₂.Heights.Kleiman


