-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutZeroNotLeSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutZeroNotLeSt
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:31:01.523839+00:00
-- url     : https://prove2.me/theorems/e1b181f5-acdb-4866-9297-9a4c50d89b4d
-- title:
--   Cut Zero Not Le St
-- statement:
--   Definitions and structural lemmas for Cut Zero Not Le St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CutZeroNotLeSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutComponentSt
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
def CutZeroNotLe.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (e : ℕ) (pp : Ideal (Poly k N)) (L : LineBundle k x) (s : Ω), IsSubvar x pp e →
    s ∈ L.secs → (∃ I, s ∉ (L.twist (idealSys x pp)).sub I) →
    ∃ f ∈ zeroIdeal L.toSubSystem s, f ∉ pp
end
end GroundTheory.Heights₂.Heights.Kleiman


