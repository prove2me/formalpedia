-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_WOnLatG
-- name    : Formalism_PeriodIntegrals_WOnLatG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:52.252653+00:00
-- url     : https://prove2.me/theorems/8b87362a-1533-42d1-b96b-a0f0a98bf47c
-- title:
--   WOn Lat G
-- statement:
--   Definitions and structural lemmas for WOn Lat G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/WOnLatG.lean

import Definitions.Def_Formalism_PeriodIntegrals_WPhDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI
open WPhDefs
def WOnLatG : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ) (La' : AddSubgroup (T → I → J → ℂ)), QIntLat s A La' →
    ∀ p : ℕ, p.Prime → ∀ x ∈ La', wPhG s A p x = alG s A x
end PI


