-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_ThGExist
-- name    : Formalism_PeriodIntegrals_ThGExist
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:01.233804+00:00
-- url     : https://prove2.me/theorems/875a7a6a-f4f6-4b04-a64c-7b9eec23c8eb
-- title:
--   Th GExist
-- statement:
--   Definitions and structural lemmas for Th GExist, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ThGExist.lean

import Definitions.Def_Formalism_PeriodIntegrals_ThGDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI
def ThGExist : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ La' : AddSubgroup (T → I → J → ℂ), GoodLat s A La' →
      ∃ G ∈ ThSpG s A La', G ≠ 0
end PI


