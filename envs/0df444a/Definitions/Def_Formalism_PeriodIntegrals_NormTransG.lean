-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_NormTransG
-- name    : Formalism_PeriodIntegrals_NormTransG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:04.133732+00:00
-- url     : https://prove2.me/theorems/4dcb96d8-cedd-4aaf-90e5-5a883723b415
-- title:
--   Norm Trans G
-- statement:
--   Definitions and structural lemmas for Norm Trans G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/NormTransG.lean

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
def NormTransG : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ La' : AddSubgroup (T → I → J → ℂ), GoodLat s A La' → ∀ F ∈ ThSpG s A La', ∀ x : T → I → J → ℂ,
      normSqG A La' (UG A x F) = normSqG A La' F
end PI


