-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_HeisNorm
-- name    : Formalism_PeriodIntegrals_HeisNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:02.572811+00:00
-- url     : https://prove2.me/theorems/d0bc3165-3c19-4a52-9c4c-99703e92a891
-- title:
--   Heis Norm
-- statement:
--   Definitions and structural lemmas for Heis Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HeisNorm.lean

import Definitions.Def_Formalism_PeriodIntegrals_HeisDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI
def HeisNorm : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (A : ℝ) (x z : T → I → J → ℂ) (G : (T → I → J → ℂ) → ℂ),
    ‖UG A x G z‖ ^ 2 * Real.exp (-Real.pi * (HfG A z z).re) =
      ‖G (z + x)‖ ^ 2 * Real.exp (-Real.pi * (HfG A (z + x) (z + x)).re)
end PI


