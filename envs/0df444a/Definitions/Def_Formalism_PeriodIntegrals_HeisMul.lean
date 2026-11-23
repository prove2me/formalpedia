-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_HeisMul
-- name    : Formalism_PeriodIntegrals_HeisMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:02.993246+00:00
-- url     : https://prove2.me/theorems/67515d15-452d-45ba-984b-2fe802d23588
-- title:
--   Heis Mul
-- statement:
--   Definitions and structural lemmas for Heis Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HeisMul.lean

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
def HeisMul : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (A : ℝ) (x y : T → I → J → ℂ) (G : (T → I → J → ℂ) → ℂ),
    UG A x (UG A y G) =
      fun z => Complex.exp (-((Real.pi : ℂ) * Complex.I) * ((HfG A x y).im : ℂ)) * UG A (x + y) G z
end PI


