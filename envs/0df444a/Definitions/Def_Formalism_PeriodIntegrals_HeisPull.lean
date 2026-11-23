-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_HeisPull
-- name    : Formalism_PeriodIntegrals_HeisPull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:16.861479+00:00
-- url     : https://prove2.me/theorems/80db8904-e205-4ec5-abed-e884a187b239
-- title:
--   Heis Pull
-- statement:
--   Definitions and structural lemmas for Heis Pull, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HeisPull.lean

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
def HeisPull : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (A : ℝ) (ψ : (T → I → J → ℂ) ≃ₗ[ℂ] (T → I → J → ℂ)),
    (∀ z w, HfG A (ψ z) (ψ w) = HfG A z w) → ∀ (x : T → I → J → ℂ) (F : (T → I → J → ℂ) → ℂ),
      (fun z => UG A x F (ψ z)) = UG A (ψ.symm x) (fun z => F (ψ z))
end PI


