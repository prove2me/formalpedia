-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_QuadDiff
-- name    : Formalism_PeriodIntegrals_QuadDiff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:20.041865+00:00
-- url     : https://prove2.me/theorems/723cf8d7-fb7e-4801-8e7d-c53ebb4aaae9
-- title:
--   Quad Diff
-- statement:
--   Definitions and structural lemmas for Quad Diff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/QuadDiff.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI
open NumberField IntermediateField
def QuadDiff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (d : ℕ) (θ : E), Squarefree d → d % 4 = 3 →
    θ ^ 2 = -(d : E) →
    (((differentIdeal ℤ (𝓞 ℚ⟮θ⟯)).map (algebraMap (𝓞 ℚ⟮θ⟯) (𝓞 E)) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) θ
end PI
end


