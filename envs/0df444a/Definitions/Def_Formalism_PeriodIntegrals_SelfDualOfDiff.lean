-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_SelfDualOfDiff
-- name    : Formalism_PeriodIntegrals_SelfDualOfDiff
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T21:21:05.496255+00:00
-- url     : https://prove2.me/theorems/0301e6cb-3610-4ad8-a140-61a4232916ad
-- title:
--   Self Dual Of Diff
-- statement:
--   Definitions and structural lemmas for Self Dual Of Diff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/SelfDualOfDiff.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
namespace PI.KerIso
def SelfDualOfDiff : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E) (𝔟 𝔟c : Ideal (𝓞 E)),
    IsConj K cj → (∀ x : 𝓞 E, x ∈ 𝔟c ↔ ∃ y ∈ 𝔟, cj (y : E) = (x : E)) →
    differentIdeal (𝓞 K) (𝓞 E) = 𝔟 * 𝔟c →
      SelfDualI K cj ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹)
def SplitOfJacobi : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E) (d p : ℕ) (s : K),
    d % 8 = 7 → s * s = -(d : K) → cj (algebraMap K E s) = -algebraMap K E s → p.Prime →
    (p = 2 ∨ jacobiSym (-(d : ℤ)) p = 1) → SplitsAt K cj p
end PI.KerIso


