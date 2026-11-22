-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementL
-- name    : Formalism_HermitianCurvature_StatementL
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:13:00.4948+00:00
-- url     : https://prove2.me/theorems/f0984fec-f21c-43d2-b345-bfda832c332b
-- title:
--   Statement L
-- statement:
--   Definitions and structural lemmas for Statement L, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementL.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.L
open NumberField
def DualIdealInclusion : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (dd : FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = dd⁻¹ →
    ∀ (ν : ℤ) (g : ℤ), g ≠ 0 → ∀ La : FractionalIdeal (nonZeroDivisors (𝓞 E)) E,
      dd ^ ν * FractionalIdeal.spanSingleton _ ((g : E) ^ 2) ≤ La →
      FractionalIdeal.spanSingleton _ (g : E) * FractionalIdeal.dual ℤ ℚ La ≤
        dd ^ (-(ν + 1)) * FractionalIdeal.spanSingleton _ ((g : E)⁻¹)
def DualLatticeInclusion : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (dd : FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = dd⁻¹ →
    ∀ (ν : ℤ) (g : ℤ), g ≠ 0 → ∀ La : Submodule ℤ E,
      (∀ y ∈ (dd ^ ν * FractionalIdeal.spanSingleton _ ((g : E) ^ 2) :
        FractionalIdeal (nonZeroDivisors (𝓞 E)) E), y ∈ La) →
      ∀ x : E, (∀ y ∈ La, Algebra.trace ℚ E (x * y / g) ∈ (algebraMap ℤ ℚ).range) →
        x ∈ (dd ^ (-(ν + 1)) * FractionalIdeal.spanSingleton _ ((g : E)⁻¹) :
          FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
end Formalism.FourierDecayAlt.L


