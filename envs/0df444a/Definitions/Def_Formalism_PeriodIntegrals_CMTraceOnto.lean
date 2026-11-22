-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_CMTraceOnto
-- name    : Formalism_PeriodIntegrals_CMTraceOnto
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:27.509716+00:00
-- url     : https://prove2.me/theorems/cb86cfad-a6b5-4909-90fc-c6306c17e941
-- title:
--   CMTrace Onto
-- statement:
--   Definitions and structural lemmas for CMTrace Onto, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/CMTraceOnto.lean

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
open NumberField
def IsCMUnram (K : Type*) [Field K] [NumberField K] [StarRing K] : Prop :=
  IsTotallyComplex K ∧ (∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a)) ∧
    ∀ P : Ideal (RingOfIntegers K), P.IsMaximal →
      ∃ θ t : RingOfIntegers K, algebraMap (RingOfIntegers K) K t =
        star (algebraMap (RingOfIntegers K) K θ) ∧ θ - t ∉ P
def CMTraceOnto : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], IsCMUnram K →
    ∀ a : 𝓞 K, star (a : K) = (a : K) → ∃ x y : 𝓞 K, (y : K) = star (x : K) ∧ x + y = a
end PI
end


