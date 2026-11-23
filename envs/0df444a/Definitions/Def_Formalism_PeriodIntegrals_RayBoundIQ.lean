-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_RayBoundIQ
-- name    : Formalism_PeriodIntegrals_RayBoundIQ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:52.537689+00:00
-- url     : https://prove2.me/theorems/f4654786-474a-4c53-8ce6-4028a00e876e
-- title:
--   Ray Bound IQ
-- statement:
--   Definitions and structural lemmas for Ray Bound IQ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/RayBoundIQ.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
namespace PI
def RayBoundIQ : Prop :=
  ∀ (K0 : Type) [Field K0] [NumberField K0], Module.finrank ℚ K0 = 2 → IsEmpty (K0 →+* ℝ) →
    ∀ qq : Ideal (𝓞 K0), qq ≠ ⊥ →
      1 ≤ Nat.card (Quot (fun I J : {I : Ideal (𝓞 K0) // I ≠ ⊥ ∧ I ⊔ qq = ⊤} =>
        ∃ a b : 𝓞 K0, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ qq ∧ b - 1 ∈ qq ∧
          (∀ σ : K0 →+* ℝ, 0 < σ (a : K0) ∧ 0 < σ (b : K0)) ∧
          Ideal.span {a} * I.1 = Ideal.span {b} * J.1)) ∧
      (Nat.card (Quot (fun I J : {I : Ideal (𝓞 K0) // I ≠ ⊥ ∧ I ⊔ qq = ⊤} =>
        ∃ a b : 𝓞 K0, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ qq ∧ b - 1 ∈ qq ∧
          (∀ σ : K0 →+* ℝ, 0 < σ (a : K0) ∧ 0 < σ (b : K0)) ∧
          Ideal.span {a} * I.1 = Ideal.span {b} * J.1)) : ℝ) ≤
        4 * |(discr K0 : ℝ)| * (Ideal.absNorm qq : ℝ)
end PI


