-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:14.852559+00:00
-- url     : https://prove2.me/theorems/b98780f6-de44-4403-865f-b2076617df62
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ImaginaryQuadraticClassBound/Development.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RayBoundIQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
namespace PI.RayBoundIQW
def rayRel (K0 : Type) [Field K0] [NumberField K0] (qq : Ideal (𝓞 K0))
    (I J : {I : Ideal (𝓞 K0) // I ≠ ⊥ ∧ I ⊔ qq = ⊤}) : Prop :=
  ∃ a b : 𝓞 K0, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ qq ∧ b - 1 ∈ qq ∧
    (∀ σ : K0 →+* ℝ, 0 < σ (a : K0) ∧ 0 < σ (b : K0)) ∧
    Ideal.span {a} * I.1 = Ideal.span {b} * J.1
def FibreBound : Prop :=
  ∀ (K0 : Type) [Field K0] [NumberField K0], IsEmpty (K0 →+* ℝ) →
    ∀ qq : Ideal (𝓞 K0), qq ≠ ⊥ →
      Finite (Quot (rayRel K0 qq)) ∧
        Nat.card (Quot (rayRel K0 qq)) ≤ classNumber K0 * Ideal.absNorm qq
def ClassNumBound : Prop :=
  ∀ (K0 : Type) [Field K0] [NumberField K0], Module.finrank ℚ K0 = 2 → IsEmpty (K0 →+* ℝ) →
    (classNumber K0 : ℝ) ≤ 4 * |(discr K0 : ℝ)|
end PI.RayBoundIQW


