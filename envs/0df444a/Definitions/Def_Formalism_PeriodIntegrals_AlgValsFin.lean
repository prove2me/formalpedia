-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_AlgValsFin
-- name    : Formalism_PeriodIntegrals_AlgValsFin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:45.380689+00:00
-- url     : https://prove2.me/theorems/9874b613-f3b1-4773-8b9a-c206af6f725b
-- title:
--   Alg Vals Fin
-- statement:
--   Definitions and structural lemmas for Alg Vals Fin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/AlgValsFin.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host
namespace PI.AlgValsFin
def AlgValsFin (L : Type) [Field L] [NumberField L] : Prop :=
  ∀ (χ : HChar L) (s : ℝ) (m : (L →+* ℂ) → ℤ),
    (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) * ∏ φ : L →+* ℂ, ((‖φ (k : L)‖ : ℝ) : ℂ) ^ (s : ℂ) = ∏ φ : L →+* ℂ, φ (k : L) ^ m φ) →
    ∃ C : Subfield ℂ, FiniteDimensional ℚ C ∧ χ.ValuesIn s C.subtype
end PI.AlgValsFin


