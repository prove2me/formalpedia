-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:14.195866+00:00
-- url     : https://prove2.me/theorems/b0491675-234f-4c0e-96b3-10c96e616808
-- title:
--   Sm One Of Not Is Unit
-- statement:
--   Definitions and structural lemmas for Sm One Of Not Is Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/SmOneOfNotIsUnit.lean

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
namespace PI.WADVR
variable {W Q : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q]
  [Algebra W Q] [IsFractionRing W Q]
def Sm (Q : Type*) [Field Q] [Algebra W Q] (ϖ : W) (k : ℤ) (q : Q) : Prop :=
  ∃ c : W, q = algebraMap W Q ϖ ^ k * algebraMap W Q c
variable {ϖ : W}
end PI.WADVR


