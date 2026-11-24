-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_IsIntegralOfMemCompo
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_IsIntegralOfMemCompo
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T21:54:00.146803+00:00
-- url     : https://prove2.me/theorems/9b4f6a0f-47a2-4fd0-b03e-4920820f7f25
-- title:
--   Is Integral Of Mem Compo
-- statement:
--   Definitions and structural lemmas for Is Integral Of Mem Compo, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/IsIntegralOfMemCompo.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
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
namespace PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
def compo (L : Type) [Field L] [NumberField L] : IntermediateField ℚ ℂ :=
  ⨆ φ : L →+* ℂ, φ.toRatAlgHom.fieldRange
instance (φ : L →+* ℂ) : FiniteDimensional ℚ φ.toRatAlgHom.fieldRange :=
  LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField φ.toRatAlgHom).toLinearEquiv
instance : FiniteDimensional ℚ (compo L) := by
  unfold compo; infer_instance
end PI.AlgValsFin.W


