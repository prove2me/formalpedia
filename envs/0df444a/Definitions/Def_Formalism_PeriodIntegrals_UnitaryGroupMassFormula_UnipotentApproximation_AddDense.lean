-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:41.704842+00:00
-- url     : https://prove2.me/theorems/91a293f4-70ba-4685-8e59-376375d024f7
-- title:
--   Add Dense
-- statement:
--   Definitions and structural lemmas for Add Dense, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentApproximation/AddDense.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_MemZeroLocusGLIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnipApproxD.IntegersDenseFiniteAdeles
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
def IsInt (b : FiniteAdeleRing R K) : Prop := ∀ v, b v ∈ v.adicCompletionIntegers K
end PI.UnipApproxD.IntegersDenseFiniteAdeles
namespace PI.UnipApproxD
open NumberField IsDedekindDomain
end PI.UnipApproxD


