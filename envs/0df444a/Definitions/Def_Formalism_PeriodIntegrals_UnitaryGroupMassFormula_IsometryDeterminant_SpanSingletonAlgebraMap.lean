-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:29:30.507352+00:00
-- url     : https://prove2.me/theorems/d8a2ce1b-38db-4f74-bd29-cc33fd68e6d0
-- title:
--   Span Singleton Algebra Map
-- statement:
--   Definitions and structural lemmas for Span Singleton Algebra Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.IsoDetW.Loc
open PI.IsoDetDefs IsDedekindDomain
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K
abbrev mulR (a : K) : K →ₗ[R] K := (LinearMap.mulLeft K a).restrictScalars R
end PI.IsoDetW.Loc


