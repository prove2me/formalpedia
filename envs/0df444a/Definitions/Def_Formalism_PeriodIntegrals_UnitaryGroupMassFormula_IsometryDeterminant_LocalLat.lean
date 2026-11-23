-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalLat
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalLat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:33:26.024457+00:00
-- url     : https://prove2.me/theorems/24f3a243-df63-436a-9d8b-0b03b787a990
-- title:
--   Local Lat
-- statement:
--   Definitions and structural lemmas for Local Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalLat.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalPi
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
  {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K
def std : Submodule R (ι → K) := Submodule.pi Set.univ (fun _ => (1 : Submodule R K))
def sc (a : K) : Submodule R (ι → K) :=
  Submodule.pi Set.univ (fun _ => ((FractionalIdeal.spanSingleton (nonZeroDivisors R) a : FI) : Submodule R K))
def IsLat (A : Submodule R (ι → K)) : Prop :=
  ∃ r : R, r ≠ 0 ∧ sc (algebraMap R K r) ≤ A ∧ A ≤ sc (algebraMap R K r)⁻¹
end PI.IsoDetW.Loc


