-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalDet
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalDet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:36:50.580009+00:00
-- url     : https://prove2.me/theorems/7d5f5f9a-5e26-4a2a-8e10-6bf668802df5
-- title:
--   Local Det
-- statement:
--   Definitions and structural lemmas for Local Det, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalDet.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalLat
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K
abbrev mR (g : Matrix ι ι K) : (ι → K) →ₗ[R] (ι → K) := g.mulVecLin.restrictScalars R
variable (R) in

def chi (P : HeightOneSpectrum R) (g : Matrix ι ι K) : ℤ :=
  lidx P.asIdeal (std : Submodule R (ι → K)) ((std : Submodule R (ι → K)).map (mR g))
end PI.IsoDetW.Loc


