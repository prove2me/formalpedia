-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:24.036261+00:00
-- url     : https://prove2.me/theorems/2dbb2d6e-ccd3-4578-9112-596f5de1d47c
-- title:
--   Neg Log Valuation
-- statement:
--   Definitions and structural lemmas for Neg Log Valuation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndexDeterminant/NegLogValuation.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatIdxDet
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.DivisionValues
open scoped nonZeroDivisors
noncomputable section
namespace PI.LatIdxDetW
section Gen
variable {R W W' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
end Gen
section Lat
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable [FiniteDimensional K V]
end Lat
end PI.LatIdxDetW


