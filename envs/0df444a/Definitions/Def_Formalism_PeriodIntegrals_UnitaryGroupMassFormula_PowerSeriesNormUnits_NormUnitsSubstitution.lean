-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_NormUnitsSubstitution
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_NormUnitsSubstitution
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:04.786572+00:00
-- url     : https://prove2.me/theorems/a773a028-619e-4f68-8cd2-1e0f7d45157d
-- title:
--   Norm Units Substitution
-- statement:
--   Definitions and structural lemmas for Norm Units Substitution, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PowerSeriesNormUnits/NormUnitsSubstitution.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace PI.PhNormUnits.UnitaryGroupMassFormula
open PI.PhNormUnits
namespace PAdicPowerSeriesCoefficients
variable {p : ℕ} [Fact p.Prime]
noncomputable def intRing (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] :=
  _root_.UpperTheory.Reformulated.B.PadicComplexRingOfIntegers.intRing p
end PAdicPowerSeriesCoefficients
open PAdicPowerSeriesCoefficients
end PI.PhNormUnits.UnitaryGroupMassFormula


