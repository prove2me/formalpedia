-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LintFibre
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LintFibre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:08:33.538459+00:00
-- url     : https://prove2.me/theorems/d2069390-9b70-4e06-91db-f2d2c2bc21a7
-- title:
--   Lint Fibre
-- statement:
--   Definitions and structural lemmas for Lint Fibre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LintFibre.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnfoldAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW
open MeasureTheory Set
open scoped ENNReal Pointwise
section Abs2
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
  [MulAction G Y]
end Abs2
end PI.VolStabW


