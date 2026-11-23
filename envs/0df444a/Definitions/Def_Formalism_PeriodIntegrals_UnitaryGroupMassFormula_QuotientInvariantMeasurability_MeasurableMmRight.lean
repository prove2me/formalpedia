-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableMmRight
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableMmRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:26:21.08061+00:00
-- url     : https://prove2.me/theorems/62592b34-87ea-4be0-acb1-bb311db1ab4c
-- title:
--   Measurable Mm Right
-- statement:
--   Definitions and structural lemmas for Measurable Mm Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientInvariantMeasurability/MeasurableMmRight.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
noncomputable section
namespace PI.QuotInvW
variable {m : ℕ}
def mm (a b : MtM m) : MtM m := fun i j => (Matrix.of a * Matrix.of b) i j
def minv (a : MtM m) : MtM m := fun i j => (Matrix.of a)⁻¹ i j
def oneM : MtM m := fun i j => (1 : Matrix (Fin m) (Fin m) ℂ) i j
section HidaSetting
variable {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}
end HidaSetting
end PI.QuotInvW


