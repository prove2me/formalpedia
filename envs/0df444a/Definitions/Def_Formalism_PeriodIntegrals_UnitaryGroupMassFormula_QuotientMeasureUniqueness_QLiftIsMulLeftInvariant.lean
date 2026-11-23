-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QLiftIsMulLeftInvariant
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QLiftIsMulLeftInvariant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:55:00.725108+00:00
-- url     : https://prove2.me/theorems/f1a4602a-84f5-4266-998f-f1a662e42dc9
-- title:
--   QLift Is Mul Left Invariant
-- statement:
--   Definitions and structural lemmas for QLift Is Mul Left Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientMeasureUniqueness/QLiftIsMulLeftInvariant.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QmuWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Pointwise
open scoped ENNReal
namespace PI.QuotMeasUniqW
def hAvg {G : Type} [Group G] [MeasurableSpace G] {H : Subgroup G} (ν : Measure H) (f : G → ℝ≥0∞)
    (g : G) : ℝ≥0∞ :=
  ∫⁻ h, f (g * (h : G)) ∂ν
def qKer {G : Type} [Group G] [MeasurableSpace G] {H : Subgroup G} (ν : Measure H)
    (y : G ⧸ H) : Measure G :=
  Measure.map (fun h : H => y.out * (h : G)) ν
def qLift {G : Type} [Group G] [MeasurableSpace G] {H : Subgroup G} (ν : Measure H)
    (ρ : Measure (G ⧸ H)) : Measure G :=
  ρ.bind (qKer ν)
end PI.QuotMeasUniqW


