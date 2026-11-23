-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerSubgroupIntersection_IsOpenIntSub
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerSubgroupIntersection_IsOpenIntSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:56.654434+00:00
-- url     : https://prove2.me/theorems/f9bf7ee3-3bee-4596-bc9f-69dc1869141d
-- title:
--   Is Open Int Sub
-- statement:
--   Definitions and structural lemmas for Is Open Int Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegerSubgroupIntersection/IsOpenIntSub.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GaugeGap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerSubgroupIntersection_IntInter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.GaugeCharW
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
section
variable (F : Type) [Field F] [NumberField F]
def intSub : AddSubgroup (AF F) where
  carrier := {x | ∀ v : HeightOneSpectrum (𝓞 F), sndA F x v ∈ v.adicCompletionIntegers F}
  add_mem' {a b} ha hb v := by
    rw [map_add]
    exact add_mem (ha v) (hb v)
  zero_mem' v := by
    rw [map_zero]
    exact zero_mem _
  neg_mem' {a} ha v := by
    rw [map_neg]
    exact neg_mem (ha v)
end
end PI.GaugeCharW


