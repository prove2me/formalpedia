-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_EventuallySmulSub
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_EventuallySmulSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:31.144272+00:00
-- url     : https://prove2.me/theorems/eb9631ff-aec3-4758-a472-8acb87a159dc
-- title:
--   Eventually Smul Sub
-- statement:
--   Definitions and structural lemmas for Eventually Smul Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/EventuallySmulSub.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_MeasureEqOfCos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabS
open Topology Filter Set
section Abs
variable {K V X : Type} [Field K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]
  [AddCommGroup X] [Module K X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul K X]
def smulSub {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) : AddSubgroup W :=
  P.map (DistribMulAction.toAddMonoidHom W t)
variable [T2Space X]
end Abs
end PI.VolStabS


