-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabTop
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabTop
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:09:50.005035+00:00
-- url     : https://prove2.me/theorems/c99355f4-5dd6-46d2-b9a9-af382e7e4496
-- title:
--   Ex Stab Top
-- statement:
--   Definitions and structural lemmas for Ex Stab Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/ExStabTop.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabSt
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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal
section Abstract
variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [MulAction G X] [TopologicalSpace X] [MeasurableSpace X]
end Abstract
def LCSCPolish : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y] [SecondCountableTopology Y],
    PolishSpace Y
def SecCtblW : Prop := InCtx fun F E _ _ _ _ _ _σ _M _J _a _X0 _hT =>
  SecondCountableTopology (AF F ⊗[F] E)
end PI.VolStabW


