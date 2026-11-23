-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_SplTApply
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_SplTApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:22.06383+00:00
-- url     : https://prove2.me/theorems/5d9433f6-db7b-4cd4-b10a-45d55a9c5e0a
-- title:
--   Spl TApply
-- statement:
--   Definitions and structural lemmas for Spl TApply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/SplTApply.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_Measures
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.MeasWCore
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures NumberField
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
def splT : AF F ⊗[F] E →+* (Ainf F ⊗[F] E) × (Af F ⊗[F] E) :=
  RingHom.prod (tensMap (E := E) (fstA F)) (tensMap (E := E) (sndA F))
end PI.UnitaryGroupMassFormula.MeasWCore


