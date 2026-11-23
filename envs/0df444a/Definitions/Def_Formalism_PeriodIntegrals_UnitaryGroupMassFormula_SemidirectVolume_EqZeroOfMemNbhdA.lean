-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_EqZeroOfMemNbhdA
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_EqZeroOfMemNbhdA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:35.978146+00:00
-- url     : https://prove2.me/theorems/6fd1cbac-f8bf-4251-b574-f5eba80f56df
-- title:
--   Eq Zero Of Mem Nbhd A
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Mem Nbhd A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/EqZeroOfMemNbhdA.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
  IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct Matrix
section Adele
variable (F : Type) [Field F] [NumberField F]
def nbhdA : Set (AF F) := {x | ‖x.1‖ < 1 ∧ x.2 ∈ PI.AdCpctDenWork.intAd F}
end Adele
section Tens
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [Module.Finite F E]
end Tens
end PI.VolSemiDirect.W


