-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnitaryOrbits_VolSqMulIndex
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnitaryOrbits_VolSqMulIndex
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T07:56:06.364707+00:00
-- url     : https://prove2.me/theorems/5a478233-78e8-4804-8841-abc019e17e8a
-- title:
--   Vol Sq Mul Index
-- statement:
--   Definitions and structural lemmas for Vol Sq Mul Index, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnitaryOrbits/VolSqMulIndex.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.OmLocU.Sd
open MeasureTheory PI.VolStabSW.SdUniqW Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
section Vol
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V]
end Vol
section Ann
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
end Ann
end PI.OmLocU.Sd


