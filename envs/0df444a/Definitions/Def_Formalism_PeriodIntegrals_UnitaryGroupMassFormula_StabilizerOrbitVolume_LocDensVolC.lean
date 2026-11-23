-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolC
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:30.586274+00:00
-- url     : https://prove2.me/theorems/af8e35e6-baf0-4a52-805c-aff812281a47
-- title:
--   Loc Dens Vol C
-- statement:
--   Definitions and structural lemmas for Loc Dens Vol C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensVolC.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabSW
namespace VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))
end VolAAW
end PI.VolStabSW


