-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSA
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSA
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T13:30:22.775652+00:00
-- url     : https://prove2.me/theorems/4e27b114-bced-499c-bee4-807392fd28e3
-- title:
--   Loc Dens SA
-- statement:
--   Definitions and structural lemmas for Loc Dens SA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensSA.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_FiniteNeighbourhoodSecond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
namespace PI.VolStabW
def SAf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (U : AddSubgroup (FiniteAdeleRing (𝓞 F) F)),
    IsOpen (U : Set (FiniteAdeleRing (𝓞 F) F)) →
    ∀ x : FiniteAdeleRing (𝓞 F) F, ∃ a : F, x - algebraMap F (FiniteAdeleRing (𝓞 F) F) a ∈ U
end PI.VolStabW


