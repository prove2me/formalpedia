-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:27.9558+00:00
-- url     : https://prove2.me/theorems/1cb402cd-0e08-4e94-9acf-c9aaf76cf633
-- title:
--   Add Dbl
-- statement:
--   Definitions and structural lemmas for Add Dbl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/AddDbl.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.GalTorsConj.W
open Formalism.L2.Th1.F
open Filter Topology
namespace ZetaDoubling
open OriginCoordinatesAdd
def mu (L : PeriodPair) (z : ℂ) : ℂ :=
  (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) / L.derivWeierstrassP z
end ZetaDoubling
end PI.GalTorsConj.W
end


