-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SplHformZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SplHformZero
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T13:34:07.748795+00:00
-- url     : https://prove2.me/theorems/b4657d9c-6c79-4733-bdef-390cad878e5b
-- title:
--   Spl Hform Zero
-- statement:
--   Definitions and structural lemmas for Spl Hform Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/SplHformZero.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartSplitOfOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSingleLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PIW.AdelClassFin
open Formalism.UG NumberField
open scoped Matrix
end PIW.AdelClassFin


