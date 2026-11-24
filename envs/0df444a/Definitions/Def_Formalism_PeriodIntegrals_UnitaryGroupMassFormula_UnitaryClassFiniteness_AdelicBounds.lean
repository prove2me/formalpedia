-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_AdelicBounds
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_AdelicBounds
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T14:49:36.187855+00:00
-- url     : https://prove2.me/theorems/08dda884-67b1-45b5-99aa-eeefcd2fb19d
-- title:
--   Adelic Bounds
-- statement:
--   Definitions and structural lemmas for Adelic Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/AdelicBounds.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermASingleLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct ComplexOrder
namespace PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
end PI.UnitaryGroupMassFormula.UJClassFin


