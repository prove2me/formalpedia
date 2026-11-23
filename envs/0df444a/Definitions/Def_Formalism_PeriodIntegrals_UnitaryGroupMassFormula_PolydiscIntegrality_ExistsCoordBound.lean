-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolydiscIntegrality_ExistsCoordBound
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolydiscIntegrality_ExistsCoordBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:34.547045+00:00
-- url     : https://prove2.me/theorems/0caea086-2532-470a-802b-8656b9ac3b1d
-- title:
--   Exists Coord Bound
-- statement:
--   Definitions and structural lemmas for Exists Coord Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolydiscIntegrality/ExistsCoordBound.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolydiscIntegrality_NormPPosLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolydiscIntegrality_Lemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.PolydiscIntegrality₂
open Filter Topology
variable {p : ℕ} [Fact p.Prime]
end PI.PolydiscIntegrality₂


