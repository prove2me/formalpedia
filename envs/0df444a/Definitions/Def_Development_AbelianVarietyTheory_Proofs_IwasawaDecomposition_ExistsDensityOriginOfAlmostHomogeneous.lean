-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsDensityOriginOfAlmostHomogeneous
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsDensityOriginOfAlmostHomogeneous
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:28:10.997992+00:00
-- url     : https://prove2.me/theorems/b41bf1fa-71e2-4b0e-904f-754dde72f8ae
-- title:
--   Exists Density Origin Of Almost Homogeneous
-- statement:
--   Definitions and structural lemmas for Exists Density Origin Of Almost Homogeneous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsDensityOriginOfAlmostHomogeneous.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
namespace GlobalTheory
section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
end
end GlobalTheory


