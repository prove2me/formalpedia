-- Prove2me | Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_ExistsContinuousLowerUpperEntry
-- name    : Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_ExistsContinuousLowerUpperEntry
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:11:41.84597+00:00
-- url     : https://prove2.me/theorems/e691a7e9-8473-4eb5-ad68-a57636e4787d
-- title:
--   Exists Continuous Lower Upper Entry
-- statement:
--   Definitions and structural lemmas for Exists Continuous Lower Upper Entry, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
namespace Formalism.DoubleCosetMeasures.P
namespace Supp
section LU
variable {K : Type} [CommRing K] {n : ℕ}
variable [TopologicalSpace K] [IsTopologicalRing K]
end LU
section Pt
end Pt
section Closed
variable {K : Type} [CommRing K] [TopologicalSpace K] [T2Space K] {n : ℕ}
end Closed
end Supp
end Formalism.DoubleCosetMeasures.P


