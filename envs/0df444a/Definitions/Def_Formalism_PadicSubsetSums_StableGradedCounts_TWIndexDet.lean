-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexDet
-- name    : Formalism_PadicSubsetSums_StableGradedCounts_TWIndexDet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:10:56.643799+00:00
-- url     : https://prove2.me/theorems/958a7587-f56c-4eaf-a1b6-f8c273580f00
-- title:
--   TWIndex Det
-- statement:
--   Definitions and structural lemmas for TWIndex Det, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexDet.lean

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
namespace Formalism.IrreducibleCountingLemmas.TW
namespace Idx
variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]
end Idx
end Formalism.IrreducibleCountingLemmas.TW


