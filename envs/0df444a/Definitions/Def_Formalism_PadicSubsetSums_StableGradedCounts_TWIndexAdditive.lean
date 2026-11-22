-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive
-- name    : Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:18.550804+00:00
-- url     : https://prove2.me/theorems/7124b21b-d1c8-4139-bce5-585e3d6ece6a
-- title:
--   TWIndex Additive
-- statement:
--   Definitions and structural lemmas for TWIndex Additive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
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
section General
variable {O V : Type} [CommRing O] [AddCommGroup V] [Module O V]
end General
section LenDet
variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
end LenDet
section Lat
variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]
variable [FiniteDimensional K V]
end Lat
end Idx
end Formalism.IrreducibleCountingLemmas.TW


