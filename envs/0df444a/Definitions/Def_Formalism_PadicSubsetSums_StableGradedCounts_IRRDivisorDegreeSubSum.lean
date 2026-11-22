-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRDivisorDegreeSubSum
-- name    : Formalism_PadicSubsetSums_StableGradedCounts_IRRDivisorDegreeSubSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:47:24.959855+00:00
-- url     : https://prove2.me/theorems/b0348ecc-12a0-4a89-9cbd-3c185b54d8ad
-- title:
--   IRRDivisor Degree Sub Sum
-- statement:
--   Definitions and structural lemmas for IRRDivisor Degree Sub Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRDivisorDegreeSubSum.lean

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Lemmata_GeneralBFactRightRest_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial UniqueFactorizationMonoid
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.GaloisIrreducibility (IsSubSum)
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility


