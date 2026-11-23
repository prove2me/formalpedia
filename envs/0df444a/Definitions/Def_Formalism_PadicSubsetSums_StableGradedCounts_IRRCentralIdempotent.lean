-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdempotent
-- name    : Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdempotent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:49:14.833829+00:00
-- url     : https://prove2.me/theorems/90a67482-ba12-4ad2-8f3d-6332947fc866
-- title:
--   IRRCentral Idempotent
-- statement:
--   Definitions and structural lemmas for IRRCentral Idempotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRCentralIdempotent.lean

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
section
variable {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
end
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility


