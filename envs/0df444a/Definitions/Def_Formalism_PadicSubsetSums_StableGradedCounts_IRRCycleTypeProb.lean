-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleTypeProb
-- name    : Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleTypeProb
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:46:10.264845+00:00
-- url     : https://prove2.me/theorems/b7365fb6-3f24-4e41-8833-13b82f2d4790
-- title:
--   IRRCycle Type Prob
-- statement:
--   Definitions and structural lemmas for IRRCycle Type Prob, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRCycleTypeProb.lean

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
def typeMultiset (s : Finset ℕ) (n : ℕ → ℕ) : Multiset ℕ :=
  ∑ d ∈ s, Multiset.replicate (n d) d
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility


