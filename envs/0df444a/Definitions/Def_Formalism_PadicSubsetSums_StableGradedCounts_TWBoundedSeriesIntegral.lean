-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWBoundedSeriesIntegral
-- name    : Formalism_PadicSubsetSums_StableGradedCounts_TWBoundedSeriesIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:18.78445+00:00
-- url     : https://prove2.me/theorems/e7d12d89-07c2-4bd4-90cc-c3a1a990a4f3
-- title:
--   TWBounded Series Integral
-- statement:
--   Definitions and structural lemmas for TWBounded Series Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWBoundedSeriesIntegral.lean

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
namespace Formalism.IrreducibleCountingLemmas.TW
noncomputable def consEquiv (n : ℕ) : ℕ × (Fin n →₀ ℕ) ≃ (Fin (n + 1) →₀ ℕ) where
  toFun p := Finsupp.cons p.1 p.2
  invFun m := (m 0, Finsupp.tail m)
  left_inv p := by simp
  right_inv m := by simp
end Formalism.IrreducibleCountingLemmas.TW


