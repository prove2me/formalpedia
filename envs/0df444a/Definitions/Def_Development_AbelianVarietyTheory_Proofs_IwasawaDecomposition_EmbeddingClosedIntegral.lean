-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EmbeddingClosedIntegral
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EmbeddingClosedIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:02.198976+00:00
-- url     : https://prove2.me/theorems/2a7efe55-308a-4c57-8f01-b48e26574268
-- title:
--   Embedding Closed Integral
-- statement:
--   Definitions and structural lemmas for Embedding Closed Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EmbeddingClosedIntegral.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.CoefEmbed
open IsLocalRing Topology
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
end GlobalTheory.CoefEmbed


