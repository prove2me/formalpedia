-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualEmbBijective
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualEmbBijective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:45.340465+00:00
-- url     : https://prove2.me/theorems/61a3b6bc-0145-4220-b802-924acb4c01f1
-- title:
--   PDual Emb Bijective
-- statement:
--   Definitions and structural lemmas for PDual Emb Bijective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualEmbBijective.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open NumberField Matrix
noncomputable section
namespace DualEmbeddingBijective
variable {K : Type} [Field K] [NumberField K] {i : ℕ}
def pairing (w : (K →+* ℂ) × Fin i → ℂ) : (Fin i → K) →+ ℂ where
  toFun φ := ∑ p, p.1 (φ p.2) * w p
  map_zero' := by simp
  map_add' φ ψ := by simp [add_mul, Finset.sum_add_distrib]
end DualEmbeddingBijective
end
end GroundTheory.Heights₂.Heights


