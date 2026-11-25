-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemIdealLattice
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemIdealLattice
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T10:35:18.881371+00:00
-- url     : https://prove2.me/theorems/68f78273-ee17-5242-b7bc-189db150e00e
-- title:
--   Exists Smul Mem Ideal Lattice
-- statement:
--   Definitions and structural lemmas for Exists Smul Mem Ideal Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulMemIdealLattice.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsTer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ComplexAt
open scoped nonZeroDivisors ComplexOrder
noncomputable section
namespace S6.QuotExtension
variable {K : Type} [Field K] [NumberField K]
def embMat (σ : K →+* ℂ) {n : ℕ} {ι : Type*} (u : ι → Fin n → K) : Matrix (Fin n) ι ℂ :=
  Matrix.of fun r s => σ (u s r)
end S6.QuotExtension
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels


