-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DirichletLZeroSymmetry
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DirichletLZeroSymmetry
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:57.463421+00:00
-- url     : https://prove2.me/theorems/5a4b4336-4786-4796-ab0a-aec8e58d5f01
-- title:
--   Dirichlet LZero Symmetry
-- statement:
--   Definitions and structural lemmas for Dirichlet LZero Symmetry, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DirichletLZeroSymmetry.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Complex GlobalTheory.Mem.An
namespace GlobalTheory.Mem.An
section
variable {q : ℕ}
variable [NeZero q]
noncomputable def zsymFactor (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  (q : ℂ) ^ ((1 - s) - 1 / 2) * χ.rootNumber * (χ.gammaFactor s)⁻¹ / (χ⁻¹.gammaFactor (1 - s))⁻¹
end
end GlobalTheory.Mem.An


