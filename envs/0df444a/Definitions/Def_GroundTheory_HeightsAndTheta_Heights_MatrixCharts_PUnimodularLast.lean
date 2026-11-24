-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PUnimodularLast
-- name    : GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PUnimodularLast
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:31.289221+00:00
-- url     : https://prove2.me/theorems/94fcc2c6-6e66-46f3-8b9f-5c62cd554818
-- title:
--   PUnimodular Last
-- statement:
--   Definitions and structural lemmas for PUnimodular Last, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PUnimodularLast.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
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
open Matrix
noncomputable section
namespace UnimodularLast
def dotForm {k : ℕ} (ρ : Fin (k + 1) → ℤ) : (Fin (k + 1) → ℤ) →ₗ[ℤ] ℤ where
  toFun x := ρ ⬝ᵥ x
  map_add' x y := dotProduct_add ρ x y
  map_smul' c x := by rw [dotProduct_smul]; rfl
end UnimodularLast
end
end GroundTheory.Heights₂.Heights


