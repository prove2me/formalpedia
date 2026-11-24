-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:48.377293+00:00
-- url     : https://prove2.me/theorems/50d59efa-528d-49a0-b304-46dba39d0c86
-- title:
--   Statements Herm Form Compare
-- statement:
--   Definitions and structural lemmas for Statements Herm Form Compare, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsHermFormCompare.lean

import Mathlib
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
open scoped ComplexOrder
noncomputable section
def HermFormCompare.Statement : Prop :=
  ∀ (n : ℕ) (M N : Matrix (Fin n) (Fin n) ℂ), M.PosDef → N.PosDef →
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℂ, (star x ⬝ᵥ (M *ᵥ x)).re ≤ c * (star x ⬝ᵥ (N *ᵥ x)).re
example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin 2) (Fin 2) ℂ).PosDef ∧
    (1 : Matrix (Fin 2) (Fin 2) ℂ).PosDef :=
  ⟨Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, Matrix.PosDef.one⟩
end
end GroundTheory.Heights₂.Heights


