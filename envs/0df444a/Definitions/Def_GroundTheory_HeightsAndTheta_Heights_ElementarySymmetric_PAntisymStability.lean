-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymStability
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymStability
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:46.71668+00:00
-- url     : https://prove2.me/theorems/ee8737a4-5022-4e1f-b87c-3f0b66d8be14
-- title:
--   PAntisym Stability
-- statement:
--   Definitions and structural lemmas for PAntisym Stability, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymStability.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
def antisymEvalOn {T : Type*} {N : ℕ} (Ω : Set (T × Fin N → ℝ)) :
    MvPolynomial (T × Fin N) ℝ →ₗ[ℝ] C(Ω, ℝ) where
  toFun p := ⟨fun x => eval (x : T × Fin N → ℝ) p, (continuous_eval p).comp continuous_subtype_val⟩
  map_add' p q := by ext x; simp
  map_smul' c p := by ext x; simp
end GroundTheory.Heights₂.Heights


