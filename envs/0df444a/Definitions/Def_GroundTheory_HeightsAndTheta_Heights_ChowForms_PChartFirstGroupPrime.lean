-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartFirstGroupPrime
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartFirstGroupPrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:36:38.142527+00:00
-- url     : https://prove2.me/theorems/892eeb82-093f-4451-a137-705a3937e66c
-- title:
--   PChart First Group Prime
-- statement:
--   Definitions and structural lemmas for PChart First Group Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartFirstGroupPrime.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
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
open MvPolynomial
noncomputable section
def firstGroupVars (e n : ℕ) : Fin (e + 1) × Fin n ≃ Fin n ⊕ Fin e × Fin n where
  toFun ij := Fin.cases (motive := fun _ => Fin n ⊕ Fin e × Fin n) (Sum.inl ij.2)
    (fun i => Sum.inr (i, ij.2)) ij.1
  invFun := Sum.elim (fun m => (0, m)) (fun im => (im.1.succ, im.2))
  left_inv := by
    rintro ⟨i, m⟩
    cases i using Fin.cases <;> rfl
  right_inv := by
    rintro (m | ⟨i, m⟩) <;> rfl
end
end GroundTheory.Heights₂.Heights


