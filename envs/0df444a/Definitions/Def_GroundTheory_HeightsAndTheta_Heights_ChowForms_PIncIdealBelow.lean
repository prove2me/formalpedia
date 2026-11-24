-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PIncIdealBelow
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_PIncIdealBelow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:22.589674+00:00
-- url     : https://prove2.me/theorems/00d5db27-eb5e-471f-b39c-afdbad8abd58
-- title:
--   PInc Ideal Below
-- statement:
--   Definitions and structural lemmas for PInc Ideal Below, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PIncIdealBelow.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
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
def shiftGroup {e n : ℕ} (ij : Fin e × Fin n) : Fin (e + 1) × Fin n := (ij.1.succ, ij.2)
def killFirst {F : Type*} [Field F] {e n : ℕ} (ij : Fin (e + 1) × Fin n) :
    MvPolynomial (Fin (e + 1) × Fin n) F :=
  if ij.1 = 0 then 0 else X ij
end
end GroundTheory.Heights₂.Heights


