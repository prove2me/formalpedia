-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_OrthogonalDecomposition_Imports
-- name    : Development_WeilBound_ThetaLifts_EigenvalueEndgame_OrthogonalDecomposition_Imports
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:31.776028+00:00
-- url     : https://prove2.me/theorems/616e2710-cc74-4ee5-b23e-425f4d9486d2
-- title:
--   Imports
-- statement:
--   Definitions and structural lemmas for Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/OrthogonalDecomposition/Imports.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKEnd.Orth
variable {H P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q]
def vals (ρ : H → Module.End ℂ P) (c : H → Module.End ℂ Q) : Set Q :=
  {y | ∃ U : P →ₗ[ℂ] Q, (∀ h x, U (ρ h x) = c h (U x)) ∧ ∃ x, y = U x}
end PositivityTheory.ThKEnd.Orth
end


