-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_ExpTri
-- name    : Formalism_PeriodIntegrals_ExpTri
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:42.693934+00:00
-- url     : https://prove2.me/theorems/754d791d-6a7f-48e7-9890-f76eba1db05f
-- title:
--   Exp Tri
-- statement:
--   Definitions and structural lemmas for Exp Tri, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ExpTri.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace PI
def ExpTri : Prop :=
  ∀ (n : ℕ) (X Y Z U : Matrix (Fin n) (Fin n) ℂ), Xᴴ = X → Yᴴ = Y → Zᴴ = Z →
    U ∈ Matrix.unitaryGroup (Fin n) ℂ →
    NormedSpace.exp X * NormedSpace.exp Y = U * NormedSpace.exp Z →
    Real.sqrt (∑ i, ∑ j, ‖Z i j‖ ^ 2) ≤
      Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2) + Real.sqrt (∑ i, ∑ j, ‖Y i j‖ ^ 2)
end PI
end


