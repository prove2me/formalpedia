-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieAlg
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_LieAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:24.254774+00:00
-- url     : https://prove2.me/theorems/9681ab4f-559b-4e51-9665-dd3bf2b2809d
-- title:
--   Lie Alg
-- statement:
--   Definitions and structural lemmas for Lie Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LieAlg.lean

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
namespace Formalism.L2.Pj.LieAlg
open Submodule
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]
def tailZero (m : ℕ) (i : Fin m) : Submodule V (Fin m → K) where
  carrier := {α | ∀ j, i < j → α j = 0}
  add_mem' {a b} ha hb j hj := by simp [ha j hj, hb j hj]
  zero_mem' j _ := rfl
  smul_mem' r α ha j hj := by simp [ha j hj]
end Formalism.L2.Pj.LieAlg


