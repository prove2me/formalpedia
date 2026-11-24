-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PSpecFirstNe
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_PSpecFirstNe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:52.370804+00:00
-- url     : https://prove2.me/theorems/a4daf8ba-8dab-4df4-b700-e0b203632cfd
-- title:
--   PSpec First Ne
-- statement:
--   Definitions and structural lemmas for PSpec First Ne, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PSpecFirstNe.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
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
section Choice
variable {F : Type} [Field F] {k n : ℕ}
def specFirstSplit (ij : Fin (k + 1) × Fin n) : (Fin k × Fin n) ⊕ Fin n :=
  Fin.cases (motive := fun _ => (Fin k × Fin n) ⊕ Fin n) (Sum.inr ij.2) (fun i => Sum.inl (i, ij.2)) ij.1
end Choice
end
end GroundTheory.Heights₂.Heights


