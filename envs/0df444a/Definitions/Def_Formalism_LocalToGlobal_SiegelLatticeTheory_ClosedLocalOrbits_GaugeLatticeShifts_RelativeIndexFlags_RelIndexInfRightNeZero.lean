-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_RelIndexInfRightNeZero
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_RelIndexInfRightNeZero
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T08:38:48.89987+00:00
-- url     : https://prove2.me/theorems/1b235c6c-c2f7-4118-8296-18df53b48246
-- title:
--   Rel Index Inf Right Ne Zero
-- statement:
--   Definitions and structural lemmas for Rel Index Inf Right Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RelativeIndexFlags/RelIndexInfRightNeZero.lean

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
namespace Formalism.L2.SG.Pf.RelativeIndexFlags
variable {G : Type*} [Group G]
def ratio (A S : Subgroup G) : ℝ := (A.relIndex S : ℝ) / (S.relIndex A : ℝ)
abbrev cj (g : G) (A : Subgroup G) : Subgroup G := A.map (MulAut.conj g).toMonoidHom
end Formalism.L2.SG.Pf.RelativeIndexFlags


