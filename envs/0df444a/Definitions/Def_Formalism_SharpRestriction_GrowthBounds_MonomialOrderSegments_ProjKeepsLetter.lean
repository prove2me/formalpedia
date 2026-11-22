-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:45:44.340533+00:00
-- url     : https://prove2.me/theorems/549087c1-e189-4bf0-be82-cf90b9204ead
-- title:
--   Proj Keeps Letter
-- statement:
--   Definitions and structural lemmas for Proj Keeps Letter, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ProjKeepsLetter.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}
section Generic
variable {L : Type} [Fintype L] [DecidableEq L] (sg : L → Bool) {r : ℕ} [NeZero r] (d : L → ℕ)
end Generic
section Torus
variable {L : Type} [DecidableEq L] (sg : L → Bool) {r : ℕ}
end Torus
end Formalism.MainNotions.PlaneGram


