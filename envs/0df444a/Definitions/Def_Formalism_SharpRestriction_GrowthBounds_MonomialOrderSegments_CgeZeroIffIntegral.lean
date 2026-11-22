-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:39:21.131392+00:00
-- url     : https://prove2.me/theorems/8d2eccfc-3155-4f22-8354-356195531c59
-- title:
--   Cge Zero Iff Integral
-- statement:
--   Definitions and structural lemmas for Cge Zero Iff Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
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
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
section DVR
variable {v} {p : ℕ} [CharZero K]
end DVR
def kapL (p r : ℕ) {L : Type} [Fintype L] (d : L → ℕ) : ℝ :=
  ∑ i, if d i = 0 then 0 else (r : ℝ) * Real.logb p ((d i : ℝ) + r)
section DVR2
variable {v} {p : ℕ} [CharZero K]
end DVR2
section Star
variable {v} {p : ℕ} [CharZero K]
end Star
end Formalism.MainNotions.PlaneGram


