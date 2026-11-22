-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_LandauZeroFreeHalfPlane
-- name    : Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_LandauZeroFreeHalfPlane
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:58:33.792862+00:00
-- url     : https://prove2.me/theorems/b505681b-ff9a-47fc-a5d8-c7d970bb1bc0
-- title:
--   Landau Zero Free Half Plane
-- statement:
--   Definitions and structural lemmas for Landau Zero Free Half Plane, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/LandauZeroFreeHalfPlane.lean

import Mathlib
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ZetaZeroFreeRegion.SlopeTestRemainingChoices
open Formalism
def LandauZeroFreeHalfPlane : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ y₀ : ℝ, (∀ y : ℝ, y₀ ≤ y → Gz y ≤ y ^ θ) →
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0
end Formalism.MainNotions.ZetaZeroFreeRegion.SlopeTestRemainingChoices
end


