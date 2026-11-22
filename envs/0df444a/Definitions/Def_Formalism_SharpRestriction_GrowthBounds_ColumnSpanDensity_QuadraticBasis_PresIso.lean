-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_PresIso
-- name    : Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_PresIso
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:04:04.436441+00:00
-- url     : https://prove2.me/theorems/65ec8b8d-1caf-4776-965b-b98ad283767d
-- title:
--   Pres Iso
-- statement:
--   Definitions and structural lemmas for Pres Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/QuadraticBasis/PresIso.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_StatementO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
section
variable {W O : Type} [CommRing W] [CommRing O]
def pbE (j : W →+* O) (θ w : O) (t : W × W × W × W) : O :=
  j t.1 + j t.2.1 * θ + j t.2.2.1 * w + j t.2.2.2 * θ * w
def pbM (f0 f1 ϖ : W) (t s : W × W × W × W) : W × W × W × W :=
  (t.1 * s.1 - t.2.1 * s.2.1 * f0 + ϖ * (t.2.2.1 * s.2.2.1 - t.2.2.2 * s.2.2.2 * f0),
   t.1 * s.2.1 + t.2.1 * s.1 - t.2.1 * s.2.1 * f1
     + ϖ * (t.2.2.1 * s.2.2.2 + t.2.2.2 * s.2.2.1 - t.2.2.2 * s.2.2.2 * f1),
   t.1 * s.2.2.1 - t.2.1 * s.2.2.2 * f0 + t.2.2.1 * s.1 - t.2.2.2 * s.2.1 * f0,
   t.1 * s.2.2.2 + t.2.1 * s.2.2.1 - t.2.1 * s.2.2.2 * f1 + t.2.2.1 * s.2.1 + t.2.2.2 * s.1
     - t.2.2.2 * s.2.1 * f1)
end
def pbF {W₁ W₂ : Type} [CommRing W₁] [CommRing W₂] (φ : W₁ ≃+* W₂) (t : W₁ × W₁ × W₁ × W₁) :
    W₂ × W₂ × W₂ × W₂ :=
  (φ t.1, φ t.2.1, φ t.2.2.1, φ t.2.2.2)
end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis


