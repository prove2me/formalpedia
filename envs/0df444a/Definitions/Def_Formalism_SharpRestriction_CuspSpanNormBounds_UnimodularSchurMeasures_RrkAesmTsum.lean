-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkAesmTsum
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkAesmTsum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:09.277719+00:00
-- url     : https://prove2.me/theorems/70ddbdd3-73c0-4757-9cfe-faa6aab89ea1
-- title:
--   Rrk Aesm Tsum
-- statement:
--   Definitions and structural lemmas for Rrk Aesm Tsum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkAesmTsum.lean

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
variable {G : Type*} [Group G]
def rrk_K (Γ : Subgroup G) (φ : G → ℂ) (x y : G) : ℂ := ∑' γ : Γ, φ (x⁻¹ * (γ : G) * y)
def rrk_Kab (Γ : Subgroup G) (φ : G → ℂ) (x y : G) : ℝ≥0∞ := ∑' γ : Γ, ‖φ (x⁻¹ * (γ : G) * y)‖ₑ
end Formalism.MainNotions.LeviCoordinates
end


