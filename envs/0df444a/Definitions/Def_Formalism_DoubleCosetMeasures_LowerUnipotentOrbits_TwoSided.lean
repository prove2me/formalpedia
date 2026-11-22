-- Prove2me | Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_TwoSided
-- name    : Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_TwoSided
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:11:46.825065+00:00
-- url     : https://prove2.me/theorems/334c96f2-bf45-489a-b4e6-1e306b1ef6a9
-- title:
--   Two Sided
-- statement:
--   Definitions and structural lemmas for Two Sided, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/TwoSided.lean

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
namespace Formalism.DoubleCosetMeasures.P
def box {G₁ G₂ : Type} [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂)) : Set (G₁ × G₂) :=
  ((fun x => x * p.1.out⁻¹) ⁻¹' (K₁ : Set G₁)) ×ˢ ((fun y => p.2.out⁻¹ * y) ⁻¹' (K₂ : Set G₂))
def clsTS {G₁ G₂ : Type} [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (z : G₁ × G₂) : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂) :=
  (Quotient.mk _ z.1, (z.2 : G₂ ⧸ K₂))
end Formalism.DoubleCosetMeasures.P


