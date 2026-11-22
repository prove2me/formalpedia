-- Prove2me | Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_DoubleCosetEqPreimage
-- name    : Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_DoubleCosetEqPreimage
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:11:38.569803+00:00
-- url     : https://prove2.me/theorems/ba20e37a-e3b7-4dd6-bb6b-50edea754896
-- title:
--   Double Coset Eq Preimage
-- statement:
--   Definitions and structural lemmas for Double Coset Eq Preimage, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace Formalism.DoubleCosetMeasures.P
section Generic
variable {X : Type}
def cls (r : Setoid X) (q : Quotient r) : Set X := Quotient.mk r ⁻¹' {q}
variable [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
end Generic
section Left
variable {G : Type} [Group G]
end Left
section Doset
variable {G : Type} [Group G]
def dcMap (K₀ : Subgroup G) (g : G) (k : K₀) : G ⧸ K₀ := ((k : G) * g : G)
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
end Doset
end Formalism.DoubleCosetMeasures.P


