-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_FullIffBijective
-- name    : Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_FullIffBijective
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T23:16:22.129952+00:00
-- url     : https://prove2.me/theorems/049ccf82-2593-4653-8ae0-bd5198f7e4f0
-- title:
--   Full Iff Bijective
-- statement:
--   Definitions and structural lemmas for Full Iff Bijective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/FullIffBijective.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CoeffRingTest
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
section Ring
variable {O L : Type} [CommRing O] [Field L] (ι : O →+* L) (σ : L →+* ℂ)
def gen : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range (σ.comp ι))
def Full : Prop := Function.Injective ι ∧ ∀ z ∈ gen ι σ, IsIntegral ℤ z → z ∈ Set.range (σ.comp ι)
end Ring
end GlobalTheory.CoeffRingTest


