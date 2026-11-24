-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmIndCoinvariants
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmIndCoinvariants
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:24:44.251799+00:00
-- url     : https://prove2.me/theorems/fc5dedcd-e343-4db1-857a-f5f3b375a52a
-- title:
--   Sm Ind Coinvariants
-- statement:
--   Definitions and structural lemmas for Sm Ind Coinvariants, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmIndCoinvariants.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.IndDual
namespace GlobalTheory.SmGL.IndCoinv
variable {G X U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup U] [Module ℂ U] {P : Subgroup G} {σ : Representation ℂ P X} {ρ : Representation ℂ P U}
omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem map_mem_fixed {σ : Representation ℂ G X} {ρ : Representation ℂ G U} (β : σ.IntertwiningMap ρ)
    {H : Subgroup G} {w : X} (hw : w ∈ fixed σ H) : β w ∈ fixed ρ H :=
  mem_fixed_iff.2 fun h hh => by rw [← β.isIntertwining, mem_fixed_iff.1 hw h hh]
end GlobalTheory.SmGL.IndCoinv


