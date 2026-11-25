-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SaturatedBlocksSummand
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SaturatedBlocksSummand
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:47.43012+00:00
-- url     : https://prove2.me/theorems/7b92c548-d131-4e56-9986-a75e01bd2a20
-- title:
--   Saturated Blocks Summand
-- statement:
--   Definitions and structural lemmas for Saturated Blocks Summand, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/SaturatedBlocksSummand.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
namespace GlobalTheory.SatBlocks
def intRing {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) : Subring C where
  carrier := {z | (0 : WithTop ℝ) ≤ v z}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [v.map_mul]; exact add_nonneg ha hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    exact v.map_le_add ha hb
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rwa [v.map_neg]
end GlobalTheory.SatBlocks


