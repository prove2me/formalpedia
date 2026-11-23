-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrand
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrand
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:11:47.986735+00:00
-- url     : https://prove2.me/theorems/fe054bb0-6bb7-46f9-81ff-0f789833f712
-- title:
--   Units Herbrand
-- statement:
--   Definitions and structural lemmas for Units Herbrand, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrand.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_Herbrand
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandF
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_uval_mem
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_uval_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K L}
noncomputable def uE (h : K ≤ L) [(subG p K L).Normal] :
    (layerU p K L).V →+ Additive (IntermediateField.extendScalars h)ˣ where
  toFun w := Additive.ofMul (Units.mk0 (⟨uval w, uval_mem h w⟩ : IntermediateField.extendScalars h)
    (fun h0 => uval_ne_zero w (congrArg Subtype.val h0)))
  map_zero' := Units.ext (Subtype.ext rfl)
  map_add' _ _ := Units.ext (Subtype.ext rfl)
end ReciprocityTheory.DiscreteGroups.LocalClassField


