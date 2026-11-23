-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandF
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:49.687796+00:00
-- url     : https://prove2.me/theorems/8bc8f248-f583-46ff-8f58-7746c1f86b70
-- title:
--   Units Herbrand F
-- statement:
--   Definitions and structural lemmas for Units Herbrand F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandF.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandE
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
variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}
def uval [(subG p K L).Normal] (w : (layerU p K L).V) : PadicAlgCl p :=
  ((Additive.toMul (Subtype.val (p := fun x => x ∈ Ubar p) w.1) : (PadicAlgCl p)ˣ) : PadicAlgCl p)
section
variable [(subG p K L).Normal]
end
end ReciprocityTheory.DiscreteGroups.LocalClassField


