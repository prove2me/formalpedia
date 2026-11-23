-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:43.444848+00:00
-- url     : https://prove2.me/theorems/ea76d418-b3f9-403c-bd5e-79c393016f7d
-- title:
--   Val Units C
-- statement:
--   Definitions and structural lemmas for Val Units C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsC.lean

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
def eLK : ℕ := eK p L / eK p K
def fLK : ℕ := fK p L / fK p K
variable {K L}
end
end ReciprocityTheory.DiscreteGroups.LocalClassField


