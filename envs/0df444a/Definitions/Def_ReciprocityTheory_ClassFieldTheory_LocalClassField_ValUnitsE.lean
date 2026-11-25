-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsE
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsE
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T16:38:07.940987+00:00
-- url     : https://prove2.me/theorems/2d3896d9-6439-5c69-893c-37474ac331c5
-- title:
--   Val Units E
-- statement:
--   Definitions and structural lemmas for Val Units E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsE.lean

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
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
variable (p : ℕ) [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}
def toLayer [(subG p K L).Normal] (x : multOf p L) : (layer p K L).V :=
  ⟨x.1, fun σ => Units.ext (σ.2 _ x.2)⟩
end
end ReciprocityTheory.DiscreteGroups.LocalClassField


