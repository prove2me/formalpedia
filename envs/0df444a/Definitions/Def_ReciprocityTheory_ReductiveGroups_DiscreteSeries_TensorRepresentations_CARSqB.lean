-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqB
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:55.512798+00:00
-- url     : https://prove2.me/theorems/f13e0fd2-a916-4bf5-9a21-e77e8681f16e
-- title:
--   CARSq B
-- statement:
--   Definitions and structural lemmas for CARSq B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARSqB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
def crossT (ε : Fin n → Bool) (E cp cm : Fin n → Fin n → Module.End ℂ W) : Module.End ℂ W :=
  ∑ x ∈ plusIdx ε, ∑ y ∈ plusIdx ε, E x y * sgE ε cp cm y x +
    ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, E a b * sgE ε cp cm b a
end ReciprocityTheory.ChartRestriction.DS


