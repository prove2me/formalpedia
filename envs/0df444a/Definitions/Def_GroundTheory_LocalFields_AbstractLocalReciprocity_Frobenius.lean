-- Prove2me | Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
-- name    : GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:03:18.903291+00:00
-- url     : https://prove2.me/theorems/260b5213-97d4-401b-ad8c-a567842726e8
-- title:
--   Frobenius
-- statement:
--   Definitions and structural lemmas for Frobenius, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Frobenius.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_index_multiples

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.LocalField.Abstract
open ProfiniteInteger
section Density
instance finiteIndex_multiples (N : ℕ+) : (multiples N).FiniteIndex :=
  ⟨by rw [index_multiples]; exact N.ne_zero⟩
end Density
section FixedField
variable {G : Type*} [Group G] {d : G →* Multiplicative ℤ̂} {L : Subgroup G} {σ : G}
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable (d L σ) in

def frobeniusClosure : Subgroup G :=
  (Subgroup.zpowers σ ⊔ (L ⊓ d.ker)).topologicalClosure
variable [CompactSpace G] [TotallyDisconnectedSpace G]
end FixedField
end GroundTheory.LocalField.Abstract


