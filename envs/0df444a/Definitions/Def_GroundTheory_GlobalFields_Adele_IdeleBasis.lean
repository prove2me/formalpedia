-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Adele_IdeleBasis
-- name    : GroundTheory_GlobalFields_Adele_IdeleBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:55.553246+00:00
-- url     : https://prove2.me/theorems/82b3c10f-bf84-47dc-a631-5ba79d59ac50
-- title:
--   Idele Basis
-- statement:
--   Definitions and structural lemmas for Idele Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IdeleBasis.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology TopologicalSpace NumberField IsDedekindDomain
open scoped RestrictedProduct NumberField.AdeleRing
namespace GroundTheory.Global
namespace RestrictedProduct
variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)}
end RestrictedProduct
namespace IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
end IdeleGroup
end GroundTheory.Global


