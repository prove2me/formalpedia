-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
-- name    : ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:09:05.828809+00:00
-- url     : https://prove2.me/theorems/0006468d-22fa-4cad-b53a-2f3cd257a904
-- title:
--   Pair Hom FCoe Of Id
-- statement:
--   Definitions and structural lemmas for Pair Hom FCoe Of Id, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PairHomFCoeOfId.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh
open ReciprocityTheory.Gal
universe u
section AdmAux
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def mkC (M : TRep R G) (n : ℕ) (f : (Fin n → G) → M.V) (hf : Continuous f) : M.coch.X n := ⟨f, hf⟩
end AdmAux
section ColimAux
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
end ColimAux
end ReciprocityTheory.Coh


