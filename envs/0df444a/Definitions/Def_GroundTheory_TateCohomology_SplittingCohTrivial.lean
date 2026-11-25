-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_SplittingCohTrivial
-- name    : GroundTheory_TateCohomology_SplittingCohTrivial
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T05:18:57.51621+00:00
-- url     : https://prove2.me/theorems/d236abdc-3004-5d97-8c74-4fc7c0e283c1
-- title:
--   Splitting Coh Trivial
-- statement:
--   Definitions and structural lemmas for Splitting Coh Trivial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingCohTrivial.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_SplittingModule
import Definitions.Def_GroundTheory_TateCohomology_CohTrivial
import Definitions.Def_GroundTheory_TateCohomology_ResCores
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory Limits groupCohomology Rep
namespace GroundTheory.GroupCoh
universe u
section LES
variable {k H : Type u} [CommRing k] [Group H] {X : ShortComplex (Rep.{u} k H)} (hX : X.ShortExact)
end LES
section TrivialInt
end TrivialInt
section Tate
variable {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (u : groupCohomology M 2)
variable (S : Subgroup G) [Fintype S]
noncomputable def augClass : groupCohomology (res S.subtype (augIdeal ℤ G)) 1 :=
  δ (augTrivSES_res_shortExact ℤ S.subtype) 0 1 rfl ((H0Iso _).inv (oneInvariant ℤ S.subtype))
noncomputable def subgroupNormElt : MonoidAlgebra ℤ G :=
  ∑ t : S, MonoidAlgebra.single (t : G) (1 : ℤ)
noncomputable abbrev resClass : groupCohomology (res S.subtype M) 2 :=
  map S.subtype (𝟙 (res S.subtype M)) 2 u
noncomputable abbrev splitδ :
    groupCohomology (res S.subtype (augIdeal ℤ G)) 1 ⟶ groupCohomology (res S.subtype M) 2 :=
  δ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) 1 2 rfl
end Tate
end GroundTheory.GroupCoh


