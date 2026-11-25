-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_SplittingModule
-- name    : GroundTheory_TateCohomology_SplittingModule
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T04:39:51.53841+00:00
-- url     : https://prove2.me/theorems/17fec628-67c8-4299-988f-5738e37b29b3
-- title:
--   Splitting Module
-- statement:
--   Definitions and structural lemmas for Splitting Module, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingModule.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PullbackExtension
import Definitions.Def_GroundTheory_TateCohomology_AugTrivial
import Definitions.Def_GroundTheory_TateCohomology_DeltaMap
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Theorems.Thm_GroundTheory_GroupCoh_CohTrivial_of_iso
import Theorems.Thm_GroundTheory_GroupCoh_TateAcyclic_of_iso
import Theorems.Thm_GroundTheory_GroupCoh_pullbackSES_shortExact

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
section Construction
variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (M : Rep.{u} k G)
  (u : groupCohomology M 2)
theorem isZero_groupCohomology_coind_two : IsZero (groupCohomology (coindSES.obj M).X₂ 2) :=
  ((tateAcyclic_coindSES_X₂ M) 2).of_iso (tateIsoH _ 2 2 rfl).symm
theorem exists_cocycle_δ_eq : ∃ f : cocycles₁ (coindSES.obj M).X₃,
    δ (coindSES_shortExact M) 1 2 rfl (H1π _ f) = u := by
  have : Epi (δ (coindSES_shortExact M) 1 2 rfl) :=
    epi_δ_of_isZero (coindSES_shortExact M) 1 (isZero_groupCohomology_coind_two M)
  obtain ⟨v, hv⟩ := (ModuleCat.epi_iff_surjective _).1 this u
  obtain ⟨f, rfl⟩ := (ModuleCat.epi_iff_surjective (H1π _)).1 inferInstance v
  exact ⟨f, hv⟩
noncomputable def splittingCocycle : cocycles₁ (coindSES.obj M).X₃ :=
  (exists_cocycle_δ_eq M u).choose
noncomputable def splittingSES : ShortComplex (Rep.{u} k G) :=
  pullbackSES (coindSES.obj M) (cocycleHom (splittingCocycle M u))
theorem splittingSES_shortExact : (splittingSES M u).ShortExact :=
  pullbackSES_shortExact _ (coindSES_shortExact M)
noncomputable abbrev splittingModule : Rep.{u} k G := (splittingSES M u).X₂
noncomputable def splittingSESResHom {H : Type u} [Group H] (φ : H →* G) :
    (splittingSES M u).map (resFunctor φ) ⟶ (coindSES.obj M).map (resFunctor φ) where
  τ₁ := 𝟙 _
  τ₂ := (resFunctor φ).map (pullbackFst _ (cocycleHom (splittingCocycle M u)))
  τ₃ := (resFunctor φ).map (cocycleHom (splittingCocycle M u))
  comm₁₂ := by
    ext x
    rfl
  comm₂₃ := by
    ext p
    exact mem_pullbackSubmodule.1 p.2
end Construction
end GroundTheory.GroupCoh


