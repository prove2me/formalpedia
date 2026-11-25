-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_NotDvdSuperIndexIffMap
-- name    : GroundTheory_ProfiniteCohomology_NotDvdSuperIndexIffMap
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:54:19.826088+00:00
-- url     : https://prove2.me/theorems/ac3776ad-1678-4831-9370-4579eab280c9
-- title:
--   Not Dvd Super Index Iff Map
-- statement:
--   Definitions and structural lemmas for Not Dvd Super Index Iff Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/NotDvdSuperIndexIffMap.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone
import Definitions.Def_GroundTheory_ProfiniteCohomology_IsProPGroupSubgroupIffIsPGroupMap
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_exp_ofNat
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_ofNat_one
import Theorems.Thm_GroundTheory_ProfCoh_isProPGroup_subgroup_iff_isPGroup_map
import Theorems.Thm_GroundTheory_ProfCoh_not_dvd_superIndex_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.Supernatural.exp_ofNat
attribute [local simp] GroundTheory.ProfCoh.Supernatural.ofNat_one


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open Pointwise CategoryTheory
variable {G : Type*} [Group G]
theorem sup_eq_comap_map (H U : Subgroup G) [U.Normal] :
    H ⊔ U = (H.map (QuotientGroup.mk' U)).comap (QuotientGroup.mk' U) := by
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
theorem index_sup_eq_index_map (H U : Subgroup G) [U.Normal] :
    (H ⊔ U).index = (H.map (QuotientGroup.mk' U)).index := by
  rw [sup_eq_comap_map, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective U)]
variable [TopologicalSpace G]
noncomputable def quotMap {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    G ⧸ (U : Subgroup G) →* G ⧸ (V : Subgroup G) :=
  QuotientGroup.map _ _ (MonoidHom.id G) (fun _ hx => h hx)
theorem quotMap_comp_mk' {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    (quotMap h).comp (QuotientGroup.mk' (U : Subgroup G)) = QuotientGroup.mk' (V : Subgroup G) :=
  rfl
theorem quotMap_surjective {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    Function.Surjective (quotMap h) := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (V : Subgroup G) y
  exact ⟨QuotientGroup.mk' (U : Subgroup G) x, rfl⟩
theorem quotMap_self {U : OpenNormalSubgroup G} (h : U ≤ U) : quotMap h = MonoidHom.id _ :=
  MonoidHom.ext fun x => QuotientGroup.induction_on x fun _ => rfl
theorem quotMap_comp {U V W : OpenNormalSubgroup G} (h₁ : U ≤ V) (h₂ : V ≤ W) :
    (quotMap h₂).comp (quotMap h₁) = quotMap (h₁.trans h₂) :=
  MonoidHom.ext fun x => QuotientGroup.induction_on x fun _ => rfl
theorem map_map_quotMap (H : Subgroup G) {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    (H.map (QuotientGroup.mk' (U : Subgroup G))).map (quotMap h) =
      H.map (QuotientGroup.mk' (V : Subgroup G)) := by
  rw [Subgroup.map_map, quotMap_comp_mk']
def IsProSylow (p : ℕ) (P : Subgroup G) : Prop :=
  IsClosed (P : Set G) ∧ IsProPGroup p P ∧ ¬ Supernatural.ofNat p ∣ superIndex P
variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
variable {p : ℕ} [hp : Fact p.Prime]
omit [TotallyDisconnectedSpace G] in

theorem not_dvd_superIndex_iff_map (H : Subgroup G) :
    ¬ Supernatural.ofNat p ∣ superIndex H ↔
      ∀ U : OpenNormalSubgroup G, ¬ p ∣ (H.map (QuotientGroup.mk' (U : Subgroup G))).index := by
  have h := not_dvd_superIndex_iff (⟨p, hp.out⟩ : Nat.Primes) H
  simp only [index_sup_eq_index_map] at h
  exact h
noncomputable def IsProSylow.toSylow {P : Subgroup G} (hP : IsProSylow p P)
    (U : OpenNormalSubgroup G) : Sylow p (G ⧸ (U : Subgroup G)) :=
  IsPGroup.toSylow (isProPGroup_subgroup_iff_isPGroup_map.mp hP.2.1 U)
    ((not_dvd_superIndex_iff_map P).mp hP.2.2 U)
@[simp] theorem IsProSylow.coe_toSylow {P : Subgroup G} (hP : IsProSylow p P)
    (U : OpenNormalSubgroup G) :
    (hP.toSylow U : Subgroup (G ⧸ (U : Subgroup G))) = P.map (QuotientGroup.mk' (U : Subgroup G)) :=
  rfl
omit [CompactSpace G] [TotallyDisconnectedSpace G] in

noncomputable def sylowSystem (p : ℕ) [Fact p.Prime] (H : Subgroup G) :
    OpenNormalSubgroup G ⥤ Type _ where
  obj U := {S : Sylow p (G ⧸ (U : Subgroup G)) //
    H.map (QuotientGroup.mk' (U : Subgroup G)) ≤ (S : Subgroup (G ⧸ (U : Subgroup G)))}
  map {U V} f := ↾fun S => ⟨S.1.mapSurjective (quotMap_surjective (leOfHom f)), by
    rw [Sylow.coe_mapSurjective, ← map_map_quotMap H (leOfHom f)]
    exact Subgroup.map_mono S.2⟩
  map_id U := by
    ext ⟨S, hS⟩ x
    show x ∈ (S : Subgroup (G ⧸ (U : Subgroup G))).map (quotMap _) ↔
      x ∈ (S : Subgroup (G ⧸ (U : Subgroup G)))
    rw [quotMap_self, Subgroup.map_id]
  map_comp {U V W} f g := by
    ext ⟨S, hS⟩ x
    show x ∈ (S : Subgroup (G ⧸ (U : Subgroup G))).map (quotMap _) ↔
      x ∈ ((S : Subgroup (G ⧸ (U : Subgroup G))).map (quotMap (leOfHom f))).map
        (quotMap (leOfHom g))
    rw [Subgroup.map_map, quotMap_comp]
end GroundTheory.ProfCoh


