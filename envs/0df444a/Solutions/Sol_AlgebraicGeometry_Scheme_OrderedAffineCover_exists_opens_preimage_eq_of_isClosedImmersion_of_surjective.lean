-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.OrderedAffineCover.exists_opens_preimage_eq_of_isClosedImmersion_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/bb720fa3-e6e0-59f1-91e7-efacf7a2c3c4

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Theorems.Thm_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_opens_preimage_eq_of_isClosedImmersion_of_surjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {P' P : Scheme.{u}} (j : P' ⟶ P) [IsClosedImmersion j] [Surjective j] (𝒲 : P'.OrderedAffineCover) :
    ∃ (V : 𝒲.ι → P.Opens), (∀ w, IsAffineOpen (V w)) ∧ (⨆ w, V w = ⊤) ∧ (∀ w, j ⁻¹ᵁ (V w) = 𝒲.U w) ∧
      (∀ (U : P.Opens) (w : 𝒲.ι), 𝒲.U w ≤ j ⁻¹ᵁ U → V w ≤ U) := by
  classical
  have hce : Topology.IsClosedEmbedding j.base := j.isClosedEmbedding
  have hinj : Function.Injective j.base := hce.injective
  have hsurj : Function.Surjective j.base := j.surjective
  have hbij : Function.Bijective j.base := ⟨hinj, hsurj⟩

  have hopen : ∀ O : Set P', IsOpen O → IsOpen (j.base '' O) := by
    intro O hO
    have h1 : j.base '' O = (j.base '' Oᶜ)ᶜ := by rw [Set.image_compl_eq hbij, compl_compl]
    rw [h1, isOpen_compl_iff]
    exact hce.isClosedMap _ hO.isClosed_compl
  let V : 𝒲.ι → P.Opens := fun w => ⟨j.base '' (𝒲.U w : Set P'), hopen _ (𝒲.U w).isOpen⟩
  have hpre : ∀ w, j ⁻¹ᵁ (V w) = 𝒲.U w := by
    intro w
    ext x
    change j.base x ∈ j.base '' (𝒲.U w : Set P') ↔ x ∈ (𝒲.U w : Set P')
    exact hinj.mem_set_image
  refine ⟨V, ?_, ?_, hpre, ?_⟩
  · intro w
    have h1 : IsAffineOpen (j ⁻¹ᵁ (V w)) := by rw [hpre]; exact 𝒲.isAffineOpen w
    haveI : IsAffine (↑(j ⁻¹ᵁ (V w)) : Scheme.{u}) := h1
    haveI : IsClosedImmersion (j ∣_ V w) := IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) (inferInstance : IsClosedImmersion j) (V w)
    haveI : Surjective (j ∣_ V w) := IsZariskiLocalAtTarget.restrict (P := @Surjective) (inferInstance : Surjective j) (V w)
    exact AlgebraicGeometry.isAffine_of_isClosedImmersion_of_surjective (j ∣_ V w)
  · refine le_antisymm le_top ?_
    intro y _
    obtain ⟨x, rfl⟩ := hsurj y
    have hx : x ∈ (⊤ : P'.Opens) := trivial
    rw [← 𝒲.iSup_eq_top, TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨w, hw⟩ := hx
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨w, ⟨x, hw, rfl⟩⟩
  · intro U w hle y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hle hx

end S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_opens_preimage_eq_of_isClosedImmersion_of_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_opens_preimage_eq_of_isClosedImmersion_of_surjective (solution)
