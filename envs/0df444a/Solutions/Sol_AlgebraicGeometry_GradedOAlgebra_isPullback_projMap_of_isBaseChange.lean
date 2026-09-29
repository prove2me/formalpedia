-- Prove2me | solution 1 for AlgebraicGeometry.GradedOAlgebra.isPullback_projMap_of_isBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/1947fc91-509f-55c5-a112-33ceaeaf3d0e

import Mathlib
import Theorems.Thm_HomogeneousLocalization_Away_isPushout_map_of_isBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_isPullback_projMap_of_isBaseChange

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization

theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (R' : Type u) [CommRing R'] [Algebra S' R'] [Algebra S R'] [IsScalarTower S S' R']
    (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
    (ϑ : R →ₐ[S] R') (hϑdeg : ∀ n, ∀ x ∈ 𝓡 n, ϑ x ∈ 𝓡' n)
    (hbc : ∀ n, IsBaseChange S' ((ϑ.toLinearMap.restrict (p := 𝓡 n) (q := (𝓡' n).restrictScalars S) (hϑdeg n))
      : 𝓡 n →ₗ[S] (𝓡' n).restrictScalars S))
    (hirr : HomogeneousIdeal.irrelevant 𝓡' ≤
      (HomogeneousIdeal.irrelevant 𝓡).map ({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡')) :
    IsPullback (Proj.map ({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡') hirr)
      (Proj.toSpecZero 𝓡' ≫ Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' 𝓡').comp (algebraMap S' R'))))
      (Proj.toSpecZero 𝓡 ≫ Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' 𝓡).comp (algebraMap S R))))
      (Spec.map (CommRingCat.ofHom (algebraMap S S'))) := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (Proj.affineOpenCover 𝓡).openCover ?_
  rintro ⟨⟨m, hm⟩, ⟨r, hr⟩⟩

  have sq1 : IsPullback
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map ({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡') r)))
      (Proj.awayι 𝓡' (({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡') r) (hϑdeg _ _ hr) hm) (Proj.awayι 𝓡 r hr hm)
      (Proj.map ({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡') hirr) :=
    IsOpenImmersion.isPullback _ _ _ _ (Proj.awayι_comp_map _ hirr hm r hr)
      (by rw [Proj.opensRange_awayι, Proj.opensRange_awayι, Proj.map_preimage_basicOpen])

  have sq2 := AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _
    (HomogeneousLocalization.Away.isPushout_map_of_isBaseChange S' R 𝓡 R' 𝓡' ϑ hϑdeg hbc r hr)
  have h1 := sq1.flip.isoPullback_hom_fst
  have h2 := sq1.flip.isoPullback_hom_snd
  refine sq2.of_iso sq1.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans h2.symm
  · rw [← Category.assoc]
    erw [Category.comp_id, h1, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · simp only [Scheme.AffineOpenCover.openCover_f, Proj.affineOpenCover_f]
    erw [Category.comp_id, Category.id_comp, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

end S_AlgebraicGeometry_GradedOAlgebra_isPullback_projMap_of_isBaseChange
end P2MW
export P2MW.S_AlgebraicGeometry_GradedOAlgebra_isPullback_projMap_of_isBaseChange (solution)
