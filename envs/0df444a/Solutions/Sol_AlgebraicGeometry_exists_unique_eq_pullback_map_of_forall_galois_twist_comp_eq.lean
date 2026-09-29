-- Prove2me | solution 1 for AlgebraicGeometry.exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/4bdcbf30-4a4d-58ce-8fa6-115324d24ddf

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_intermediateField_isGalois_galois_twist_comp_pullback_map_eq
import Theorems.Thm_AlgebraicGeometry_exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq_of_finiteDimensional
import Theorems.Thm_AlgebraicGeometry_eq_of_pullback_map_eq_pullback_map_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    (k K : Type) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (X Y : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] [IsSeparated fY] [LocallyOfFiniteType fY]
    (f : pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ pullback fY (Spec.map (CommRingCat.ofHom (algebraMap k K))))

    (hf : f ≫ pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k K))))

    (hgal : ∀ (σ : K ≃ₐ[k] K)
      (hσ : Spec.map (CommRingCat.ofHom ((σ : K →ₐ[k] K) : K →+* K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
        Spec.map (CommRingCat.ofHom (algebraMap k K))),
      pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          (𝟙 X) (Spec.map (CommRingCat.ofHom ((σ : K →ₐ[k] K) : K →+* K))) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hσ]) ≫ f =
        f ≫ pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          (𝟙 Y) (Spec.map (CommRingCat.ofHom ((σ : K →ₐ[k] K) : K →+* K))) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hσ])) :
    ∃ g : X ⟶ Y, ∃ hg : g ≫ fY = fX,
      f = pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            g (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hg]) (by rw [Category.comp_id, Category.id_comp]) ∧
      ∀ (g' : X ⟶ Y) (hg' : g' ≫ fY = fX),
        f = pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))
              g' (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hg']) (by rw [Category.comp_id, Category.id_comp]) →
        g' = g := by
  classical

  obtain ⟨L, hLfin, hLgal, gL, hι, hgL, hgalL, hsq⟩ :=
    AlgebraicGeometry.exists_intermediateField_isGalois_galois_twist_comp_pullback_map_eq k K X Y fX fY f hf hgal
  haveI := hLfin
  haveI := hLgal

  obtain ⟨g, hg, hgeq, _huniqL⟩ := AlgebraicGeometry.exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq_of_finiteDimensional k L X Y fX fY gL hgL hgalL
  refine ⟨g, hg, ?_, ?_⟩
  ·
    apply pullback.hom_ext
    ·
      have h1 : f ≫ pullback.fst fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
          (f ≫ pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 Y) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι])) ≫
            pullback.fst fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
        rw [Category.assoc, pullback.lift_fst, Category.comp_id]
      rw [h1, hsq, Category.assoc, hgeq, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, Category.comp_id,
        pullback.lift_fst]
    · rw [hf, pullback.lift_snd, Category.comp_id]
  ·
    intro g' hg' hfeq
    refine AlgebraicGeometry.eq_of_pullback_map_eq_pullback_map_of_isSeparated k K X Y fX fY g' g hg' hg ?_
    rw [← hfeq]
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      have h1 : f ≫ pullback.fst fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
          (f ≫ pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 Y) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι])) ≫
            pullback.fst fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
        rw [Category.assoc, pullback.lift_fst, Category.comp_id]
      rw [h1, hsq, Category.assoc, hgeq, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, Category.comp_id]
    · rw [hf, pullback.lift_snd, Category.comp_id]

end S_AlgebraicGeometry_exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq (solution)
