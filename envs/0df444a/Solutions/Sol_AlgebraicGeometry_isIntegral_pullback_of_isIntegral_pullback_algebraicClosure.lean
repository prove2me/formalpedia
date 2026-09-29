-- Prove2me | solution 1 for AlgebraicGeometry.isIntegral_pullback_of_isIntegral_pullback_algebraicClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/81f541af-f9fa-5a22-aba2-a66b15e7d9de

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIntegral_pullback_of_isIntegral_pullback_algebraicClosure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (K : Type) [Field K] [Algebra R K]
    (h : IsIntegral ↑(pullback f (Spec.map (CommRingCat.ofHom
      ((algebraMap K (AlgebraicClosure K)).comp (algebraMap R K)))))) :
    IsIntegral ↑(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by
  set ψ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R K)) with hψ
  set φ : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) with hφ
  have hcomp : Spec.map (CommRingCat.ofHom
      ((algebraMap K (AlgebraicClosure K)).comp (algebraMap R K))) = φ ≫ ψ := by
    rw [hφ, hψ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [hcomp] at h
  haveI := h
  let g : pullback f (φ ≫ ψ) ⟶ pullback f ψ :=
    (pullbackLeftPullbackSndIso f ψ φ).inv ≫ pullback.fst (pullback.snd f ψ) φ
  haveI : Surjective φ := by
    rw [hφ]
    exact ⟨fun y => ⟨⟨⊥, Ideal.bot_prime⟩, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  haveI : Flat φ := by rw [hφ]; infer_instance
  haveI : Surjective (pullback.fst (pullback.snd f ψ) φ) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  haveI : Flat (pullback.fst (pullback.snd f ψ) φ) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  haveI hsurj : Surjective g := by unfold g; infer_instance
  haveI hflat : Flat g := by unfold g; infer_instance
  haveI : Nonempty ↥(pullback f (φ ≫ ψ)) := inferInstance

  haveI : IrreducibleSpace ↥(pullback f ψ) := by
    have himg : IsIrreducible (Set.univ : Set ↥(pullback f ψ)) := by
      rw [← Set.image_univ_of_surjective g.surjective]
      exact (IrreducibleSpace.isIrreducible_univ _).image _ (by fun_prop)
    exact { isPreirreducible_univ := himg.isPreirreducible
            toNonempty := ⟨g.base (Classical.arbitrary _)⟩ }

  haveI : IsReduced ↑(pullback f ψ) := by
    haveI : ∀ y : ↥(pullback f ψ), IsReduced ↑((pullback f ψ).presheaf.stalk y) := by
      intro y
      obtain ⟨z, hz⟩ := g.surjective y
      subst hz
      haveI hzred : IsReduced ↑((pullback f (φ ≫ ψ)).presheaf.stalk z) := inferInstance

      letI : Algebra ↑((pullback f ψ).presheaf.stalk (g.base z))
                     ↑((pullback f (φ ≫ ψ)).presheaf.stalk z) :=
        (g.stalkMap z).hom.toAlgebra

      haveI hmf : Module.Flat ↑((pullback f ψ).presheaf.stalk (g.base z))
                              ↑((pullback f (φ ≫ ψ)).presheaf.stalk z) :=
        (Flat.iff_flat_stalkMap g).1 hflat z

      haveI hlh : IsLocalHom (algebraMap
          ↑((pullback f ψ).presheaf.stalk (g.base z))
          ↑((pullback f (φ ≫ ψ)).presheaf.stalk z)) :=
        inferInstanceAs (IsLocalHom (g.stalkMap z).hom)

      haveI hff : Module.FaithfullyFlat ↑((pullback f ψ).presheaf.stalk (g.base z))
                                        ↑((pullback f (φ ≫ ψ)).presheaf.stalk z) :=
        Module.FaithfullyFlat.of_flat_of_isLocalHom

      have hrff : (g.stalkMap z).hom.FaithfullyFlat := hff
      have hinj : Function.Injective (g.stalkMap z).hom := hrff.injective
      exact isReduced_of_injective (g.stalkMap z).hom hinj
    exact isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end
end S_AlgebraicGeometry_isIntegral_pullback_of_isIntegral_pullback_algebraicClosure
end P2MW
export P2MW.S_AlgebraicGeometry_isIntegral_pullback_of_isIntegral_pullback_algebraicClosure (solution)
