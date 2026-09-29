-- Prove2me | solution 1 for AlgebraicGeometry.bijective_kaehlerDifferential_map_comp_mapBaseChange_stalk_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/4c23a087-1069-5a56-b958-3399c87c7551

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk
import Theorems.Thm_KaehlerDifferential_bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_bijective_kaehlerDifferential_map_comp_mapBaseChange_stalk_pullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem solution
    {R : Type u} [CommRing R] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : Z ⟶ Spec (CommRingCat.of R))
    (p : ↥(pullback z f))
    [Algebra R (Z.presheaf.stalk ((pullback.fst z f).base p))]
    (halgZ : Z.fromSpecStalk ((pullback.fst z f).base p) ≫ z =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z f).base p)))))
    [Algebra R (X.presheaf.stalk ((pullback.snd z f).base p))]
    (halgX : X.fromSpecStalk ((pullback.snd z f).base p) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base p)))))
    [Algebra R ((pullback z f).presheaf.stalk p)] :
    letI : Algebra (Z.presheaf.stalk ((pullback.fst z f).base p)) ((pullback z f).presheaf.stalk p) :=
      ((pullback.fst z f).stalkMap p).hom.toAlgebra
    letI : Algebra (X.presheaf.stalk ((pullback.snd z f).base p)) ((pullback z f).presheaf.stalk p) :=
      ((pullback.snd z f).stalkMap p).hom.toAlgebra
    ∀ [IsScalarTower R (Z.presheaf.stalk ((pullback.fst z f).base p)) ((pullback z f).presheaf.stalk p)]
      [IsScalarTower R (X.presheaf.stalk ((pullback.snd z f).base p)) ((pullback z f).presheaf.stalk p)],
      Function.Bijective
        ((KaehlerDifferential.map R (Z.presheaf.stalk ((pullback.fst z f).base p))
              ((pullback z f).presheaf.stalk p) ((pullback z f).presheaf.stalk p)).restrictScalars
            ((pullback z f).presheaf.stalk p) ∘ₗ
          KaehlerDifferential.mapBaseChange R (X.presheaf.stalk ((pullback.snd z f).base p))
            ((pullback z f).presheaf.stalk p)) := by
  intro hTA hTB
  letI algA : Algebra (Z.presheaf.stalk ((pullback.fst z f).base p)) ((pullback z f).presheaf.stalk p) := ((pullback.fst z f).stalkMap p).hom.toAlgebra
  letI algB : Algebra (X.presheaf.stalk ((pullback.snd z f).base p)) ((pullback z f).presheaf.stalk p) := ((pullback.snd z f).stalkMap p).hom.toAlgebra
  obtain ⟨𝔔, h𝔔, e, he₁, he₂⟩ := AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk f z p halgZ halgX
  haveI : 𝔔.IsPrime := h𝔔

  letI algT : Algebra ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p))) ((pullback z f).presheaf.stalk p) :=
    (e.symm.toRingHom.comp (algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p))) (Localization.AtPrime 𝔔))).toAlgebra
  let eT : Localization.AtPrime 𝔔 ≃ₐ[((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p)))] ((pullback z f).presheaf.stalk p) :=
    AlgEquiv.ofRingEquiv (f := e.symm) (fun _ => rfl)
  haveI : IsLocalization 𝔔.primeCompl ((pullback z f).presheaf.stalk p) :=
    IsLocalization.isLocalization_of_algEquiv 𝔔.primeCompl eT
  haveI : IsScalarTower (Z.presheaf.stalk ((pullback.fst z f).base p)) ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p))) ((pullback z f).presheaf.stalk p) :=
    IsScalarTower.of_algebraMap_eq (R := (Z.presheaf.stalk ((pullback.fst z f).base p))) (S := ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p)))) (A := ((pullback z f).presheaf.stalk p)) fun s => by
    show ((pullback.fst z f).stalkMap p).hom s =
      e.symm (algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p))) (Localization.AtPrime 𝔔) (algebraMap (Z.presheaf.stalk ((pullback.fst z f).base p)) ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p))) s))
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, ← he₁,
      RingEquiv.symm_apply_apply]
  have hB : (algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p))) ((pullback z f).presheaf.stalk p)).comp
      (Algebra.TensorProduct.includeRight (R := R) (A := (Z.presheaf.stalk ((pullback.fst z f).base p))) (B := (X.presheaf.stalk ((pullback.snd z f).base p)))).toRingHom =
      algebraMap (X.presheaf.stalk ((pullback.snd z f).base p)) ((pullback z f).presheaf.stalk p) := by
    refine RingHom.ext fun t => ?_
    show e.symm (algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p))) (Localization.AtPrime 𝔔) (Algebra.TensorProduct.includeRight t)) =
      ((pullback.snd z f).stalkMap p).hom t
    rw [Algebra.TensorProduct.includeRight_apply, ← he₂, RingEquiv.symm_apply_apply]
  haveI : IsLocalization (⊥ : Submonoid (Z.presheaf.stalk ((pullback.fst z f).base p))) (Z.presheaf.stalk ((pullback.fst z f).base p)) := IsLocalization.self (by simp)
  exact KaehlerDifferential.bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct R (Z.presheaf.stalk ((pullback.fst z f).base p)) (Z.presheaf.stalk ((pullback.fst z f).base p)) (X.presheaf.stalk ((pullback.snd z f).base p)) ((pullback z f).presheaf.stalk p)
    (⊥ : Submonoid (Z.presheaf.stalk ((pullback.fst z f).base p))) hB 𝔔.primeCompl

end S_AlgebraicGeometry_bijective_kaehlerDifferential_map_comp_mapBaseChange_stalk_pullback
end P2MW
export P2MW.S_AlgebraicGeometry_bijective_kaehlerDifferential_map_comp_mapBaseChange_stalk_pullback (solution)
