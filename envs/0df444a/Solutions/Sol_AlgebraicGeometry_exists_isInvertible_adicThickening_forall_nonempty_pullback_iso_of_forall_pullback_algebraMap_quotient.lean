-- Prove2me | solution 1 for AlgebraicGeometry.exists_isInvertible_adicThickening_forall_nonempty_pullback_iso_of_forall_pullback_algebraMap_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/c0df5ede-95c1-5820-89f2-331b72bd0de1

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isInvertible_adicThickening_forall_nonempty_pullback_iso_of_forall_pullback_algebraMap_quotient

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

noncomputable section

namespace TransportBridgeSol

variable {S R : Type u} [CommRing S] [CommRing R] [Algebra S R] (I : Ideal R)
  {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of S))

abbrev sR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S R))

abbrev sQ (k : ℕ) : Spec (CommRingCat.of (R ⧸ I ^ (k + 1))) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1))))

abbrev mkQ (k : ℕ) : Spec (CommRingCat.of (R ⧸ I ^ (k + 1))) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (k + 1))))

theorem mkQ_comp_sR (k : ℕ) : mkQ I k ≫ sR (S := S) (R := R) = sQ (S := S) I k := by
  rw [mkQ, sR, sQ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

scoped instance mono_mkQ (k : ℕ) : Mono (mkQ I k) := by
  haveI : IsClosedImmersion (mkQ I k) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

noncomputable def e (k : ℕ) :
    adicThickening (pullback.snd g (sR (S := S) (R := R))) I k ≅ pullback g (sQ (S := S) I k) :=
  pullbackLeftPullbackSndIso g (sR (S := S) (R := R)) (mkQ I k) ≪≫ pullback.congrHom rfl (mkQ_comp_sR I k)

theorem e_hom_fst (k : ℕ) :
    (e I g k).hom ≫ pullback.fst g (sQ (S := S) I k) =
      adicThickeningι (pullback.snd g (sR (S := S) (R := R))) I k ≫ pullback.fst g (sR (S := S) (R := R)) := by
  rw [adicThickeningι_def]
  simp only [e, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]
  exact pullbackLeftPullbackSndIso_hom_fst g sR (mkQ I k)

theorem e_hom_snd (k : ℕ) :
    (e I g k).hom ≫ pullback.snd g (sQ (S := S) I k) =
      adicThickeningToBase (pullback.snd g (sR (S := S) (R := R))) I k := by
  rw [adicThickeningToBase_def]
  simp only [e, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
  exact pullbackLeftPullbackSndIso_hom_snd g sR (mkQ I k)

end TransportBridgeSol
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isInvertible_adicThickening_forall_nonempty_pullback_iso_of_forall_pullback_algebraMap_quotient.TransportBridgeSol"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isInvertible_adicThickening_forall_nonempty_pullback_iso_of_forall_pullback_algebraMap_quotient.TransportBridgeSol"

open TransportBridgeSol in
theorem solution
    {S R : Type u} [CommRing S] [CommRing R] [Algebra S R] (I : Ideal R)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of S))

    (j : ∀ k : ℕ, pullback g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1))))) ⟶
      pullback g (Spec.map (CommRingCat.ofHom (algebraMap S R))))
    (hj₁ : ∀ k, j k ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap S R))) =
      pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1))))))
    (hj₂ : ∀ k, j k ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S R))) =
      pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1))))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (k + 1)))))
    (t : ∀ k : ℕ, pullback g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1))))) ⟶
      pullback g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1 + 1))))))
    (ht₁ : ∀ k, t k ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1 + 1))))) =
      pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1))))))
    (ht : ∀ k, t k ≫ j (k + 1) = j k)

    (𝓛k : ∀ k : ℕ, (pullback g (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ I ^ (k + 1)))))).Modules)
    (hinv : ∀ k, Scheme.Modules.IsInvertible (𝓛k k))
    (hcompat : ∀ k : ℕ, Nonempty ((Scheme.Modules.pullback (t k)).obj (𝓛k (k + 1)) ≅ 𝓛k k)) :
    ∃ L : ∀ n : ℕ, (adicThickening (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S R)))) I n).Modules,
      (∀ n, Scheme.Modules.IsInvertible (L n)) ∧
      (∀ n, Nonempty ((Scheme.Modules.pullback
        (adicThickeningTransition (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S R)))) I n)).obj
          (L (n + 1)) ≅ L n)) ∧
      ∀ M : (pullback g (Spec.map (CommRingCat.ofHom (algebraMap S R)))).Modules,
        (∀ n, Nonempty ((Scheme.Modules.pullback
          (adicThickeningι (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S R)))) I n)).obj M ≅ L n)) →
        ∀ k : ℕ, Nonempty ((Scheme.Modules.pullback (j k)).obj M ≅ 𝓛k k) := by

  have hej : ∀ k, (e I g k).hom ≫ j k =
      adicThickeningι (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S R)))) I k := by
    intro k
    apply pullback.hom_ext
    · rw [Category.assoc, hj₁, e_hom_fst]
    · rw [Category.assoc, hj₂, ← Category.assoc, e_hom_snd, adicThickeningι_def, adicThickeningToBase_def]
      exact pullback.condition.symm

  have het : ∀ k, adicThickeningTransition (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S R)))) I k ≫
      (e I g (k + 1)).hom = (e I g k).hom ≫ t k := by
    intro k
    have h1 : (adicThickeningTransition (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S R)))) I k ≫
        (e I g (k + 1)).hom) ≫ j (k + 1) = ((e I g k).hom ≫ t k) ≫ j (k + 1) := by
      simp only [Category.assoc]
      rw [ht, hej, hej, adicThickeningTransition_ι]
    have h2 := h1 =≫ pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S R)))
    simp only [Category.assoc] at h2
    rw [hj₂] at h2
    apply pullback.hom_ext
    · rw [Category.assoc, e_hom_fst, ← Category.assoc, adicThickeningTransition_ι, Category.assoc, ht₁,
        e_hom_fst]
    · rw [← cancel_mono (mkQ I (k + 1))]
      simpa only [Category.assoc] using h2

  refine ⟨fun n => (Scheme.Modules.pullback (e I g n).hom).obj (𝓛k n),
    fun n => (hinv n).pullback (e I g n).hom, fun n => ?_, fun M hM k => ?_⟩
  ·
    obtain ⟨c⟩ := hcompat n
    exact ⟨(Scheme.Modules.pullbackComp
        (adicThickeningTransition (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S R)))) I n)
        (e I g (n + 1)).hom).app (𝓛k (n + 1)) ≪≫
      (Scheme.Modules.pullbackCongr (het n)).app (𝓛k (n + 1)) ≪≫
      ((Scheme.Modules.pullbackComp (e I g n).hom (t n)).app (𝓛k (n + 1))).symm ≪≫
      (Scheme.Modules.pullback (e I g n).hom).mapIso c⟩
  ·
    obtain ⟨c⟩ := hM k
    have hjk : j k = (e I g k).inv ≫
        adicThickeningι (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S R)))) I k := by
      rw [← hej, Iso.inv_hom_id_assoc]
    exact ⟨(Scheme.Modules.pullbackCongr hjk).app M ≪≫
      ((Scheme.Modules.pullbackComp (e I g k).inv
        (adicThickeningι (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap S R)))) I k)).app M).symm ≪≫
      (Scheme.Modules.pullback (e I g k).inv).mapIso c ≪≫
      (Scheme.Modules.pullbackComp (e I g k).inv (e I g k).hom).app (𝓛k k) ≪≫
      (Scheme.Modules.pullbackCongr (e I g k).inv_hom_id).app (𝓛k k) ≪≫
      (Scheme.Modules.pullbackId _).app (𝓛k k)⟩

end S_AlgebraicGeometry_exists_isInvertible_adicThickening_forall_nonempty_pullback_iso_of_forall_pullback_algebraMap_quotient
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isInvertible_adicThickening_forall_nonempty_pullback_iso_of_forall_pullback_algebraMap_quotient (solution)
