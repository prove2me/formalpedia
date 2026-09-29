-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_locIsoOnBase_pullback_of_forall_away_of_locIsoOnBase
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/62cc85e2-ddd8-5337-a524-ab04a71c759a

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_tensor_pullback_of_isInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_pullback_dual_pullback_and_nonempty_pullback_iso_unit_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_isPullback_specMap_awayToAwayRight_awayToAwayLeft
import Theorems.Thm_AlgebraicGeometry_Scheme_surjective_appTop_and_forall_away_of_isPullback_of_forall_surjective_appTop_away
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isPullback_fst_awayToAwayRight_and_isPullback_snd_awayToAwayLeft
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_pullback_iso_of_charts_of_rigidified_of_surjective_appTop
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_locIsoOnBase_pullback_of_forall_away_of_locIsoOnBase
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u v

namespace Z1R3

theorem locIsoOnBase_of_iso {S' : Type u} [CommRing S'] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S'))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

theorem nonempty_restrict_iso_of_eq {X : Scheme.{u}} {W₁ W₂ : X.Opens} (h : W₁ = W₂) (A B : X.Modules)
    (hAB : Nonempty ((Scheme.Modules.pullback W₂.ι).obj A ≅ (Scheme.Modules.pullback W₂.ι).obj B)) :
    Nonempty ((Scheme.Modules.pullback W₁.ι).obj A ≅ (Scheme.Modules.pullback W₁.ι).obj B) := by
  subst h; exact hAB

theorem awayToAwayRight_comp_algebraMap {S : Type u} [CommRing S] (a b : S) :
    (IsLocalization.Away.awayToAwayRight a b : Localization.Away a →+* Localization.Away (a * b)).comp
      (algebraMap S (Localization.Away a)) = algebraMap S (Localization.Away (a * b)) :=
  RingHom.ext fun x => IsLocalization.Away.awayToAwayRight_eq a b x

end Z1R3

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (e : Spec (CommRingCat.of S) ⟶ A) (he : e ≫ f = 𝟙 _)
    (hΓ : ∀ r : S, Function.Surjective
      ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))).appTop).hom)
    {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (A' : Fin k → Scheme.{u}) (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (Localization.Away (r i))))
    (g : ∀ i, A' i ⟶ A)
    (hg : ∀ i, IsPullback (g i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))))
    (e' : ∀ i, Spec (CommRingCat.of (Localization.Away (r i))) ⟶ A' i) (he' : ∀ i, e' i ≫ f' i = 𝟙 _)
    (hee' : ∀ i, e' i ≫ g i = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) ≫ e)
    (M : ∀ i, (A' i).Modules) (hM : ∀ i, Scheme.Modules.IsInvertible (M i))
    (hagree : ∀ (i j : Fin k) (Aij : Scheme.{u})
      (fij : Aij ⟶ Spec (CommRingCat.of (Localization.Away (r i * r j))))
      (pi : Aij ⟶ A' i) (pj : Aij ⟶ A' j),
      IsPullback pi fij (f' i)
        (Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight (r i) (r j) :
          Localization.Away (r i) →+* Localization.Away (r i * r j)))) →
      IsPullback pj fij (f' j)
        (Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayLeft (r j) (r i) :
          Localization.Away (r j) →+* Localization.Away (r i * r j)))) →
      pi ≫ g i = pj ≫ g j →
      LocIsoOnBase fij ((Scheme.Modules.pullback pi).obj (M i)) ((Scheme.Modules.pullback pj).obj (M j))) :
    ∃ Mg : A.Modules, Scheme.Modules.IsInvertible Mg ∧
      ∀ i, Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (g i)).obj Mg) ∧
        LocIsoOnBase (f' i) ((Scheme.Modules.pullback (g i)).obj Mg) (M i) := by
  classical

  haveI hgopen : ∀ i, IsOpenImmersion (g i) := fun i =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) (hg i).flip
      (Scheme.isOpenImmersion_SpecMap_localizationAway (R := CommRingCat.of S) (r i))

  have hN : ∀ i, Scheme.Modules.IsInvertible
      (Scheme.Modules.dual ((Scheme.Modules.pullback (e' i)).obj (M i))) :=
    fun i => ((hM i).pullback (e' i)).dual_monoidalV2.1
  have hR : ∀ i, Scheme.Modules.IsInvertible
        (M i ⊗ (Scheme.Modules.pullback (f' i)).obj (Scheme.Modules.dual ((Scheme.Modules.pullback (e' i)).obj (M i)))) ∧
      Nonempty ((Scheme.Modules.pullback (e' i)).obj
        (M i ⊗ (Scheme.Modules.pullback (f' i)).obj (Scheme.Modules.dual ((Scheme.Modules.pullback (e' i)).obj (M i)))) ≅
        𝟙_ _) :=
    fun i => AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor_pullback_dual_pullback_and_nonempty_pullback_iso_unit_monoidalV2
      (he' i) (hM i)
  have hRM : ∀ i, LocIsoOnBase (f' i)
      (M i ⊗ (Scheme.Modules.pullback (f' i)).obj (Scheme.Modules.dual ((Scheme.Modules.pullback (e' i)).obj (M i)))) (M i) :=
    fun i => AlgebraicGeometry.Polarisation.locIsoOnBase_tensor_pullback_of_isInvertible (f' i) (M i) _ (hN i)

  have hsurj : ∀ y : ↥A, ∃ (i : Fin k) (x : ↥(A' i)), (g i).base x = y := by
    intro y
    obtain ⟨i, hi⟩ : ∃ i, r i ∉ (f.base y).asIdeal := by
      by_contra h
      push_neg at h
      have hle : Ideal.span (Set.range r) ≤ (f.base y).asIdeal :=
        Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
      rw [hr, top_le_iff] at hle
      exact (f.base y).isPrime.ne_top hle
    obtain ⟨s', hs'⟩ : ∃ s' : PrimeSpectrum (Localization.Away (r i)),
        PrimeSpectrum.comap (algebraMap S (Localization.Away (r i))) s' = f.base y := by
      rw [← Set.mem_range, PrimeSpectrum.localization_away_comap_range _ (r i)]; exact hi
    have hy : y ∈ Set.range (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))))).base := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨s', hs'⟩
    obtain ⟨z, hz⟩ := hy
    refine ⟨i, (hg i).isoPullback.inv.base z, ?_⟩
    have h := congrArg (fun φ => φ.base z) (hg i).isoPullback_inv_fst
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at h
    exact h.trans hz

  have hΓ' : ∀ i, Function.Surjective ((f' i).appTop).hom ∧
      ∀ r' : Localization.Away (r i), Function.Surjective
        ((pullback.snd (f' i) (Spec.map (CommRingCat.ofHom
          (algebraMap (Localization.Away (r i)) (Localization.Away r'))))).appTop).hom := fun i =>
    AlgebraicGeometry.Scheme.surjective_appTop_and_forall_away_of_isPullback_of_forall_surjective_appTop_away
      f hΓ (r i) (Localization.Away (r i)) (f' i) (g i) (hg i)

  have heagree : ∀ (i j : Fin k) (C : Type u) [CommRing C] [Algebra S C] [IsLocalization.Away (r i * r j) C]
      (ρ₁ : Localization.Away (r i) →ₐ[S] C) (ρ₂ : Localization.Away (r j) →ₐ[S] C),
      Spec.map (CommRingCat.ofHom ρ₁.toRingHom) ≫ e' i ≫ g i = Spec.map (CommRingCat.ofHom ρ₂.toRingHom) ≫ e' j ≫ g j := by
    intro i j C _ _ _ ρ₁ ρ₂
    have key : ∀ (l : Fin k) (ρ : Localization.Away (r l) →ₐ[S] C),
        Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ e' l ≫ g l = Spec.map (CommRingCat.ofHom (algebraMap S C)) ≫ e := by
      intro l ρ
      have hc : ρ.toRingHom.comp (algebraMap S (Localization.Away (r l))) = algebraMap S C :=
        RingHom.ext fun x => ρ.commutes x
      rw [hee' l, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
    rw [key i ρ₁, key j ρ₂]

  have hloc : ∀ (i j : Fin k) (q : ↥(Limits.pullback (g i) (g j))), ∃ U : (Spec (CommRingCat.of S)).Opens,
      (pullback.fst (g i) (g j) ≫ g i ≫ f).base q ∈ U ∧
      Nonempty
        ((Scheme.Modules.pullback ((pullback.fst (g i) (g j) ≫ g i ≫ f) ⁻¹ᵁ U).ι).obj
            ((Scheme.Modules.pullback (pullback.fst (g i) (g j))).obj
              (M i ⊗ (Scheme.Modules.pullback (f' i)).obj (Scheme.Modules.dual ((Scheme.Modules.pullback (e' i)).obj (M i))))) ≅
          (Scheme.Modules.pullback ((pullback.fst (g i) (g j) ≫ g i ≫ f) ⁻¹ᵁ U).ι).obj
            ((Scheme.Modules.pullback (pullback.snd (g i) (g j))).obj
              (M j ⊗ (Scheme.Modules.pullback (f' j)).obj (Scheme.Modules.dual ((Scheme.Modules.pullback (e' j)).obj (M j)))))) := by
    intro i j q
    obtain ⟨fij, sqi, sqj⟩ := AlgebraicGeometry.Scheme.exists_isPullback_fst_awayToAwayRight_and_isPullback_snd_awayToAwayLeft f r A' f' g hg i j

    have hag := hagree i j (Limits.pullback (g i) (g j)) fij (pullback.fst (g i) (g j)) (pullback.snd (g i) (g j))
      sqi sqj pullback.condition

    have hNi' := (hN i).pullback (Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight (r i) (r j) :
          Localization.Away (r i) →+* Localization.Away (r i * r j))))
    have hNj' := (hN j).pullback (Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayLeft (r j) (r i) :
          Localization.Away (r j) →+* Localization.Away (r i * r j))))
    have hRi : LocIsoOnBase fij
        ((Scheme.Modules.pullback (pullback.fst (g i) (g j))).obj
          (M i ⊗ (Scheme.Modules.pullback (f' i)).obj (Scheme.Modules.dual ((Scheme.Modules.pullback (e' i)).obj (M i)))))
        ((Scheme.Modules.pullback (pullback.fst (g i) (g j))).obj (M i)) := by
      refine (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence fij).trans (Z1R3.locIsoOnBase_of_iso fij ?_)
        (AlgebraicGeometry.Polarisation.locIsoOnBase_tensor_pullback_of_isInvertible fij _ _ hNi')
      exact AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
        whiskerLeftIso _ ((Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr sqi.w).app _ ≪≫
          ((Scheme.Modules.pullbackComp _ _).app _).symm)
    have hRj : LocIsoOnBase fij
        ((Scheme.Modules.pullback (pullback.snd (g i) (g j))).obj
          (M j ⊗ (Scheme.Modules.pullback (f' j)).obj (Scheme.Modules.dual ((Scheme.Modules.pullback (e' j)).obj (M j)))))
        ((Scheme.Modules.pullback (pullback.snd (g i) (g j))).obj (M j)) := by
      refine (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence fij).trans (Z1R3.locIsoOnBase_of_iso fij ?_)
        (AlgebraicGeometry.Polarisation.locIsoOnBase_tensor_pullback_of_isInvertible fij _ _ hNj')
      exact AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
        whiskerLeftIso _ ((Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr sqj.w).app _ ≪≫
          ((Scheme.Modules.pullbackComp _ _).app _).symm)
    have hRR := (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence fij).trans
      ((AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence fij).trans hRi hag)
      ((AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence fij).symm hRj)

    set φ : Spec (CommRingCat.of (Localization.Away (r i * r j))) ⟶ Spec (CommRingCat.of S) :=
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i * r j)))) with hφ
    haveI : IsOpenImmersion φ := by
      rw [hφ]; exact Scheme.isOpenImmersion_SpecMap_localizationAway (R := CommRingCat.of S) (r i * r j)
    have hcomp : pullback.fst (g i) (g j) ≫ g i ≫ f = fij ≫ φ := by
      rw [(hg i).w, ← Category.assoc, sqi.w, Category.assoc, hφ, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        Z1R3.awayToAwayRight_comp_algebraMap]
    obtain ⟨V, hqV, hV⟩ := hRR (fij.base q)
    refine ⟨φ ''ᵁ V, ?_, ?_⟩
    · rw [hcomp, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
      exact ⟨fij.base q, hqV, rfl⟩
    · have hW : (pullback.fst (g i) (g j) ≫ g i ≫ f) ⁻¹ᵁ (φ ''ᵁ V) = fij ⁻¹ᵁ V := by
        rw [hcomp, Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq]
      exact Z1R3.nonempty_restrict_iso_of_eq hW _ _ hV

  obtain ⟨Mg, hMg, hiso⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_pullback_iso_of_charts_of_rigidified_of_surjective_appTop
      r hr (fun i => Localization.Away (r i)) f f' g hg hsurj hΓ' e' he' heagree
      (fun i => M i ⊗ (Scheme.Modules.pullback (f' i)).obj (Scheme.Modules.dual ((Scheme.Modules.pullback (e' i)).obj (M i))))
      (fun i => (hR i).1) (fun i => (hR i).2) hloc
  refine ⟨Mg, hMg, fun i => ⟨hMg.pullback (g i), ?_⟩⟩
  obtain ⟨φi⟩ := hiso i
  exact (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence (f' i)).trans
    (Z1R3.locIsoOnBase_of_iso (f' i) φi) (hRM i)

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_locIsoOnBase_pullback_of_forall_away_of_locIsoOnBase
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_locIsoOnBase_pullback_of_forall_away_of_locIsoOnBase (solution)
