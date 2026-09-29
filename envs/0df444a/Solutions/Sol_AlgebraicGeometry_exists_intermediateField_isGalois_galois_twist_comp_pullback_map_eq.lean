-- Prove2me | solution 1 for AlgebraicGeometry.exists_intermediateField_isGalois_galois_twist_comp_pullback_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f93e0808-70de-5bcc-a5f6-eec0c7c97530

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_intermediateField_finiteDimensional_comp_pullback_map_eq_of_isAlgebraic
import Theorems.Thm_AlgebraicGeometry_eq_of_pullback_map_eq_pullback_map_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_intermediateField_isGalois_galois_twist_comp_pullback_map_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LiftTwistAux

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section pullbackMap
variable {C : Type*} [Category C] {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
  (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
  (e₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (e₂ : f₂ ≫ i₃ = i₂ ≫ g₂)

@[reassoc]
theorem map_fst' : pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ e₁ e₂ ≫ pullback.fst g₁ g₂ = pullback.fst f₁ f₂ ≫ i₁ :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem map_snd' : pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ e₁ e₂ ≫ pullback.snd g₁ g₂ = pullback.snd f₁ f₂ ≫ i₂ :=
  pullback.lift_snd _ _ _

end pullbackMap

variable {k : Type} [Field k]

theorem specMap_algEquiv_comp {F : Type} [Field F] [Algebra k F] (τ : F ≃ₐ[k] F) :
    Spec.map (CommRingCat.ofHom ((τ : F →ₐ[k] F) : F →+* F)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k F)) =
      Spec.map (CommRingCat.ofHom (algebraMap k F)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (τ : F →ₐ[k] F).comp_algebraMap

theorem specMap_algEquiv_symm_comp {F : Type} [Field F] [Algebra k F] (τ : F ≃ₐ[k] F) :
    Spec.map (CommRingCat.ofHom ((τ : F →ₐ[k] F) : F →+* F)) ≫
      Spec.map (CommRingCat.ofHom ((τ.symm : F →ₐ[k] F) : F →+* F)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id, ← CommRingCat.ofHom_id]
  congr 2
  ext x
  exact τ.apply_symm_apply x

theorem specMap_algEquiv_symm_comp' {F : Type} [Field F] [Algebra k F] (τ : F ≃ₐ[k] F) :
    Spec.map (CommRingCat.ofHom ((τ.symm : F →ₐ[k] F) : F →+* F)) ≫
      Spec.map (CommRingCat.ofHom ((τ : F →ₐ[k] F) : F →+* F)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id, ← CommRingCat.ofHom_id]
  congr 2
  ext x
  exact τ.symm_apply_apply x

end LiftTwistAux

namespace LiftTwistAux

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem eq_of_comp_eq_of_isSchemeTheoreticallyDominant {X' X Y : Scheme.{0}} (m : X' ⟶ X)
    [IsSchemeTheoreticallyDominant m] [Y.IsSeparated] (g₁ g₂ : X ⟶ Y) (h : m ≫ g₁ = m ≫ g₂) : g₁ = g₂ := by
  let e := equalizer.ι g₁ g₂
  haveI : IsClosedImmersion e := inferInstance
  let l := equalizer.lift _ h
  have hl : l ≫ e = m := equalizer.lift_ι _ _
  have hker : e.ker = ⊥ := by
    apply le_bot_iff.mp
    have := Scheme.Hom.le_ker_comp l e
    rw [hl, Scheme.Hom.ker_eq_bot m] at this
    exact this
  haveI : IsIso e := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  exact eq_of_epi_equalizer

theorem isSchemeTheoreticallyDominant_specMap_of_injective'
    {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : Function.Injective φ) :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom φ)) := by
  rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine]
  have hinj : Function.Injective (Spec.map (CommRingCat.ofHom φ)).appTop.hom := by
    have e : (Spec.map (CommRingCat.ofHom φ)).appTop =
        (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).inv := by
      rw [← Iso.inv_comp_eq]
      exact (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm
    have i1 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv).1
    have i2 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
    rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, RingHom.coe_comp]
    exact (i1.comp hφ).comp i2
  rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp [Scheme.IdealSheafData.ideal_bot]

theorem isSchemeTheoreticallyDominant_levelMap
    {k K : Type} [Field k] [Field K] [Algebra k K] {X : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of k))
    (L : IntermediateField k K)
    (hι : Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
        Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    IsSchemeTheoreticallyDominant
      (pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX (Spec.map (CommRingCat.ofHom (algebraMap k L)))
        (𝟙 X) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι])) := by
  set ι := Spec.map (CommRingCat.ofHom (algebraMap L K)) with hιdef
  set gL := Spec.map (CommRingCat.ofHom (algebraMap k L)) with hgL
  set gK := Spec.map (CommRingCat.ofHom (algebraMap k K)) with hgK
  haveI : IsSchemeTheoreticallyDominant ι :=
    isSchemeTheoreticallyDominant_specMap_of_injective' (algebraMap L K) (algebraMap L K).injective
  haveI : IsSchemeTheoreticallyDominant (pullback.fst (pullback.snd fX gL) ι) := inferInstance

  let Φ : pullback (pullback.snd fX gL) ι ≅ pullback fX gK :=
    pullbackLeftPullbackSndIso fX gL ι ≪≫ pullback.congrHom rfl hι
  have hΦ : Φ.hom ≫ pullback.map fX gK fX gL (𝟙 X) ι (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) =
      pullback.fst (pullback.snd fX gL) ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, map_fst', Category.comp_id]
      change ((pullbackLeftPullbackSndIso fX gL ι).hom ≫ (pullback.congrHom rfl hι).hom) ≫ pullback.fst fX gK = _
      rw [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
    · rw [Category.assoc, map_snd']
      change ((pullbackLeftPullbackSndIso fX gL ι).hom ≫ (pullback.congrHom rfl hι).hom) ≫ pullback.snd fX gK ≫ ι = _
      rw [Category.assoc, ← Category.assoc (pullback.congrHom rfl hι).hom, pullback.congrHom_hom, pullback.lift_snd,
        Category.comp_id, ← Category.assoc, pullbackLeftPullbackSndIso_hom_snd]
      exact pullback.condition.symm
  have : pullback.map fX gK fX gL (𝟙 X) ι (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) =
      Φ.inv ≫ pullback.fst (pullback.snd fX gL) ι := by
    rw [← hΦ, Iso.inv_hom_id_assoc]
  rw [this]
  infer_instance

theorem twist_comm
    (k K : Type) [Field k] [Field K] [Algebra k K] [Normal k K]
    (X Y : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated fY]
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
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hσ]))
    (L : IntermediateField k K)
    (hι : Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
        Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (g : pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶ pullback fY (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (hgL :
      g ≫ pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
        pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (hsq :
      f ≫ pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 Y) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) =
        pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 X) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) ≫ g) :
    ∀ (τ : L ≃ₐ[k] L)
        (hτ : Spec.map (CommRingCat.ofHom ((τ : L →ₐ[k] L) : L →+* L)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
          Spec.map (CommRingCat.ofHom (algebraMap k L))),
        pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) fX (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 X) (Spec.map (CommRingCat.ofHom ((τ : L →ₐ[k] L) : L →+* L))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hτ]) ≫ g =
          g ≫ pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) fY (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 Y) (Spec.map (CommRingCat.ofHom ((τ : L →ₐ[k] L) : L →+* L))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hτ]) := by
  intro τ hτ

  let σ : K ≃ₐ[k] K := AlgEquiv.liftNormal τ K
  have hσ := specMap_algEquiv_comp (k := k) σ
  have hσι : (Spec.map (CommRingCat.ofHom ((σ : K →ₐ[k] K) : K →+* K))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap L K))) = (Spec.map (CommRingCat.ofHom (algebraMap L K))) ≫ (Spec.map (CommRingCat.ofHom ((τ : L →ₐ[k] L) : L →+* L))) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact AlgEquiv.liftNormal_commutes τ K x

  have pX : fX ≫ 𝟙 _ = 𝟙 X ≫ fX := (Category.comp_id _).trans (Category.id_comp _).symm
  have pY : fY ≫ 𝟙 _ = 𝟙 Y ≫ fY := (Category.comp_id _).trans (Category.id_comp _).symm
  have pσ : (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫ 𝟙 _ = (Spec.map (CommRingCat.ofHom ((σ : K →ₐ[k] K) : K →+* K))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap k K))) := (Category.comp_id _).trans hσ.symm
  have pτ : (Spec.map (CommRingCat.ofHom (algebraMap k L))) ≫ 𝟙 _ = (Spec.map (CommRingCat.ofHom ((τ : L →ₐ[k] L) : L →+* L))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap k L))) := (Category.comp_id _).trans hτ.symm
  have pι : (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫ 𝟙 _ = (Spec.map (CommRingCat.ofHom (algebraMap L K))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap k L))) := (Category.comp_id _).trans hι.symm

  have hTX : pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) (𝟙 X) (Spec.map (CommRingCat.ofHom ((σ : K →ₐ[k] K) : K →+* K))) (𝟙 _) pX pσ ≫
      pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) (𝟙 X) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _) pX pι =
      pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) (𝟙 X) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _) pX pι ≫
      pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) (𝟙 X) (Spec.map (CommRingCat.ofHom ((τ : L →ₐ[k] L) : L →+* L))) (𝟙 _) pX pτ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, map_fst', Category.comp_id]
    · simp only [Category.assoc, map_snd', map_snd'_assoc, hσι]
  have hTY : pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) (𝟙 Y) (Spec.map (CommRingCat.ofHom ((σ : K →ₐ[k] K) : K →+* K))) (𝟙 _) pY pσ ≫
      pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) (𝟙 Y) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _) pY pι =
      pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) (𝟙 Y) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _) pY pι ≫
      pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) (𝟙 Y) (Spec.map (CommRingCat.ofHom ((τ : L →ₐ[k] L) : L →+* L))) (𝟙 _) pY pτ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, map_fst', Category.comp_id]
    · simp only [Category.assoc, map_snd', map_snd'_assoc, hσι]

  haveI := isSchemeTheoreticallyDominant_levelMap fX L hι
  haveI : (pullback fY (Spec.map (CommRingCat.ofHom (algebraMap k L)))).IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from (pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k L))))]
    infer_instance
  apply eq_of_comp_eq_of_isSchemeTheoreticallyDominant
    (pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) (𝟙 X) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _) pX pι)
  have e1 := congrArg (· ≫ g) hTX
  have e2 := congrArg (pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) (𝟙 X) (Spec.map (CommRingCat.ofHom ((σ : K →ₐ[k] K) : K →+* K))) (𝟙 _) pX pσ ≫ ·) hsq
  have e3 := congrArg (· ≫ pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) (𝟙 Y) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _) pY pι) (hgal σ hσ)
  have e4 := congrArg (f ≫ ·) hTY
  have e5 := congrArg (· ≫ pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) (𝟙 Y) (Spec.map (CommRingCat.ofHom ((τ : L →ₐ[k] L) : L →+* L))) (𝟙 _) pY pτ) hsq
  simp only [Category.assoc] at e1 e2 e3 e4 e5 ⊢

  rw [← e1, ← e2, e3, e4, e5]

end LiftTwistAux

open AlgebraicGeometry in

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
    ∃ (L : IntermediateField k K) (_ : FiniteDimensional k L) (_ : IsGalois k L)
      (g : pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶ pullback fY (Spec.map (CommRingCat.ofHom (algebraMap k L))))
      (hι : Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
        Spec.map (CommRingCat.ofHom (algebraMap k K))),
      g ≫ pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
        pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) ∧
      (∀ (τ : L ≃ₐ[k] L)
        (hτ : Spec.map (CommRingCat.ofHom ((τ : L →ₐ[k] L) : L →+* L)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
          Spec.map (CommRingCat.ofHom (algebraMap k L))),
        pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) fX (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 X) (Spec.map (CommRingCat.ofHom ((τ : L →ₐ[k] L) : L →+* L))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hτ]) ≫ g =
          g ≫ pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) fY (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 Y) (Spec.map (CommRingCat.ofHom ((τ : L →ₐ[k] L) : L →+* L))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hτ])) ∧
      f ≫ pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 Y) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) =
        pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 X) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) ≫ g := by
  classical

  obtain ⟨L₀, hL₀fin, g₀, hι₀, hg₀L, hsq₀⟩ :=
    AlgebraicGeometry.exists_intermediateField_finiteDimensional_comp_pullback_map_eq_of_isAlgebraic k K X Y fX fY f hf
  haveI := hL₀fin

  let L : IntermediateField k K := IntermediateField.normalClosure k L₀ K
  have hL₀L : L₀ ≤ L := IntermediateField.le_normalClosure L₀
  haveI : FiniteDimensional k L := normalClosure.is_finiteDimensional k L₀ K
  haveI : Normal k L := normalClosure.normal k L₀ K
  haveI : IsGalois k L := IsGalois.mk

  have hι : Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hιL₀L : Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hL₀L).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k L₀)) = Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have hιL₀LK : Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫
      Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hL₀L).toRingHom) =
        Spec.map (CommRingCat.ofHom (algebraMap L₀ K)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2

  let pX : pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶
      pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k L₀))) :=
    pullback.map _ _ _ _ (𝟙 X) (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hL₀L).toRingHom)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hιL₀L])
  let g : pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶
      pullback fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
    pullback.lift (pX ≫ g₀ ≫ pullback.fst _ _) (pullback.snd _ _) (by
      rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hg₀L]
      dsimp only [pX]
      rw [LiftTwistAux.map_snd'_assoc, hιL₀L])
  have hgL : g ≫ pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
      pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) := pullback.lift_snd _ _ _
  have hg_fst : g ≫ pullback.fst fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) = pX ≫ g₀ ≫ pullback.fst _ _ :=
    pullback.lift_fst _ _ _

  have hsq : f ≫ pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 Y) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) =
        pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 X) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) ≫ g := by

    have hpp : pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX (Spec.map (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 X) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) ≫ pX =
        pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX (Spec.map (CommRingCat.ofHom (algebraMap k L₀)))
            (𝟙 X) (Spec.map (CommRingCat.ofHom (algebraMap L₀ K))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι₀]) := by
      dsimp only [pX]
      apply pullback.hom_ext
      · rw [Category.assoc, LiftTwistAux.map_fst', LiftTwistAux.map_fst'_assoc, LiftTwistAux.map_fst', Category.comp_id]
      · rw [Category.assoc, LiftTwistAux.map_snd', LiftTwistAux.map_snd'_assoc, LiftTwistAux.map_snd', hιL₀LK]
    apply pullback.hom_ext
    · rw [Category.assoc, LiftTwistAux.map_fst', Category.comp_id, Category.assoc, hg_fst, reassoc_of% hpp]
      have := congrArg (· ≫ pullback.fst fY (Spec.map (CommRingCat.ofHom (algebraMap k L₀)))) hsq₀
      simp only [Category.assoc] at this
      rw [LiftTwistAux.map_fst', Category.comp_id] at this
      exact this
    · rw [Category.assoc, LiftTwistAux.map_snd', reassoc_of% hf, Category.assoc, hgL, LiftTwistAux.map_snd']

  exact ⟨L, inferInstance, inferInstance, g, hι, hgL,
    LiftTwistAux.twist_comm k K X Y fX fY f hf hgal L hι g hgL hsq, hsq⟩

end S_AlgebraicGeometry_exists_intermediateField_isGalois_galois_twist_comp_pullback_map_eq
end P2MW
export P2MW.S_AlgebraicGeometry_exists_intermediateField_isGalois_galois_twist_comp_pullback_map_eq (solution)
