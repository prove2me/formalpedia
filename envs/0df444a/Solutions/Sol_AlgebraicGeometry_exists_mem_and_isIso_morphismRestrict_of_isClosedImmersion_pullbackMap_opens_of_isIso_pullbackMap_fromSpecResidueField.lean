-- Prove2me | solution 1 for AlgebraicGeometry.exists_mem_and_isIso_morphismRestrict_of_isClosedImmersion_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/ec592cc2-3d58-57f5-90cd-22f7feaf0257

import Mathlib
import Theorems.Thm_Ideal_exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective
import Theorems.Thm_AlgebraicGeometry_bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_mem_and_isIso_morphismRestrict_of_isClosedImmersion_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TensorProduct

namespace K63A2b

theorem isPullback_fst_map_fst {X Y Z W : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X)
    (w : h ≫ q = p) (g : W ⟶ Y) :
    IsPullback (pullback.fst p g)
      (pullback.map p g q g h (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]))
      h (pullback.fst q g) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd q g) (v₂₂ := q) (h₃₁ := g) ?_ ?_
    (IsPullback.of_hasPullback q g)
  · have e1 : pullback.map p g q g h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]) ≫ pullback.snd q g =
        pullback.snd p g := by rw [pullback.lift_snd, Category.comp_id]
    rw [e1, w]
    exact IsPullback.of_hasPullback p g
  · rw [pullback.lift_fst]

theorem isClosedImmersion_morphismRestrict {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X)
    (w : h ≫ q = p) (V₁ : Y.Opens)
    (hci : IsClosedImmersion (pullback.map p V₁.ι q V₁.ι h (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])))
    (D : X.Opens) (hD : D ≤ q ⁻¹ᵁ V₁) : IsClosedImmersion (h ∣_ D) := by
  set hV := pullback.map p V₁.ι q V₁.ι h (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]) with hhV

  have hsub : Set.range (D.ι ≫ q).base ⊆ Set.range V₁.ι.base := by
    rintro _ ⟨d, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hD d.2
  let dV : (D : Scheme.{0}) ⟶ V₁ := IsOpenImmersion.lift V₁.ι (D.ι ≫ q) hsub
  have hdV : dV ≫ V₁.ι = D.ι ≫ q := IsOpenImmersion.lift_fac _ _ _
  let u : (D : Scheme.{0}) ⟶ pullback q V₁.ι := pullback.lift D.ι dV hdV.symm

  let f' : (h ⁻¹ᵁ D : Scheme.{0}) ⟶ pullback p V₁.ι :=
    pullback.lift (h ⁻¹ᵁ D).ι ((h ∣_ D) ≫ dV)
      (by rw [Category.assoc, hdV, ← Category.assoc, morphismRestrict_ι, Category.assoc, w])
  have sq : IsPullback f' (h ∣_ D) hV u := by
    refine IsPullback.of_right (h₁₂ := pullback.fst p V₁.ι) (v₁₃ := h) (h₂₂ := pullback.fst q V₁.ι) ?_ ?_
      (by rw [hhV]; exact isPullback_fst_map_fst p q h w V₁.ι)
    · have e1 : f' ≫ pullback.fst p V₁.ι = (h ⁻¹ᵁ D).ι := pullback.lift_fst _ _ _
      have e2 : u ≫ pullback.fst q V₁.ι = D.ι := pullback.lift_fst _ _ _
      rw [e1, e2]
      exact (isPullback_morphismRestrict h D).flip
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hhV, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
          pullback.lift_fst, morphismRestrict_ι]
      · rw [Category.assoc, Category.assoc, hhV, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
          pullback.lift_snd, Category.comp_id]
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq hci

end K63A2b

theorem solution
    {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
    [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [IsProper q] [Flat q] [LocallyOfFinitePresentation q]
    (y : Y) (hy : IsIso (pullback.map p (Y.fromSpecResidueField y) q (Y.fromSpecResidueField y) h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])))
    (V₁ : Y.Opens) (hyV₁ : y ∈ V₁)
    (hci : IsClosedImmersion (pullback.map p V₁.ι q V₁.ι h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])))
    (x : X) (hx : q.base x = y) :
    ∃ D : X.Opens, x ∈ D ∧ IsIso (h ∣_ D) := by
  classical
  subst hx

  obtain ⟨W, hWaff, hyW, hWV₁⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) hyV₁
  obtain ⟨U, hUaff, hxU, hUW⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ q ⁻¹ᵁ W from hyW)
  have hUV₁ : U ≤ q ⁻¹ᵁ V₁ := hUW.trans (Scheme.Hom.preimage_mono q hWV₁)

  have hciD : ∀ D : X.Opens, D ≤ q ⁻¹ᵁ V₁ → IsClosedImmersion (h ∣_ D) :=
    K63A2b.isClosedImmersion_morphismRestrict p q h w V₁ hci
  haveI : IsClosedImmersion (h ∣_ U) := hciD U hUV₁
  haveI : IsAffine (U : Scheme.{0}) := hUaff
  have hhU : IsAffineOpen (h ⁻¹ᵁ U) := isAffine_of_isAffineHom (h ∣_ U)

  letI algA : Algebra Γ(Y, W) Γ(X, U) := (q.appLE W U hUW).hom.toAlgebra
  letI algB : Algebra Γ(Y, W) Γ(Z, h ⁻¹ᵁ U) := (q.appLE W U hUW ≫ h.appLE U (h ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  letI algK : Algebra Γ(Y, W) (Y.residueField (q.base x)) := (Y.evaluation W (q.base x) hyW).hom.toAlgebra
  let φ : Γ(X, U) →ₐ[Γ(Y, W)] Γ(Z, h ⁻¹ᵁ U) := AlgHom.mk (h.appLE U (h ⁻¹ᵁ U) le_rfl).hom (fun _ => rfl)

  have hφsurj : Function.Surjective φ := by
    haveI : IsAffine (U : Scheme.{0}) := hUaff
    have h0 : Function.Surjective ((h ∣_ U).app ⊤).hom :=
      Scheme.Hom.app_surjective (h ∣_ U) ⊤ (isAffineOpen_top _)
    rw [morphismRestrict_app'] at h0
    have h1 := (Scheme.Hom.appLE_congr h _ (Scheme.Opens.ι_image_top U)
      (by rw [Scheme.Hom.preimage_top, Scheme.Opens.ι_image_top])
      (fun g => Function.Surjective g.hom)).mp h0
    exact h1

  have hbij := AlgebraicGeometry.bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField
    p q h w (q.base x) hy W hWaff hyW U hUaff hUW hhU

  haveI : LocallyOfFinitePresentation (h ≫ q) := by rw [w]; infer_instance
  haveI : Flat (h ≫ q) := by rw [w]; infer_instance
  have hUW' : h ⁻¹ᵁ U ≤ (h ≫ q) ⁻¹ᵁ W := by
    rw [Scheme.Hom.comp_preimage]; exact Scheme.Hom.preimage_mono h hUW
  have hcomp : q.appLE W U hUW ≫ h.appLE U (h ⁻¹ᵁ U) le_rfl = (h ≫ q).appLE W (h ⁻¹ᵁ U) hUW' :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  haveI : Algebra.FinitePresentation Γ(Y, W) Γ(X, U) :=
    HasRingHomProperty.appLE @LocallyOfFinitePresentation q inferInstance ⟨W, hWaff⟩ ⟨U, hUaff⟩ hUW
  haveI : Algebra.FinitePresentation Γ(Y, W) Γ(Z, h ⁻¹ᵁ U) := by
    have := HasRingHomProperty.appLE @LocallyOfFinitePresentation (h ≫ q) inferInstance ⟨W, hWaff⟩ ⟨h ⁻¹ᵁ U, hhU⟩ hUW'
    rw [← hcomp] at this
    exact this
  haveI : Module.Flat Γ(Y, W) Γ(Z, h ⁻¹ᵁ U) := by
    have := HasRingHomProperty.appLE @Flat (h ≫ q) inferInstance ⟨W, hWaff⟩ ⟨h ⁻¹ᵁ U, hhU⟩ hUW'
    rw [← hcomp] at this
    exact this
  let J : Ideal Γ(X, U) := RingHom.ker φ.toRingHom
  have hJ : J.FG := Algebra.FinitePresentation.ker_fG_of_surjective φ hφsurj
  let e : (Γ(X, U) ⧸ J) ≃ₐ[Γ(Y, W)] Γ(Z, h ⁻¹ᵁ U) := Ideal.quotientKerAlgEquivOfSurjective hφsurj
  haveI : Module.Flat Γ(Y, W) (Γ(X, U) ⧸ J) := Module.Flat.of_linearEquiv e.toLinearEquiv

  let 𝔭 : Ideal Γ(X, U) := RingHom.ker (X.evaluation U x hxU).hom
  haveI : 𝔭.IsPrime := RingHom.ker_isPrime _
  have hK : RingHom.ker (algebraMap Γ(Y, W) (Y.residueField (q.base x))) = 𝔭.comap (algebraMap Γ(Y, W) Γ(X, U)) := by
    ext r
    simp only [RingHom.mem_ker, Ideal.mem_comap]
    show (Y.evaluation W (q.base x) hyW).hom r = 0 ↔
      (X.evaluation U x hxU).hom ((q.appLE W U hUW).hom r) = 0
    have hev : (X.evaluation U x hxU).hom ((q.appLE W U hUW).hom r) =
        (q.residueFieldMap x).hom ((Y.evaluation W (q.base x) hyW).hom r) := by
      rw [Scheme.evaluation_naturality_apply]
      simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
      show (X.presheaf.map (homOfLE hUW).op ≫ X.evaluation U x hxU).hom ((q.app W).hom r) = _
      congr 2
      rw [← Scheme.germ_residue, ← Scheme.germ_residue, ← Category.assoc, TopCat.Presheaf.germ_res]
    rw [hev, map_eq_zero_iff _ (q.residueFieldMap x).hom.injective]
  have hinj : Function.Injective ((Ideal.Quotient.mkₐ Γ(Y, W) J).toLinearMap.rTensor (Y.residueField (q.base x))) := by
    have hfac : φ.toLinearMap = e.toAlgHom.toLinearMap ∘ₗ (Ideal.Quotient.mkₐ Γ(Y, W) J).toLinearMap := by
      ext a
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, e]
      rfl
    have h1 := hbij.1
    rw [hfac, LinearMap.rTensor_comp, LinearMap.coe_comp] at h1
    exact h1.of_comp
  obtain ⟨s, hs𝔭, hsJ⟩ :=
    Ideal.exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective J hJ 𝔭 hK hinj

  refine ⟨X.basicOpen s, ?_, ?_⟩
  · exact (X.evaluation_ne_zero_iff_mem_basicOpen x hxU s).mp hs𝔭
  · haveI : IsClosedImmersion (h ∣_ X.basicOpen s) := hciD _ ((X.basicOpen_le s).trans hUV₁)
    haveI : IsAffine (X.basicOpen s : Scheme.{0}) := hUaff.basicOpen s
    apply IsClosedImmersion.isIso_of_injective_of_isAffine

    set t : Γ(Z, h ⁻¹ᵁ U) := (h.appLE U (h ⁻¹ᵁ U) le_rfl).hom s with ht
    have hpre : h ⁻¹ᵁ X.basicOpen s = Z.basicOpen t := by
      rw [ht, Scheme.preimage_basicOpen, Scheme.Hom.app_eq_appLE]
    have hle : Z.basicOpen t ≤ h ⁻¹ᵁ X.basicOpen s := hpre.ge
    suffices hψ : Function.Injective (h.appLE (X.basicOpen s) (Z.basicOpen t) hle).hom by
      show Function.Injective ((h ∣_ X.basicOpen s).app ⊤).hom
      rw [morphismRestrict_app']
      exact (Scheme.Hom.appLE_congr h hle (Scheme.Opens.ι_image_top _).symm
        (by rw [Scheme.Hom.preimage_top, Scheme.Opens.ι_image_top, hpre])
        (fun g => Function.Injective g.hom)).mp hψ

    haveI hlocA : IsLocalization.Away s Γ(X, X.basicOpen s) := hUaff.isLocalization_basicOpen s
    haveI hlocB : IsLocalization.Away t Γ(Z, Z.basicOpen t) := hhU.isLocalization_basicOpen t
    set ψ := (h.appLE (X.basicOpen s) (Z.basicOpen t) hle).hom with hψdef
    have hnat : ∀ a : Γ(X, U), ψ (algebraMap Γ(X, U) Γ(X, X.basicOpen s) a) =
        algebraMap Γ(Z, h ⁻¹ᵁ U) Γ(Z, Z.basicOpen t) (φ a) := by
      intro a
      show (X.presheaf.map (homOfLE (X.basicOpen_le s)).op ≫ h.appLE (X.basicOpen s) (Z.basicOpen t) hle).hom a =
        (h.appLE U (h ⁻¹ᵁ U) le_rfl ≫ Z.presheaf.map (homOfLE (Z.basicOpen_le t)).op).hom a
      rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro z hz
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) z
    rw [IsLocalization.mk'_eq_zero_iff]

    have h1 : algebraMap Γ(Z, h ⁻¹ᵁ U) Γ(Z, Z.basicOpen t) (φ a) = 0 := by
      rw [← hnat]
      have h2 := IsLocalization.mk'_spec Γ(X, X.basicOpen s) a (⟨s ^ n, n, rfl⟩ : Submonoid.powers s)
      rw [← h2, map_mul, hz, zero_mul]
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers t) Γ(Z, Z.basicOpen t) (φ a)).mp h1

    have h3 : φ (s ^ m * a) = 0 := by
      rw [map_mul, map_pow]
      exact hm
    have h4 : s ^ m * a ∈ J := by
      rw [RingHom.mem_ker]
      exact h3
    refine ⟨⟨s ^ (m + 1), m + 1, rfl⟩, ?_⟩
    show s ^ (m + 1) * a = 0
    rw [pow_succ', mul_assoc]
    exact hsJ _ h4

end S_AlgebraicGeometry_exists_mem_and_isIso_morphismRestrict_of_isClosedImmersion_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField
end P2MW
export P2MW.S_AlgebraicGeometry_exists_mem_and_isIso_morphismRestrict_of_isClosedImmersion_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField (solution)
