-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_functionField_of_flat_morphismRestrict
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/9bfffb3f-29d5-561e-8710-bc2d6a4349a7

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_morphismRestrict_eq_finrank
import Theorems.Thm_AlgebraicCurve_germToFunctionField_app_eq_of_fromSpecStalk_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_finrank_eq_finrank_functionField_of_flat_morphismRestrict

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RankAux

theorem apply_genericPoint_eq_of_surjective {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
    (hf : Function.Surjective f) : f (genericPoint Y) = genericPoint X := by
  have h := (genericPoint_spec Y).image f.continuous
  rw [Set.image_univ, Set.range_eq_univ.mpr hf, closure_univ] at h
  exact h.eq (genericPoint_spec X)

theorem exists_ringHom_functionField_of_surjective {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) (hf : Function.Surjective f) :
    ∃ φ : X.functionField →+* Y.functionField,
      Y.fromSpecStalk (genericPoint Y) ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X) := by
  have hgen := apply_genericPoint_eq_of_surjective f hf
  have hsp : f (genericPoint Y) ⤳ genericPoint X := hgen ▸ specializes_rfl
  refine ⟨(X.presheaf.stalkSpecializes hsp ≫ f.stalkMap (genericPoint Y)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem exists_ringEquiv_functionField_of_isOpenImmersion {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsOpenImmersion f] :
    ∃ e : X.functionField ≃+* Y.functionField,
      Y.fromSpecStalk (genericPoint Y) ≫ f = Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecStalk (genericPoint X) := by
  have hgen : f (genericPoint Y) = genericPoint X := genericPoint_eq_of_isOpenImmersion f
  have hins : Inseparable (genericPoint X) (f (genericPoint Y)) := Inseparable.of_eq hgen.symm
  let θ : X.functionField ≅ Y.functionField := X.presheaf.stalkCongr hins ≪≫ asIso (f.stalkMap (genericPoint Y))
  refine ⟨θ.commRingCatIsoToRingEquiv, ?_⟩
  have hθ : CommRingCat.ofHom θ.commRingCatIsoToRingEquiv.toRingHom =
      X.presheaf.stalkSpecializes hins.ge ≫ f.stalkMap (genericPoint Y) := rfl
  rw [hθ, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem app_genericPoint_of_fromSpecStalk_comp_eq {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    (φ : X.functionField →+* Y.functionField)
    (hφπ : Y.fromSpecStalk (genericPoint Y) ≫ π = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X)) :
    π (genericPoint Y) = genericPoint X := by
  have h1 := congrArg (fun q => q (IsLocalRing.closedPoint (Y.presheaf.stalk (genericPoint Y)))) hφπ
  simp only [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint] at h1
  rw [h1]
  have h2 : (Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint (Y.presheaf.stalk (genericPoint Y))) =
      IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)) := Subsingleton.elim _ _
  rw [h2, Scheme.fromSpecStalk_closedPoint]

theorem ringHom_ext_of_fromSpecStalk_comp_eq {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    (g₁ g₂ : X.functionField →+* Y.functionField)
    (h₁ : Y.fromSpecStalk (genericPoint Y) ≫ π = Spec.map (CommRingCat.ofHom g₁) ≫ X.fromSpecStalk (genericPoint X))
    (h₂ : Y.fromSpecStalk (genericPoint Y) ≫ π = Spec.map (CommRingCat.ofHom g₂) ≫ X.fromSpecStalk (genericPoint X)) :
    g₁ = g₂ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  haveI : Nonempty (U : X.Opens) := ⟨⟨_, hηU⟩⟩
  have hgen := app_genericPoint_of_fromSpecStalk_comp_eq π g₁ h₁
  haveI : Nonempty (π ⁻¹ᵁ U : Y.Opens) := ⟨⟨genericPoint Y, show π (genericPoint Y) ∈ U by rw [hgen]; exact hηU⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  apply IsLocalization.ringHom_ext (nonZeroDivisors Γ(X, U))
  ext s
  change g₁ ((X.germToFunctionField U).hom s) = g₂ ((X.germToFunctionField U).hom s)
  rw [← AlgebraicCurve.germToFunctionField_app_eq_of_fromSpecStalk_comp_eq π g₁ h₁ U s,
    ← AlgebraicCurve.germToFunctionField_app_eq_of_fromSpecStalk_comp_eq π g₂ h₂ U s]

end RankAux

theorem solution
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : X ⟶ Y) [IsFinite π] (hsurj : Function.Surjective π)
    (φ : Y.functionField →+* X.functionField)
    (hφ : X.fromSpecStalk (genericPoint X) ≫ π = Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk (genericPoint Y))
    (V : Y.Opens) [Flat (π ∣_ V)] [LocallyOfFinitePresentation (π ∣_ V)] (y : Y) (hy : y ∈ V) :
    π.finrank y = (letI := φ.toAlgebra; Module.finrank Y.functionField X.functionField) := by
  classical

  haveI : Nonempty V := ⟨⟨y, hy⟩⟩
  obtain ⟨x, hx⟩ := hsurj y
  haveI : Nonempty (π ⁻¹ᵁ V) := ⟨⟨x, show π x ∈ V by rw [hx]; exact hy⟩⟩
  let V' : Scheme.{u} := V
  let X' : Scheme.{u} := ↑(π ⁻¹ᵁ V)
  let π' : X' ⟶ V' := π ∣_ V
  haveI : IsFinite π' := inferInstance
  haveI : IsIntegral V' := inferInstance
  haveI : IsIntegral X' := inferInstance

  rw [← AlgebraicGeometry.Scheme.Hom.finrank_morphismRestrict_eq_finrank π V y hy]

  let U : V'.Opens := (V'.affineCover.f (V'.affineCover.idx ⟨y, hy⟩)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hyU : (⟨y, hy⟩ : V') ∈ U := V'.affineCover.covers _
  haveI : Nonempty U := ⟨⟨_, hyU⟩⟩
  have hVU : IsAffineOpen (π' ⁻¹ᵁ U) := hU.preimage π'
  letI alg : Algebra Γ(V', U) Γ(X', π' ⁻¹ᵁ U) := (π'.appLE U (π' ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  haveI : Module.Finite Γ(V', U) Γ(X', π' ⁻¹ᵁ U) := by
    have h := IsFinite.finite_app π' U hU
    rw [Scheme.Hom.app_eq_appLE] at h
    exact h
  haveI : Module.Flat Γ(V', U) Γ(X', π' ⁻¹ᵁ U) :=
    HasRingHomProperty.appLE @Flat π' inferInstance ⟨U, hU⟩ ⟨π' ⁻¹ᵁ U, hVU⟩ le_rfl
  let 𝔭 : PrimeSpectrum Γ(V', U) := ⟨⊥, Ideal.isPrime_bot⟩
  have hconst : π'.finrank ⟨y, hy⟩ = π'.finrank (hU.fromSpec.base 𝔭) :=
    (Scheme.Hom.isLocallyConstant_finrank π').apply_eq_of_preconnectedSpace _ _
  rw [hconst]

  have sq : IsPullback (Spec.map (π'.appLE U (π' ⁻¹ᵁ U) le_rfl)) hVU.fromSpec hU.fromSpec π' :=
    IsOpenImmersion.isPullback _ _ _ _ (IsAffineOpen.SpecMap_appLE_fromSpec π' hU hVU le_rfl).symm
      (by rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec])
  have h1 : π'.finrank (hU.fromSpec.base 𝔭) = (Spec.map (π'.appLE U (π' ⁻¹ᵁ U) le_rfl)).finrank 𝔭 :=
    (Scheme.Hom.finrank_of_isPullback _ _ _ _ sq.flip 𝔭).symm
  have h2 : (Spec.map (π'.appLE U (π' ⁻¹ᵁ U) le_rfl)).finrank 𝔭 =
      Module.rankAtStalk (R := Γ(V', U)) Γ(X', π' ⁻¹ᵁ U) 𝔭 :=
    Scheme.Hom.finrank_SpecMap_algebraMap Γ(V', U) Γ(X', π' ⁻¹ᵁ U) 𝔭
  haveI : Algebra.IsPushout Γ(V', U) Γ(X', π' ⁻¹ᵁ U) V'.functionField (V'.functionField ⊗[Γ(V', U)] Γ(X', π' ⁻¹ᵁ U)) :=
    Algebra.IsPushout.symm inferInstance
  haveI hfrac := functionField_isFractionRing_of_isAffineOpen V' U hU
  have h3 : Module.rankAtStalk (R := V'.functionField) (V'.functionField ⊗[Γ(V', U)] Γ(X', π' ⁻¹ᵁ U)) ⟨⊥, Ideal.isPrime_bot⟩ =
      Module.rankAtStalk (R := Γ(V', U)) Γ(X', π' ⁻¹ᵁ U) 𝔭 := by
    rw [Algebra.rankAtStalk_eq_of_isPushout Γ(V', U) Γ(X', π' ⁻¹ᵁ U) V'.functionField
      (V'.functionField ⊗[Γ(V', U)] Γ(X', π' ⁻¹ᵁ U))]
    congr 1
    ext1
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective Γ(V', U) V'.functionField)
  rw [h1, h2, ← h3, Module.rankAtStalk_eq_finrank_of_free]

  have hsurj' : Function.Surjective π' := by
    intro v
    obtain ⟨x', hx'⟩ := hsurj v.1
    refine ⟨⟨x', show π x' ∈ V by rw [hx']; exact v.2⟩, Subtype.ext ?_⟩
    rw [morphismRestrict_base_coe]
    exact hx'
  obtain ⟨φ', hφ'⟩ := RankAux.exists_ringHom_functionField_of_surjective π' hsurj'
  haveI : Nonempty (π' ⁻¹ᵁ U) := by
    obtain ⟨x₀, hx₀⟩ := hsurj' ⟨y, hy⟩
    exact ⟨⟨x₀, show π' x₀ ∈ U by rw [hx₀]; exact hyU⟩⟩
  haveI hfracX := functionField_isFractionRing_of_isAffineOpen X' (π' ⁻¹ᵁ U) hVU
  let F := V'.functionField
  let KX := X'.functionField
  let ιA : Γ(V', U) →+* F := (V'.germToFunctionField U).hom
  let ιB : Γ(X', π' ⁻¹ᵁ U) →+* KX := (X'.germToFunctionField (π' ⁻¹ᵁ U)).hom
  have hιB : Function.Injective ιB := Scheme.germToFunctionField_injective X' (π' ⁻¹ᵁ U)
  have hιA : Function.Injective ιA := Scheme.germToFunctionField_injective V' U
  have hcompat : ∀ a : Γ(V', U), ιB (algebraMap Γ(V', U) Γ(X', π' ⁻¹ᵁ U) a) = φ' (ιA a) := by
    intro a
    show ιB ((π'.appLE U (π' ⁻¹ᵁ U) le_rfl).hom a) = _
    rw [← Scheme.Hom.app_eq_appLE]
    exact AlgebraicCurve.germToFunctionField_app_eq_of_fromSpecStalk_comp_eq π' φ' hφ' U a

  letI algF : Algebra F KX := φ'.toAlgebra
  letI algA : Algebra Γ(V', U) KX := ((algebraMap F KX).comp (algebraMap Γ(V', U) F)).toAlgebra
  haveI : IsScalarTower Γ(V', U) F KX := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halgA : ∀ a : Γ(V', U), algebraMap Γ(V', U) KX a = φ' (ιA a) := fun _ => rfl
  let fB : Γ(X', π' ⁻¹ᵁ U) →ₐ[Γ(V', U)] KX :=
    { ιB with commutes' := fun a => by rw [halgA]; exact hcompat a }
  have hfB : ∀ b, fB b = ιB b := fun _ => rfl
  let f : Γ(X', π' ⁻¹ᵁ U) →ₗ[Γ(V', U)] KX := fB.toLinearMap
  have hf : ∀ b, f b = ιB b := fun _ => rfl

  let C : Subalgebra F KX := Algebra.adjoin F (Set.range ιB)
  have hCint : C ≤ integralClosure F KX := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨b, rfl⟩
    haveI hint : Algebra.IsIntegral Γ(V', U) Γ(X', π' ⁻¹ᵁ U) := Algebra.IsIntegral.of_finite Γ(V', U) Γ(X', π' ⁻¹ᵁ U)
    have hb : _root_.IsIntegral Γ(V', U) (fB b) := (Algebra.IsIntegral.isIntegral (R := Γ(V', U)) b).map fB
    exact hb.tower_top
  haveI : Algebra.IsIntegral F C :=
    Algebra.IsIntegral.of_injective (Subalgebra.inclusion hCint) (Subalgebra.inclusion_injective hCint)
  have hC : IsField C := isField_of_isIntegral_of_isField' (Field.toIsField F)
  have hCtop : ∀ z : KX, z ∈ C := by
    intro z
    obtain ⟨b₁, t, ht, rfl⟩ := IsFractionRing.div_surjective (A := Γ(X', π' ⁻¹ᵁ U)) z
    have hb₁ : ιB b₁ ∈ C := Algebra.subset_adjoin ⟨b₁, rfl⟩
    have htC : ιB t ∈ C := Algebra.subset_adjoin ⟨t, rfl⟩
    have htne : (⟨ιB t, htC⟩ : C) ≠ 0 := by
      intro h
      have h' : ιB t = 0 := congrArg Subtype.val h
      exact nonZeroDivisors.ne_zero ht ((map_eq_zero_iff ιB hιB).mp h')
    obtain ⟨u, hu⟩ := hC.mul_inv_cancel htne
    have hinv : (ιB t)⁻¹ = (u : KX) := by
      have hu' : ιB t * (u : KX) = 1 := congrArg Subtype.val hu
      exact inv_eq_of_mul_eq_one_right hu'
    show algebraMap _ KX b₁ / algebraMap _ KX t ∈ C
    rw [div_eq_mul_inv]
    exact C.mul_mem hb₁ (hinv ▸ u.2)
  have hCform : ∀ z ∈ C, ∃ (b : Γ(X', π' ⁻¹ᵁ U)) (s : nonZeroDivisors Γ(V', U)), (s : Γ(V', U)) • z = ιB b := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨b, rfl⟩ := hx; exact ⟨b, 1, by rw [OneMemClass.coe_one, one_smul]⟩
    | algebraMap r =>
      obtain ⟨a₁, a₂, ha₂, rfl⟩ := IsFractionRing.div_surjective (A := Γ(V', U)) r
      refine ⟨algebraMap _ _ a₁, ⟨a₂, ha₂⟩, ?_⟩
      rw [hcompat, Algebra.smul_def, halgA]
      show φ' (ιA a₂) * φ' (ιA a₁ / ιA a₂) = φ' (ιA a₁)
      rw [← map_mul, mul_div_cancel₀ _ ((map_ne_zero_iff ιA hιA).mpr (nonZeroDivisors.ne_zero ha₂))]
    | add x y _ _ hx hy =>
      obtain ⟨b₁, s₁, h₁⟩ := hx
      obtain ⟨b₂, s₂, h₂⟩ := hy
      refine ⟨algebraMap _ _ (s₂ : Γ(V', U)) * b₁ + algebraMap _ _ (s₁ : Γ(V', U)) * b₂, s₁ * s₂, ?_⟩
      have h₁' : φ' (ιA s₁) * x = ιB b₁ := by rw [← h₁, Algebra.smul_def, halgA]
      have h₂' : φ' (ιA s₂) * y = ιB b₂ := by rw [← h₂, Algebra.smul_def, halgA]
      simp only [Algebra.smul_def, halgA, Submonoid.coe_mul, map_mul, map_add, hcompat]
      rw [← h₁', ← h₂']
      ring
    | mul x y _ _ hx hy =>
      obtain ⟨b₁, s₁, h₁⟩ := hx
      obtain ⟨b₂, s₂, h₂⟩ := hy
      refine ⟨b₁ * b₂, s₁ * s₂, ?_⟩
      have h₁' : φ' (ιA s₁) * x = ιB b₁ := by rw [← h₁, Algebra.smul_def, halgA]
      have h₂' : φ' (ιA s₂) * y = ιB b₂ := by rw [← h₂, Algebra.smul_def, halgA]
      simp only [Algebra.smul_def, halgA, Submonoid.coe_mul, map_mul]
      rw [← h₁', ← h₂']
      ring
  have hloc : IsLocalizedModule (nonZeroDivisors Γ(V', U)) f := by
    refine ⟨fun s => ?_, fun z => ?_, fun {b₁ b₂} h => ⟨1, by rw [hf, hf] at h; rw [hιB h]⟩⟩
    · rw [Module.End.isUnit_iff]
      have hne : algebraMap Γ(V', U) KX (s : Γ(V', U)) ≠ 0 := by
        rw [halgA, map_ne_zero_iff _ φ'.injective, map_ne_zero_iff _ hιA]
        exact nonZeroDivisors.ne_zero s.2
      have hsm : ∀ z : KX, (algebraMap Γ(V', U) (Module.End Γ(V', U) KX) (s : Γ(V', U))) z =
          algebraMap Γ(V', U) KX (s : Γ(V', U)) * z := fun z => by
        rw [Module.algebraMap_end_apply, Algebra.smul_def]
      constructor
      · intro z₁ z₂ h; rw [hsm, hsm] at h; exact mul_left_cancel₀ hne h
      · intro z; exact ⟨(algebraMap Γ(V', U) KX (s : Γ(V', U)))⁻¹ * z, by rw [hsm, mul_inv_cancel_left₀ hne]⟩
    · obtain ⟨b, s, h⟩ := hCform z (hCtop z)
      exact ⟨(b, s), by rw [hf]; exact h⟩
  have hbc : IsBaseChange F f := (isLocalizedModule_iff_isBaseChange (nonZeroDivisors Γ(V', U)) F f).mp hloc
  rw [LinearEquiv.finrank_eq hbc.equiv]

  obtain ⟨eV, heV⟩ := RankAux.exists_ringEquiv_functionField_of_isOpenImmersion V.ι
  obtain ⟨eX, heX⟩ := RankAux.exists_ringEquiv_functionField_of_isOpenImmersion (π ⁻¹ᵁ V).ι
  have hc : φ'.comp eV.toRingHom = eX.toRingHom.comp φ := by
    apply RankAux.ringHom_ext_of_fromSpecStalk_comp_eq ((π ⁻¹ᵁ V).ι ≫ π)
    · rw [← morphismRestrict_ι, ← Category.assoc, show X'.fromSpecStalk (genericPoint X') ≫ π ∣_ V = _ from hφ',
        Category.assoc, heV, ← Category.assoc, ← Spec.map_comp]
      rfl
    · rw [← Category.assoc, heX, Category.assoc, hφ, ← Category.assoc, ← Spec.map_comp]
      rfl
  letI := φ.toAlgebra
  show Module.finrank F KX = Module.finrank Y.functionField X.functionField
  exact (Algebra.finrank_eq_of_equiv_equiv eV eX hc).symm

end S_AlgebraicGeometry_Scheme_Hom_finrank_eq_finrank_functionField_of_flat_morphismRestrict
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_finrank_eq_finrank_functionField_of_flat_morphismRestrict (solution)
