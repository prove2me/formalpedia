-- Prove2me | solution 1 for AlgebraicGeometry.mem_smoothLocus_of_forall_mem_localRing_eq_algebraMap_mul_of_perfectField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/72dc55f7-9c41-51ed-b2e1-d1831c736a3f

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_mem_smoothLocus_of_forall_mem_localRing_eq_algebraMap_mul_of_perfectField

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_mem_smoothLocus_of_forall_mem_localRing_eq_algebraMap_mul_of_perfectField.AlgebraicGeometry IsLocalRing AlgebraicCurve TensorProduct"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Spec.map_apply Scheme.Hom Spec IsIntegral Spec.map Scheme.toSpecΓ_naturality Scheme Flat Spec.structureSheaf isAffineOpen_top Scheme.toSpecΓ_apply toSpecΓ_SpecMap_ΓSpecIso_inv IsAffineOpen LocallyOfFinitePresentation Scheme.Hom.germ_stalkMap toSpecΓ Scheme.Hom.comp_apply Scheme.Hom.appLE geometrically Scheme.ΓSpecIso"
namespace GenSmoothCritAux
p2m_open "AlgebraicGeometry"

section Algebra

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {S : Type*} [CommRing S] [IsLocalRing S] [Algebra R S]

def residueTensorEquiv [IsLocalHom (algebraMap R S)]
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    (ResidueField R) ⊗[R] S ≃ₐ[ResidueField R] ResidueField S := by

  let e₁ : (S ⧸ (maximalIdeal R).map (algebraMap R S)) ≃ₐ[R ⧸ maximalIdeal R]
      (R ⧸ maximalIdeal R) ⊗[R] S :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (maximalIdeal R)
  let e₂ : (S ⧸ (maximalIdeal R).map (algebraMap R S)) ≃ₐ[R] (S ⧸ maximalIdeal S) :=
    Ideal.quotientEquivAlgOfEq R h
  let e₃ : (ResidueField R) ⊗[R] S ≃ₐ[R] ResidueField S :=
    ((e₁.restrictScalars R).symm.trans e₂ : _)
  exact AlgEquiv.extendScalarsOfSurjective (R := R) (S := ResidueField R) residue_surjective e₃

theorem formallySmooth_of_map_maximalIdeal_eq [PerfectField (ResidueField R)]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    {P : Type*} [CommRing P] [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [Algebra.FinitePresentation R P] (M : Submonoid P) [IsLocalization M S]
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) : Algebra.FormallySmooth R S := by
  haveI : Algebra.EssFiniteType P S := Algebra.EssFiniteType.of_isLocalization S M
  haveI : Algebra.EssFiniteType R S := Algebra.EssFiniteType.comp R P S
  haveI : Algebra.EssFiniteType R (ResidueField S) :=
    inferInstanceAs (Algebra.EssFiniteType R (S ⧸ maximalIdeal S))
  haveI : Algebra.EssFiniteType (ResidueField R) (ResidueField S) :=
    Algebra.EssFiniteType.of_comp R (ResidueField R) (ResidueField S)
  haveI : Algebra.FormallySmooth (ResidueField R) (ResidueField S) := inferInstance
  haveI : Algebra.FormallySmooth (ResidueField R) ((ResidueField R) ⊗[R] S) :=
    Algebra.FormallySmooth.of_equiv (residueTensorEquiv h).symm
  exact Algebra.FormallySmooth.of_formallySmooth_residueField_tensor (R := R) (S := S) (P := P) M

end Algebra

universe u

theorem germ_appLE_eq {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ ⊤) (x : X) (hxV : x ∈ V) (c : Γ(Spec (CommRingCat.of A), ⊤)) :
    (X.presheaf.germ V x hxV).hom ((f.appLE ⊤ V hVU).hom c) =
      (X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom c) := by
  change (f.appLE ⊤ V hVU ≫ X.presheaf.germ V x hxV).hom c = (f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom c
  rw [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  rfl

theorem stalkMap_germ_eq {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (x : X) (c : Γ(Spec (CommRingCat.of A), ⊤)) :
    (f.stalkMap x).hom (((Spec (CommRingCat.of A)).presheaf.germ ⊤ (f.base x) trivial).hom c) =
      (X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom c) := by
  change ((Spec (CommRingCat.of A)).presheaf.germ ⊤ (f.base x) trivial ≫ f.stalkMap x).hom c =
    (f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom c
  rw [Scheme.Hom.germ_stalkMap]
  rfl

theorem base_eq_comap_closedPoint {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (x : X) :
    f.base x = PrimeSpectrum.comap
      ((X.presheaf.germ ⊤ x trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
      (closedPoint (X.presheaf.stalk x)) := by
  have hfac : f = X.toSpecΓ ≫ Spec.map f.appTop ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv := by
    have h := Scheme.toSpecΓ_naturality f
    have h' := congrArg (· ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv) h
    simpa only [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id] using h'
  conv_lhs => rw [hfac]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.toSpecΓ_apply, ← Scheme.Hom.comp_apply,
    ← Scheme.Hom.comp_apply, ← Spec.map_comp, ← Spec.map_comp, Spec.map_apply]
  rfl

end AlgebraicGeometry.GenSmoothCritAux

open AlgebraicGeometry.GenSmoothCritAux in
theorem solution
    {A₀ : Type} [CommRing A₀] [IsLocalRing A₀] [PerfectField (IsLocalRing.ResidueField A₀)]
    (ϖ₀ : A₀) (hϖ₀ : IsLocalRing.maximalIdeal A₀ = Ideal.span {ϖ₀})
    {X₀ : Scheme.{0}} (f : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [Flat f] [LocallyOfFinitePresentation f]
    {F₀ : Type} [Field F₀] [Algebra A₀ F₀]
    (φ₀ : F₀ ≃+* X₀.functionField)
    (hφ₀ : ∀ a : A₀, φ₀ (algebraMap A₀ F₀ a) = SemistableModel.baseToFunctionField f a)
    (η : X₀) (hη : f.base η = IsLocalRing.closedPoint A₀)
    (H : ∀ g ∈ SemistableModel.localRing X₀ φ₀ η, g⁻¹ ∉ SemistableModel.localRing X₀ φ₀ η →
      ∃ h ∈ SemistableModel.localRing X₀ φ₀ η, g = algebraMap A₀ F₀ ϖ₀ * h) :
    η ∈ f.smoothLocus := by
  classical
  let eΓ := Scheme.ΓSpecIso (CommRingCat.of A₀)

  let c : A₀ →+* ↑(X₀.presheaf.stalk η) := (X₀.presheaf.germ ⊤ η trivial).hom.comp (f.appTop.hom.comp eΓ.inv.hom)
  letI algAS : Algebra A₀ ↑(X₀.presheaf.stalk η) := c.toAlgebra
  have hc : ∀ a : A₀, algebraMap A₀ ↑(X₀.presheaf.stalk η) a =
      (X₀.presheaf.germ ⊤ η trivial).hom (f.appTop.hom (eΓ.inv.hom a)) := fun _ => rfl

  let ρ : ↑(X₀.presheaf.stalk η) →+* F₀ :=
    (φ₀.symm : X₀.functionField ≃+* F₀).toRingHom.comp (algebraMap ↑(X₀.presheaf.stalk η) X₀.functionField)
  have hρ_inj : Function.Injective ρ :=
    (φ₀.symm.injective).comp (IsFractionRing.injective ↑(X₀.presheaf.stalk η) X₀.functionField)
  have hρ_range : ∀ z, ρ z ∈ SemistableModel.localRing X₀ φ₀ η := fun z => ⟨z, rfl⟩
  have hρ_mem : ∀ g : F₀, g ∈ SemistableModel.localRing X₀ φ₀ η ↔ ∃ z, ρ z = g := fun g => Iff.rfl

  have hρc : ∀ a : A₀, ρ (c a) = algebraMap A₀ F₀ a := by
    intro a
    change φ₀.symm (algebraMap ↑(X₀.presheaf.stalk η) X₀.functionField
      ((X₀.presheaf.germ ⊤ η trivial).hom (f.appTop.hom (eΓ.inv.hom a)))) = _
    have h1 : algebraMap ↑(X₀.presheaf.stalk η) X₀.functionField
        ((X₀.presheaf.germ ⊤ η trivial).hom (f.appTop.hom (eΓ.inv.hom a))) =
        SemistableModel.baseToFunctionField f a := by
      change (X₀.presheaf.germ ⊤ η trivial ≫ X₀.presheaf.stalkSpecializes (genericPoint_specializes η)).hom
        (f.appTop.hom (eΓ.inv.hom a)) = _
      rw [TopCat.Presheaf.germ_stalkSpecializes]
      rfl
    rw [h1, ← hφ₀, RingEquiv.symm_apply_apply]

  have hcomap : ∀ a : A₀, c a ∈ maximalIdeal ↑(X₀.presheaf.stalk η) ↔ a ∈ maximalIdeal A₀ := by
    intro a
    have h := base_eq_comap_closedPoint f η
    rw [hη] at h
    have h' := congrArg (fun p : PrimeSpectrum A₀ => a ∈ p.asIdeal) h
    simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h'
    change (a ∈ (closedPoint A₀).asIdeal) = (c a ∈ (closedPoint ↑(X₀.presheaf.stalk η)).asIdeal) at h'
    rw [IsLocalRing.closedPoint, IsLocalRing.closedPoint] at h'
    exact (Iff.of_eq h').symm
  haveI hloc : IsLocalHom (algebraMap A₀ ↑(X₀.presheaf.stalk η)) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : a ∈ maximalIdeal A₀ := (IsLocalRing.mem_maximalIdeal a).mpr hna
    have h2 : c a ∈ maximalIdeal ↑(X₀.presheaf.stalk η) := (hcomap a).mpr h1
    exact (IsLocalRing.mem_maximalIdeal _).mp h2 ha

  have hϖS : c ϖ₀ ∈ maximalIdeal ↑(X₀.presheaf.stalk η) :=
    (hcomap ϖ₀).mpr (hϖ₀ ▸ Ideal.mem_span_singleton_self ϖ₀)
  have hmax : maximalIdeal ↑(X₀.presheaf.stalk η) = Ideal.span {c ϖ₀} := by
    refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).mpr hϖS)
    intro z hz
    by_cases hz0 : z = 0
    · rw [hz0]; exact Ideal.zero_mem _

    have hzL : ρ z ∈ SemistableModel.localRing X₀ φ₀ η := hρ_range z
    have hzinv : (ρ z)⁻¹ ∉ SemistableModel.localRing X₀ φ₀ η := by
      intro hin
      obtain ⟨w, hw⟩ := (hρ_mem _).mp hin
      have hρz : ρ z ≠ 0 := fun h0 => hz0 (hρ_inj (by rw [h0, map_zero]))
      have hzw : z * w = 1 := hρ_inj (by rw [map_mul, hw, map_one, mul_inv_cancel₀ hρz])
      exact (IsLocalRing.mem_maximalIdeal z).mp hz (IsUnit.of_mul_eq_one w hzw)
    obtain ⟨h, hhL, hzh⟩ := H (ρ z) hzL hzinv
    obtain ⟨w, rfl⟩ := (hρ_mem h).mp hhL
    have hz_eq : z = c ϖ₀ * w := hρ_inj (by rw [map_mul, hρc]; exact hzh)
    rw [hz_eq]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hmap : (maximalIdeal A₀).map (algebraMap A₀ ↑(X₀.presheaf.stalk η)) = maximalIdeal ↑(X₀.presheaf.stalk η) := by
    rw [hϖ₀, Ideal.map_span, Set.image_singleton, hmax]
    rfl

  obtain ⟨_, ⟨V, hV, rfl⟩, hηV, -⟩ :=
    X₀.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η) isOpen_univ
  have hVU : V ≤ f ⁻¹ᵁ ⊤ := le_top
  have htop : IsAffineOpen (⊤ : (Spec (CommRingCat.of A₀)).Opens) := isAffineOpen_top _
  have hfp : (f.appLE ⊤ V hVU).hom.FinitePresentation := f.finitePresentation_appLE htop hV hVU
  have hfl : (f.appLE ⊤ V hVU).hom.Flat := f.flat_appLE htop hV hVU
  let ψ : A₀ →+* Γ(X₀, V) := (f.appLE ⊤ V hVU).hom.comp eΓ.inv.hom
  letI algAV : Algebra A₀ Γ(X₀, V) := ψ.toAlgebra
  haveI hfpAV : Algebra.FinitePresentation A₀ Γ(X₀, V) :=
    RingHom.finitePresentation_respectsIso.2 (f.appLE ⊤ V hVU).hom eΓ.commRingCatIsoToRingEquiv.symm hfp
  haveI hflAV : Module.Flat A₀ Γ(X₀, V) :=
    RingHom.Flat.respectsIso.2 (f.appLE ⊤ V hVU).hom eΓ.commRingCatIsoToRingEquiv.symm hfl
  letI algVst : Algebra Γ(X₀, V) ↑(X₀.presheaf.stalk η) :=
    TopCat.Presheaf.algebra_section_stalk X₀.presheaf (⟨η, hηV⟩ : V)
  haveI hlocst : IsLocalization.AtPrime ↑(X₀.presheaf.stalk η) (hV.primeIdealOf ⟨η, hηV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨η, hηV⟩
  haveI hstA : IsScalarTower A₀ Γ(X₀, V) ↑(X₀.presheaf.stalk η) := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    change c a = (X₀.presheaf.germ V η hηV).hom (ψ a)
    exact (germ_appLE_eq f V hVU η hηV (eΓ.inv.hom a)).symm
  haveI : Module.Flat Γ(X₀, V) ↑(X₀.presheaf.stalk η) :=
    IsLocalization.flat ↑(X₀.presheaf.stalk η) (hV.primeIdealOf ⟨η, hηV⟩).asIdeal.primeCompl
  haveI : Module.Flat A₀ ↑(X₀.presheaf.stalk η) := Module.Flat.trans A₀ Γ(X₀, V) ↑(X₀.presheaf.stalk η)

  have hAS : Algebra.FormallySmooth A₀ ↑(X₀.presheaf.stalk η) :=
    formallySmooth_of_map_maximalIdeal_eq (R := A₀) (S := ↑(X₀.presheaf.stalk η)) (P := Γ(X₀, V))
      (hV.primeIdealOf ⟨η, hηV⟩).asIdeal.primeCompl hmap

  letI algARm : Algebra A₀ ↑((Spec (CommRingCat.of A₀)).presheaf.stalk (f.base η)) :=
    inferInstanceAs (Algebra A₀ ((Spec.structureSheaf A₀).presheaf.stalk (f.base η)))
  haveI hlocRm : IsLocalization.AtPrime ↑((Spec (CommRingCat.of A₀)).presheaf.stalk (f.base η)) (f.base η).asIdeal :=
    inferInstanceAs (IsLocalization.AtPrime ((Spec.structureSheaf A₀).presheaf.stalk (f.base η)) (f.base η).asIdeal)
  letI algRS : Algebra ↑((Spec (CommRingCat.of A₀)).presheaf.stalk (f.base η)) ↑(X₀.presheaf.stalk η) :=
    (f.stalkMap η).hom.toAlgebra
  haveI : IsScalarTower A₀ ↑((Spec (CommRingCat.of A₀)).presheaf.stalk (f.base η)) ↑(X₀.presheaf.stalk η) := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    change c a = (f.stalkMap η).hom (algebraMap A₀ ((Spec.structureSheaf A₀).presheaf.stalk (f.base η)) a)
    have heq : algebraMap A₀ ((Spec.structureSheaf A₀).presheaf.stalk (f.base η)) a =
        ((Spec (CommRingCat.of A₀)).presheaf.germ ⊤ (f.base η) trivial).hom (eΓ.inv.hom a) := rfl
    rw [heq, stalkMap_germ_eq]
    rfl
  have hsm : Algebra.FormallySmooth ↑((Spec (CommRingCat.of A₀)).presheaf.stalk (f.base η)) ↑(X₀.presheaf.stalk η) :=
    Algebra.FormallySmooth.localization_base
      (Rₘ := ↑((Spec (CommRingCat.of A₀)).presheaf.stalk (f.base η))) (Sₘ := ↑(X₀.presheaf.stalk η))
      (f.base η).asIdeal.primeCompl
  change (f.stalkMap η).hom.FormallySmooth
  exact RingHom.formallySmooth_algebraMap.mp hsm

end

end S_AlgebraicGeometry_mem_smoothLocus_of_forall_mem_localRing_eq_algebraMap_mul_of_perfectField
end P2MW
export P2MW.S_AlgebraicGeometry_mem_smoothLocus_of_forall_mem_localRing_eq_algebraMap_mul_of_perfectField (solution)
