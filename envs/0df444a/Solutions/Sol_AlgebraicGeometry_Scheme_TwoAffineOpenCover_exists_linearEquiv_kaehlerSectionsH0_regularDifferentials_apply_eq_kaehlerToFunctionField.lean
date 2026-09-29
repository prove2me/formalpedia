-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_kaehlerSectionsH0_regularDifferentials_apply_eq_kaehlerToFunctionField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/515fc6b7-80ea-5bf6-a48a-d6fbfbffa9fe

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_kaehlerToFunctionField_mem_regularDifferentials
import Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_kaehlerSectionsH0_regularDifferentials_apply_eq_kaehlerToFunctionField

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_kaehlerSectionsH0_regularDifferentials_apply_eq_kaehlerToFunctionField.AlgebraicCurve"
open scoped TensorProduct

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "germToFunctionField_comp_algebraMap kaehlerToFunctionField kaehlerToFunctionField_smul kaehlerToFunctionField_smul_D placesOf Place baseToFunctionField regularDifferentials mem_regularDifferentials_iff exists_place_range_stalk_eq"
namespace SurjAux
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_mem_and_dCoord_eq (v : Place K F) :
    ∃ π ∈ v.toValuationSubring, v.dCoord = KaehlerDifferential.D K F π :=
  ⟨((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F),
    ((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose).2, rfl⟩

end AlgebraicCurve.SurjAux

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "germToFunctionField_comp_algebraMap kaehlerToFunctionField kaehlerToFunctionField_smul kaehlerToFunctionField_smul_D placesOf Place baseToFunctionField regularDifferentials mem_regularDifferentials_iff exists_place_range_stalk_eq" end AlgebraicCurve
p2m_open_scoped "AlgebraicCurve" in
set_option maxHeartbeats 3200000 in

theorem AlgebraicCurve.exists_kaehlerToFunctionField_eq_of_forall_mem_placesOf_exists_eq_smul_dCoord
    {k : Type u} [Field k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [SmoothOfRelativeDimension 1 c]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (η : letI := (baseToFunctionField c).toAlgebra; Ω[X.functionField⁄k])
    (hη : letI := (baseToFunctionField c).toAlgebra
      ∀ v : Place k X.functionField, v ∈ placesOf c U → ∃ f ∈ v.toValuationSubring, η = f • v.dCoord) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := (baseToFunctionField c).toAlgebra
    ∃ ω : Ω[Γ(X, U)⁄k], kaehlerToFunctionField c U ω = η := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI : Algebra k X.functionField := (baseToFunctionField c).toAlgebra

  set φ : Γ(X, U) →+* X.functionField := (X.germToFunctionField U).hom with hφ

  let I : Ideal Γ(X, U) :=
    { carrier := {a | ∃ ω : Ω[Γ(X, U)⁄k], kaehlerToFunctionField c U ω = φ a • η}
      add_mem' := by
        rintro a b ⟨ω, hω⟩ ⟨ω', hω'⟩
        exact ⟨ω + ω', by rw [map_add, hω, hω', map_add, add_smul]⟩
      zero_mem' := ⟨0, by rw [map_zero, map_zero, zero_smul]⟩
      smul_mem' := by
        rintro r a ⟨ω, hω⟩
        refine ⟨r • ω, ?_⟩
        rw [kaehlerToFunctionField_smul, hω, smul_eq_mul, map_mul, mul_smul] }

  suffices h1 : (1 : Γ(X, U)) ∈ I by
    obtain ⟨ω, hω⟩ := h1
    exact ⟨ω, by rw [hω, map_one, one_smul]⟩
  by_contra h1
  have hItop : I ≠ ⊤ := fun h => h1 (h ▸ Submodule.mem_top)
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hItop

  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  haveI : LocallyOfFiniteType c := inferInstance
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace c
  let p : PrimeSpectrum Γ(X, U) := ⟨P, hP.isPrime⟩
  let x : X := hU.fromSpec.base p
  have hxU : x ∈ U := by
    have : x ∈ Set.range hU.fromSpec.base := ⟨p, rfl⟩
    rwa [hU.range_fromSpec] at this
  have hxcl : IsClosed ({x} : Set X) := by
    have hp : IsClosed ({p} : Set (PrimeSpectrum Γ(X, U))) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mpr hP
    have h := hU.fromSpec.isOpenEmbedding.preimage_closedPoints
    have hp' : p ∈ hU.fromSpec.base ⁻¹' closedPoints X := by rw [h]; exact hp
    exact hp'

  obtain ⟨v, hv⟩ := AlgebraicCurve.exists_place_range_stalk_eq c x hxcl
  have hvU : v ∈ placesOf c U := ⟨x, hxU, hxcl, hv⟩
  obtain ⟨f, hf, hηf⟩ := hη v hvU
  obtain ⟨π, hπ, hdπ⟩ := SurjAux.exists_mem_and_dCoord_eq v

  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
  haveI : IsLocalization.AtPrime (X.presheaf.stalk x) P := hU.isLocalization_stalk' p hxU
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk x) X.functionField :=
    AlgebraicGeometry.functionField_isScalarTower X U ⟨x, hxU⟩
  have key : ∀ g ∈ v.toValuationSubring, ∃ (a s : Γ(X, U)), s ∉ P ∧ g * φ s = φ a := by
    intro g hg
    have hg' : g ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by
      rw [hv]; exact hg
    obtain ⟨z, rfl⟩ := hg'
    obtain ⟨⟨a, s⟩, hz⟩ := IsLocalization.surj P.primeCompl z
    refine ⟨a, s, s.2, ?_⟩
    have h2 := congrArg (algebraMap (X.presheaf.stalk x) X.functionField) hz
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h2
    exact h2
  obtain ⟨a, s, hs, hfs⟩ := key f hf
  obtain ⟨b, t, ht, hπt⟩ := key π hπ

  have hmem : s * t ^ 2 ∈ I := by
    refine ⟨(a * t) • KaehlerDifferential.D k Γ(X, U) b - (a * b) • KaehlerDifferential.D k Γ(X, U) t, ?_⟩
    rw [map_sub, kaehlerToFunctionField_smul_D, kaehlerToFunctionField_smul_D, hηf, hdπ, ← hφ]
    simp only [map_mul, map_pow]
    rw [← hfs, ← hπt]
    simp only [Derivation.leibniz, smul_add, smul_smul]
    module

  have hstP : s * t ^ 2 ∈ P := hIP hmem
  rcases hP.isPrime.mem_or_mem hstP with h | h
  · exact hs h
  · exact ht (hP.isPrime.mem_of_pow_mem 2 h)

namespace RESINJ

theorem kaehlerDifferential_map_injective_of_isFractionRing_of_flat
    (R A K : Type*) [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]
    [CommRing K] [Algebra A K] [IsFractionRing A K] [Algebra R K] [IsScalarTower R A K]
    [Module.Flat A Ω[A⁄R]] :
    Function.Injective (KaehlerDifferential.map R R A K) := by
  haveI : Algebra.FormallyEtale A K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  have hbc : IsBaseChange K (KaehlerDifferential.map R R A K) :=
    KaehlerDifferential.isBaseChange_of_formallyEtale R A K

  have hfac : ∀ m : Ω[A⁄R], KaehlerDifferential.map R R A K m = hbc.equiv ((1 : K) ⊗ₜ[A] m) := by
    intro m; rw [IsBaseChange.equiv_tmul, one_smul]

  have hinj1 : Function.Injective (fun m : Ω[A⁄R] => (1 : K) ⊗ₜ[A] m) := by
    have h := Module.Flat.rTensor_preserves_injective_linearMap (M := Ω[A⁄R]) (Algebra.linearMap A K)
      (IsFractionRing.injective A K)
    intro m m' hmm'
    have : (Algebra.linearMap A K).rTensor Ω[A⁄R] ((1 : A) ⊗ₜ[A] m) =
        (Algebra.linearMap A K).rTensor Ω[A⁄R] ((1 : A) ⊗ₜ[A] m') := by
      simpa [LinearMap.rTensor_tmul] using hmm'
    have h2 := h this
    simpa using (TensorProduct.lid A Ω[A⁄R]).congr_arg h2
  intro m m' hmm'
  rw [hfac, hfac] at hmm'
  exact hinj1 (hbc.equiv.injective hmm')

end RESINJ

namespace L4

theorem formallySmooth_algebraOfHom {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))
    [Smooth c] (U : X.Opens) (hU : IsAffineOpen U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Algebra.FormallySmooth R Γ(X, U) := by
  have h1 : (c.appLE ⊤ U le_top).hom.FormallySmooth :=
    (AlgebraicGeometry.Smooth.smooth_appLE (f := c)
      (AlgebraicGeometry.isAffineOpen_top (Spec (.of R))) hU le_top).formallySmooth
  have h2 : ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U le_top).hom.FormallySmooth := by
    rw [CommRingCat.hom_comp]
    exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).mpr h1
  exact h2.toAlgebra

theorem kaehlerToFunctionField_injective {k : Type u} [Field k] {X : Scheme.{u}} (c : X ⟶ Spec (.of k))
    [IsIntegral X] [SmoothOfRelativeDimension 1 c] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    Function.Injective (kaehlerToFunctionField c U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
  haveI : IsFractionRing Γ(X, U) X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  haveI : @IsScalarTower k Γ(X, U) X.functionField Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (RingHom.congr_fun (germToFunctionField_comp_algebraMap c U) r).symm
  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  haveI : Algebra.FormallySmooth k Γ(X, U) := formallySmooth_algebraOfHom c U hU
  have e : ∀ z, kaehlerToFunctionField c U z = KaehlerDifferential.map k k Γ(X, U) X.functionField z := fun z =>
    KaehlerDifferential.mapOfRingHom_apply_eq_map (RingHom.id k) (X.germToFunctionField U).hom
      (germToFunctionField_comp_algebraMap c U) rfl z
  intro x y hxy
  rw [e, e] at hxy
  exact RESINJ.kaehlerDifferential_map_injective_of_isFractionRing_of_flat k Γ(X, U) X.functionField hxy

end L4

theorem solution
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [IsProper c] [SmoothOfRelativeDimension 1 c] [Nonempty 𝒱.U0] [Nonempty 𝒱.U1] :
    letI := (baseToFunctionField c).toAlgebra
    ∃ eΩ : ↥((𝒱.kaehlerSections c).H0) ≃ₗ[k] ↥(regularDifferentials k X.functionField),
      ∀ ω : ↥((𝒱.kaehlerSections c).H0),
        (eΩ ω : Ω[X.functionField⁄k]) = kaehlerToFunctionField c 𝒱.U0 ω.val.1 := by
  letI : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝒱.U0
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝒱.U1
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c (𝒱.U0 ⊓ 𝒱.U1)

  haveI : Nonempty (𝒱.U0 ⊓ 𝒱.U1 : X.Opens) := by
    obtain ⟨x₀⟩ := (inferInstance : Nonempty 𝒱.U0)
    obtain ⟨x₁⟩ := (inferInstance : Nonempty 𝒱.U1)
    have h : ((𝒱.U0 : Set X) ∩ (𝒱.U1 : Set X)).Nonempty :=
      nonempty_preirreducible_inter 𝒱.U0.isOpen 𝒱.U1.isOpen ⟨x₀.1, x₀.2⟩ ⟨x₁.1, x₁.2⟩
    obtain ⟨x, hx⟩ := h
    exact ⟨⟨x, hx⟩⟩

  have hmem : ∀ ω : (𝒱.kaehlerSections c).H0,
      kaehlerToFunctionField c 𝒱.U0 ω.val.1 ∈ regularDifferentials k X.functionField :=
    fun ω => Scheme.TwoAffineOpenCover.kaehlerToFunctionField_mem_regularDifferentials 𝒱 c ω
  let Ψ₀ : (𝒱.kaehlerSections c).H0 →ₗ[k] Ω[X.functionField⁄k] :=
    (kaehlerToFunctionField c 𝒱.U0) ∘ₗ (LinearMap.fst k _ _) ∘ₗ (𝒱.kaehlerSections c).H0.subtype
  have hΨ₀ : ∀ ω, Ψ₀ ω = kaehlerToFunctionField c 𝒱.U0 ω.val.1 := fun ω => rfl
  let Ψ : (𝒱.kaehlerSections c).H0 →ₗ[k] regularDifferentials k X.functionField :=
    LinearMap.codRestrict (regularDifferentials k X.functionField) Ψ₀ (fun ω => (hΨ₀ ω).symm ▸ hmem ω)
  have hΨ : ∀ ω, (Ψ ω : Ω[X.functionField⁄k]) = kaehlerToFunctionField c 𝒱.U0 ω.val.1 := fun ω => rfl

  have hinj : Function.Injective Ψ := by
    intro ω ω' h
    have h0 : kaehlerToFunctionField c 𝒱.U0 ω.val.1 = kaehlerToFunctionField c 𝒱.U0 ω'.val.1 := by
      rw [← hΨ, ← hΨ, h]
    have e0 : ω.val.1 = ω'.val.1 := L4.kaehlerToFunctionField_injective c 𝒱.U0 𝒱.isAffineOpen_U0 h0
    have h1 : kaehlerToFunctionField c 𝒱.U1 ω.val.2 = kaehlerToFunctionField c 𝒱.U1 ω'.val.2 := by
      rw [← Scheme.TwoAffineOpenCover.kaehlerToFunctionField_fst_eq_snd_of_mem_H0,
        ← Scheme.TwoAffineOpenCover.kaehlerToFunctionField_fst_eq_snd_of_mem_H0, h0]
    have e1 : ω.val.2 = ω'.val.2 := L4.kaehlerToFunctionField_injective c 𝒱.U1 𝒱.isAffineOpen_U1 h1
    exact Subtype.ext (Prod.ext e0 e1)

  have hsurj : Function.Surjective Ψ := by
    intro η
    have hη := mem_regularDifferentials_iff.mp η.2
    obtain ⟨ω₀, h₀⟩ := exists_kaehlerToFunctionField_eq_of_forall_mem_placesOf_exists_eq_smul_dCoord c 𝒱.U0
      𝒱.isAffineOpen_U0 (η : Ω[X.functionField⁄k]) (fun v _ => hη v)
    obtain ⟨ω₁, h₁⟩ := exists_kaehlerToFunctionField_eq_of_forall_mem_placesOf_exists_eq_smul_dCoord c 𝒱.U1
      𝒱.isAffineOpen_U1 (η : Ω[X.functionField⁄k]) (fun v _ => hη v)
    have hcoc : (ω₀, ω₁) ∈ (𝒱.kaehlerSections c).H0 := by
      refine (TwoChartCech.Sections.mem_H0_iff _ _).mpr ?_
      apply L4.kaehlerToFunctionField_injective c (𝒱.U0 ⊓ 𝒱.U1) 𝒱.isAffineOpen_inf
      show kaehlerToFunctionField c (𝒱.U0 ⊓ 𝒱.U1) ((𝒱.kaehlerSections c).r0 ω₀) =
        kaehlerToFunctionField c (𝒱.U0 ⊓ 𝒱.U1) ((𝒱.kaehlerSections c).r1 ω₁)
      rw [Scheme.TwoAffineOpenCover.kaehlerToFunctionField_r0, Scheme.TwoAffineOpenCover.kaehlerToFunctionField_r1,
        h₀, h₁]
    exact ⟨⟨(ω₀, ω₁), hcoc⟩, Subtype.ext h₀⟩
  exact ⟨LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩, fun ω => hΨ ω⟩

end
end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_kaehlerSectionsH0_regularDifferentials_apply_eq_kaehlerToFunctionField
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_kaehlerSectionsH0_regularDifferentials_apply_eq_kaehlerToFunctionField (solution)
