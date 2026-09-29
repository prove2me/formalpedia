-- Prove2me | solution 1 for AlgebraicCurve.exists_kaehlerToFunctionField_eq_smul_dCoord_of_mem_placesOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d9d1787d-979a-52dd-95dd-96a418d162f3

import Mathlib
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_kaehlerToFunctionField_eq_smul_dCoord_of_mem_placesOf

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicCurve_exists_kaehlerToFunctionField_eq_smul_dCoord_of_mem_placesOf.AlgebraicCurve"
p2m_open "KaehlerDifferential P2MW.S_AlgebraicCurve_exists_kaehlerToFunctionField_eq_smul_dCoord_of_mem_placesOf.KaehlerDifferential TopologicalSpace"

section AlgebraCore
open TensorProduct

namespace KaehlerDifferential p2m_export "KaehlerDifferential" "finite exact_kerCotangentToTensor_mapBaseChange kerCotangentToTensor ideal D span_range_derivation map_D kerCotangentToTensor_toCotangent map" end KaehlerDifferential
p2m_open_scoped "KaehlerDifferential" in

theorem KaehlerDifferential.span_singleton_D_eq_top_of_maximalIdeal_eq_span
    {k S : Type*} [Field k] [CommRing S] [Algebra k S] [IsLocalRing S]
    [Module.Finite S Ω[S⁄k]] [Algebra.FormallyUnramified k (IsLocalRing.ResidueField S)]
    {π : S} (hπ : IsLocalRing.maximalIdeal S = Ideal.span {π}) :
    Submodule.span S {D k S π} = ⊤ := by
  set κ := IsLocalRing.ResidueField S
  have hsurj : Function.Surjective (algebraMap S κ) := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (algebraMap S κ) = IsLocalRing.maximalIdeal S := Ideal.mk_ker
  rw [← IsLocalRing.map_tensorProduct_mk_eq_top, eq_top_iff]
  rintro z -
  have hex := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k S κ hsurj
  have hz : z ∈ Set.range (kerCotangentToTensor k S κ) :=
    (hex z).mp (Subsingleton.elim _ _)
  obtain ⟨c, rfl⟩ := hz
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ c
  rw [kerCotangentToTensor_toCotangent]
  have hx' : x ∈ Ideal.span {π} := by rw [← hπ, ← hker]; exact hx
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hx'
  have hπ0 : algebraMap S κ π = 0 := by
    rw [← RingHom.mem_ker, hker, hπ]; exact Ideal.mem_span_singleton_self π

  have h1 : (1 : κ) ⊗ₜ[S] D k S (s * π) = s • ((1 : κ) ⊗ₜ[S] D k S π) := by
    rw [Derivation.leibniz, tmul_add, ← smul_tmul, ← smul_tmul, smul_tmul' , Algebra.smul_def π (1 : κ), mul_one,
      hπ0, zero_tmul, add_zero]
  change (1 : κ) ⊗ₜ[S] D k S (s * π) ∈ _
  rw [h1]
  exact Submodule.smul_mem _ s (Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _))

p2m_open_scoped "KaehlerDifferential" in

theorem KaehlerDifferential.exists_map_eq_smul_D_of_span_singleton_eq_top
    {k S F : Type*} [Field k] [CommRing S] [CommRing F] [Algebra k S] [Algebra k F] [Algebra S F]
    [IsScalarTower k S F] {π : S} (hπ : Submodule.span S {D k S π} = ⊤) (ω : Ω[S⁄k]) :
    ∃ s : S, KaehlerDifferential.map k k S F ω = algebraMap S F s • D k F (algebraMap S F π) := by
  have hω : ω ∈ Submodule.span S {D k S π} := hπ ▸ Submodule.mem_top
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hω
  refine ⟨s, ?_⟩
  rw [LinearMap.map_smul, KaehlerDifferential.map_D, algebraMap_smul]

namespace IsLocalRing p2m_export "IsLocalRing" "ResidueField of_surjective maximalIdeal mem_maximalIdeal map_tensorProduct_mk_eq_top residue" end IsLocalRing
p2m_open_scoped "IsLocalRing" in

theorem IsLocalRing.maximalIdeal_eq_span_singleton_of_ringEquiv
    {S A : Type*} [CommRing S] [CommRing A] [IsLocalRing S] [IsLocalRing A] (e : S ≃+* A) {ϖ : A}
    (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) :
    IsLocalRing.maximalIdeal S = Ideal.span {e.symm ϖ} := by
  ext s
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Ideal.mem_span_singleton']
  have h1 : IsUnit s ↔ IsUnit (e s) :=
    ⟨fun h => h.map e, fun h => by simpa using h.map e.symm⟩
  rw [h1, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, hϖ, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨e.symm a, ?_⟩
    apply e.injective
    rw [map_mul, e.apply_symm_apply, e.apply_symm_apply, ha]
  · rintro ⟨a, rfl⟩
    exact ⟨e a, by rw [map_mul, e.apply_symm_apply]⟩

end AlgebraCore

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "kaehlerToFunctionField kaehlerToFunctionField_D kaehlerToFunctionField_smul placesOf Place baseToFunctionField"
namespace RegAux
p2m_open "AlgebraicCurve"

variable {k : Type u} [Field k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k))

@[reducible] noncomputable def algebraStalk (x : X) : Algebra k (X.presheaf.stalk x) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ c.app ⊤ ≫ X.presheaf.germ (c ⁻¹ᵁ ⊤) x trivial).hom.toAlgebra

theorem isScalarTower_sections_stalk (W : X.Opens) (x : X) (hx : x ∈ W) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c W
    letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : W)
    letI := algebraStalk c x
    IsScalarTower k Γ(X, W) (X.presheaf.stalk x) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c W
  letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : W)
  letI := algebraStalk c x
  refine IsScalarTower.of_algebraMap_eq' ?_
  change _ = (X.presheaf.germ W x hx).hom.comp (((Scheme.ΓSpecIso (.of k)).inv ≫ c.appLE ⊤ W le_top).hom)
  rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.appLE, Category.assoc,
    TopCat.Presheaf.germ_res]

theorem isScalarTower_stalk_functionField [IsIntegral X] (x : X) :
    letI := algebraStalk c x
    letI := (baseToFunctionField c).toAlgebra
    IsScalarTower k (X.presheaf.stalk x) X.functionField := by
  letI := algebraStalk c x
  letI := (baseToFunctionField c).toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, baseToFunctionField,
    ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  congr 1
  simp only [Category.assoc]
  congr 1

  rw [TopCat.Presheaf.germ_stalkSpecializes]
  rfl

theorem algebraMap_algebraStalk (x : X) :
    letI := algebraStalk c x
    algebraMap k (X.presheaf.stalk x) =
      (c.stalkMap x).hom.comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).presheaf.germ ⊤ (c x) trivial).hom := by
  letI := algebraStalk c x
  rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.germ_stalkMap]

theorem essFiniteType_stalk [LocallyOfFiniteType c] (x : X) :
    letI := algebraStalk c x
    Algebra.EssFiniteType k (X.presheaf.stalk x) := by
  letI := algebraStalk c x
  rw [← RingHom.essFiniteType_algebraMap, algebraMap_algebraStalk]
  refine RingHom.EssFiniteType.comp ?_ (LocallyOfFiniteType.stalkMap c x)
  rw [← Spec.algebraMap_stalkIso_inv, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  refine RingHom.EssFiniteType.comp ?_ ?_
  · rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization _ (c x).asIdeal.primeCompl
  · exact RingHom.FiniteType.essFiniteType
      (RingHom.FiniteType.of_surjective _ (Spec.stalkIso (.of k) (c x)).commRingCatIsoToRingEquiv.symm.surjective)

theorem finite_kaehler_stalk [LocallyOfFiniteType c] (x : X) :
    letI := algebraStalk c x
    Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] := by
  letI := algebraStalk c x
  haveI := essFiniteType_stalk c x
  infer_instance

theorem fromSpecResidueField_comp (x : X) :
    X.fromSpecResidueField x ≫ c =
      Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ c.app ⊤ ≫ X.presheaf.germ (c ⁻¹ᵁ ⊤) x trivial ≫
        X.residue x) := by
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp, ← Spec.map_comp,
    Scheme.Spec.algebraMap_residueFieldIso_inv]
  simp only [Category.assoc, Scheme.residue_residueFieldMap, Scheme.Hom.germ_stalkMap_assoc]

theorem finite_residueField_of_isClosed [LocallyOfFiniteType c] (x : X) (hx : IsClosed ({x} : Set X)) :
    letI := algebraStalk c x
    Module.Finite k (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
  letI := algebraStalk c x
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace c
  haveI : LocallyOfFiniteType (X.fromSpecResidueField x) := isClosed_singleton_iff_locallyOfFiniteType.mp hx
  have hf : IsFinite (X.fromSpecResidueField x ≫ c) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  rw [fromSpecResidueField_comp, IsFinite.SpecMap_iff] at hf
  have : (algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x))) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ c.app ⊤ ≫ X.presheaf.germ (c ⁻¹ᵁ ⊤) x trivial ≫ X.residue x).hom := by
    rfl
  rw [← RingHom.finite_algebraMap, this]
  exact hf

theorem formallyUnramified_residueField_of_isClosed [PerfectField k] [LocallyOfFiniteType c] (x : X)
    (hx : IsClosed ({x} : Set X)) :
    letI := algebraStalk c x
    Algebra.FormallyUnramified k (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
  letI := algebraStalk c x
  haveI := finite_residueField_of_isClosed c x hx
  haveI : Algebra.IsAlgebraic k (IsLocalRing.ResidueField (X.presheaf.stalk x)) := inferInstance
  exact Algebra.FormallyUnramified.of_isSeparable _ _

theorem locallyOfFiniteType_of_smoothOfRelativeDimension [SmoothOfRelativeDimension 1 c] :
    LocallyOfFiniteType c :=
  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  inferInstance

end AlgebraicCurve.RegAux

open AlgebraicCurve.RegAux in
theorem solution
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [SmoothOfRelativeDimension 1 c]
    (U : X.Opens) [Nonempty U]
    (η : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U; Ω[Γ(X, U)⁄k])
    (v : letI := (baseToFunctionField c).toAlgebra; Place k X.functionField)
    (hv : letI := (baseToFunctionField c).toAlgebra; v ∈ placesOf c U) :
    letI := (baseToFunctionField c).toAlgebra
    ∃ f ∈ v.toValuationSubring, kaehlerToFunctionField c U η = f • v.dCoord := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI := (baseToFunctionField c).toAlgebra
  obtain ⟨x, hxU, hxcl, hrange⟩ := hv

  letI := algebraStalk c x
  letI := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
  haveI := isScalarTower_sections_stalk c U x hxU
  haveI := isScalarTower_stalk_functionField c x
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk x) X.functionField := functionField_isScalarTower X U ⟨x, hxU⟩
  have hφ : algebraMap Γ(X, U) X.functionField =
      (algebraMap (X.presheaf.stalk x) X.functionField).comp (algebraMap Γ(X, U) (X.presheaf.stalk x)) :=
    IsScalarTower.algebraMap_eq Γ(X, U) (X.presheaf.stalk x) X.functionField
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) :=
    IsFractionRing.injective (X.presheaf.stalk x) X.functionField

  have hmem : ∀ s, algebraMap (X.presheaf.stalk x) X.functionField s ∈ v.toValuationSubring := fun s => by
    have : algebraMap (X.presheaf.stalk x) X.functionField s ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range :=
      ⟨s, rfl⟩
    rw [hrange] at this
    exact this
  have hsurj : ∀ t ∈ v.toValuationSubring, ∃ s, algebraMap (X.presheaf.stalk x) X.functionField s = t := fun t ht => by
    have : t ∈ v.toValuationSubring.toSubring := ht
    rw [← hrange] at this
    exact this
  let ψ : X.presheaf.stalk x →+* v.toValuationSubring :=
    (algebraMap (X.presheaf.stalk x) X.functionField).codRestrict v.toValuationSubring hmem
  have hψ : Function.Bijective ψ :=
    ⟨fun a b h => hinj (congrArg Subtype.val h), fun t => by
      obtain ⟨s, hs⟩ := hsurj t.1 t.2; exact ⟨s, Subtype.ext hs⟩⟩
  let e : X.presheaf.stalk x ≃+* v.toValuationSubring := RingEquiv.ofBijective ψ hψ
  have he : ∀ s, ((e s : v.toValuationSubring) : X.functionField) = algebraMap _ X.functionField s := fun s => rfl

  have hϖ := (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec
  have hdC : v.dCoord = D k X.functionField
      (((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : v.toValuationSubring) :
        X.functionField) := rfl
  have hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk x) =
      Ideal.span {e.symm (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose} :=
    IsLocalRing.maximalIdeal_eq_span_singleton_of_ringEquiv e hϖ.maximalIdeal_eq
  have hφπ : algebraMap (X.presheaf.stalk x) X.functionField
      (e.symm (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose) =
      (((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : v.toValuationSubring) :
        X.functionField) := by
    rw [← he, e.apply_symm_apply]

  haveI := locallyOfFiniteType_of_smoothOfRelativeDimension c
  haveI hfin : Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] := finite_kaehler_stalk c x

  haveI hunr : Algebra.FormallyUnramified k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    formallyUnramified_residueField_of_isClosed c x hxcl

  have hspan := KaehlerDifferential.span_singleton_D_eq_top_of_maximalIdeal_eq_span (k := k) hmax

  have hD : ∀ s' : X.presheaf.stalk x, ∃ t : X.presheaf.stalk x,
      D k X.functionField (algebraMap _ X.functionField s') =
        algebraMap _ X.functionField t • v.dCoord := fun s' => by
    obtain ⟨t, ht⟩ := KaehlerDifferential.exists_map_eq_smul_D_of_span_singleton_eq_top
      (F := X.functionField) hspan (D k (X.presheaf.stalk x) s')
    refine ⟨t, ?_⟩
    rw [KaehlerDifferential.map_D] at ht
    rw [ht, hφπ, hdC]

  have hgen : ∀ b : Γ(X, U), kaehlerToFunctionField c U (D k Γ(X, U) b) =
      D k X.functionField (algebraMap _ X.functionField (algebraMap Γ(X, U) (X.presheaf.stalk x) b)) := fun b => by
    rw [kaehlerToFunctionField_D, ← RingHom.comp_apply, ← hφ]
    rfl

  suffices H : ∀ θ ∈ Submodule.span Γ(X, U) (Set.range (D k Γ(X, U))),
      ∃ s : X.presheaf.stalk x, kaehlerToFunctionField c U θ = algebraMap _ X.functionField s • v.dCoord by
    obtain ⟨s, hs⟩ := H η (by rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top)
    exact ⟨_, hmem s, hs⟩
  intro θ hθ
  refine Submodule.span_induction ?_ ⟨0, by simp⟩ ?_ ?_ hθ
  · rintro _ ⟨b, rfl⟩
    obtain ⟨t, ht⟩ := hD (algebraMap Γ(X, U) (X.presheaf.stalk x) b)
    exact ⟨t, by rw [hgen, ht]⟩
  · rintro θ₁ θ₂ - - ⟨s₁, h₁⟩ ⟨s₂, h₂⟩
    exact ⟨s₁ + s₂, by rw [map_add, h₁, h₂, map_add, add_smul]⟩
  · rintro a θ - ⟨s, hs⟩
    refine ⟨algebraMap Γ(X, U) (X.presheaf.stalk x) a * s, ?_⟩
    rw [kaehlerToFunctionField_smul, hs, map_mul, ← RingHom.comp_apply, ← hφ, smul_smul]
    rfl

end S_AlgebraicCurve_exists_kaehlerToFunctionField_eq_smul_dCoord_of_mem_placesOf
end P2MW
export P2MW.S_AlgebraicCurve_exists_kaehlerToFunctionField_eq_smul_dCoord_of_mem_placesOf (solution)
