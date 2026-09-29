-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.nontrivial_tensor_sections_of_twoChartPoleDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1bf2b701-353f-5cdd-897d-9d6939b306c9

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_section
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_nontrivial_tensor_sections_of_twoChartPoleDatum

set_option autoImplicit false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NONEMPTY

theorem exists_mem_fibre_not_mem_range
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (y : Spec (CommRingCat.of R)) :
    ∃ u : C, c.base u = y ∧ u ∉ Set.range ε.1.base := by

  let F := c.fiber y
  let ι := c.fiberι y
  let q := c.fiberToSpecResidueField y
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI hsrd : SmoothOfRelativeDimension 1 q := by
    show SmoothOfRelativeDimension 1 (pullback.snd _ _)
    exact MorphismProperty.pullback_snd _ _ inferInstance
  let p : Spec ((Spec (CommRingCat.of R)).residueField y) ⟶ F :=
    pullback.lift ((Spec (CommRingCat.of R)).fromSpecResidueField y ≫ ε.1) (𝟙 _)
      (by rw [Category.assoc, ε.2, Category.comp_id, Category.id_comp])
  have hp : p ≫ q = 𝟙 _ := pullback.lift_snd _ _ _
  have hpι : p ≫ ι = (Spec (CommRingCat.of R)).fromSpecResidueField y ≫ ε.1 := pullback.lift_fst _ _ _

  let x₀ : F := p.base (IsLocalRing.closedPoint ((Spec (CommRingCat.of R)).residueField y))
  haveI hdvr : IsDiscreteValuationRing (F.presheaf.stalk x₀) :=
    @AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_section _ _ F q
      inferInstance hsrd p hp

  let S := F.presheaf.stalk x₀
  let η : Spec (F.presheaf.stalk x₀) := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : η ≠ IsLocalRing.closedPoint S := by
    intro h
    have := congrArg PrimeSpectrum.asIdeal h
    exact IsDiscreteValuationRing.not_a_field S this.symm
  let u' : F := (F.fromSpecStalk x₀).base η
  have hu' : u' ≠ x₀ := by
    intro h
    apply hη
    apply (F.fromSpecStalk x₀).isEmbedding.injective
    change (F.fromSpecStalk x₀).base η = (F.fromSpecStalk x₀).base (IsLocalRing.closedPoint S)
    erw [Scheme.fromSpecStalk_closedPoint]
    exact h

  refine ⟨ι.base u', ?_, ?_⟩
  · have : ι.base u' ∈ Set.range (c.fiberι y).base := ⟨u', rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  · rintro ⟨y', hy'⟩

    have hcε : ∀ z, c.base (ε.1.base z) = z := fun z => by
      have := Scheme.Hom.comp_apply ε.1 c z
      rw [ε.2] at this
      exact this.symm
    have hyy : y' = y := by
      have h1 := hcε y'
      rw [hy'] at h1
      have : ι.base u' ∈ Set.range (c.fiberι y).base := ⟨u', rfl⟩
      rw [Scheme.Hom.range_fiberι] at this
      rw [← h1]; exact this
    subst hyy
    apply hu'
    apply ι.isEmbedding.injective
    rw [← hy']
    show _ = ι.base (p.base _)
    rw [← Scheme.Hom.comp_apply, hpι, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

end NONEMPTY

namespace NONEMPTY

theorem nontrivial_tensor_fields {R : Type u} [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime]
    (K F : Type u) [Field K] [Field F] [Algebra R K] [Algebra R F]
    (hK : ∀ r, algebraMap R K r = 0 ↔ r ∈ 𝔭) (hF : ∀ r, algebraMap R F r = 0 ↔ r ∈ 𝔭) :
    Nontrivial (K ⊗[R] F) := by
  let κ := 𝔭.ResidueField

  have liftable : ∀ (L : Type u) [Field L] [Algebra R L], (∀ r, algebraMap R L r = 0 ↔ r ∈ 𝔭) →
      𝔭.primeCompl ≤ (IsUnit.submonoid L).comap (algebraMap R L) := by
    intro L _ _ hL r hr
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero, ne_eq, hL]
    exact hr
  have hK' : 𝔭 ≤ RingHom.ker (algebraMap R K) := fun r hr => (hK r).mpr hr
  have hF' : 𝔭 ≤ RingHom.ker (algebraMap R F) := fun r hr => (hF r).mpr hr
  letI algK : Algebra κ K := (Ideal.ResidueField.lift 𝔭 (algebraMap R K) hK' (liftable K hK)).toAlgebra
  letI algF : Algebra κ F := (Ideal.ResidueField.lift 𝔭 (algebraMap R F) hF' (liftable F hF)).toAlgebra
  haveI : IsScalarTower R κ K := IsScalarTower.of_algebraMap_eq fun r =>
    (Ideal.ResidueField.lift_algebraMap 𝔭 (algebraMap R K) hK' _ r).symm
  haveI : IsScalarTower R κ F := IsScalarTower.of_algebraMap_eq fun r =>
    (Ideal.ResidueField.lift_algebraMap 𝔭 (algebraMap R F) hF' _ r).symm

  haveI : Nontrivial (K ⊗[κ] F) := inferInstance

  let L : K ⊗[R] F →ₗ[R] K ⊗[κ] F :=
    TensorProduct.lift
      { toFun := fun k => { toFun := fun f => k ⊗ₜ[κ] f
                            map_add' := fun a b => TensorProduct.tmul_add _ _ _
                            map_smul' := fun r f => by
                              simp only [RingHom.id_apply]
                              rw [← algebraMap_smul κ r f, TensorProduct.tmul_smul, algebraMap_smul] }
        map_add' := fun a b => by ext f; exact TensorProduct.add_tmul _ _ _
        map_smul' := fun r k => by
          ext f
          simp only [RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply]
          rw [← algebraMap_smul κ r k, ← algebraMap_smul κ r (k ⊗ₜ[κ] f), TensorProduct.smul_tmul'] }
  have hL : L ((1 : K) ⊗ₜ[R] (1 : F)) = (1 : K ⊗[κ] F) := by
    simp [L, TensorProduct.lift.tmul, Algebra.TensorProduct.one_def]
  refine ⟨⟨(1 : K) ⊗ₜ[R] (1 : F), 0, fun h => ?_⟩⟩
  have := congrArg L h
  rw [hL, map_zero] at this
  exact one_ne_zero this

theorem eval_algebraMap_eq_zero_iff
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {U : C.Opens} (u : C) (hu : u ∈ U) (r : R) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    (C.evaluation U u hu).hom (algebraMap R Γ(C, U) r) = 0 ↔ r ∈ (c.base u).asIdeal := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  erw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen, Scheme.basicOpen_appLE, basicOpen_eq_of_affine]
  rw [TopologicalSpace.Opens.mem_inf, not_and]
  constructor
  · intro h
    have h2 : u ∉ c ⁻¹ᵁ PrimeSpectrum.basicOpen r := h hu
    change ¬ (c.base u ∈ PrimeSpectrum.basicOpen r) at h2
    exact not_not.mp ((not_congr (PrimeSpectrum.mem_basicOpen r (c.base u))).mp h2)
  · intro hr _
    change ¬ (c.base u ∈ PrimeSpectrum.basicOpen r)
    exact fun h => ((PrimeSpectrum.mem_basicOpen r (c.base u)).mp h) hr

theorem main
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U V : C.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (hUε : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hf : U ⊓ V = C.basicOpen f) (hg : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (K : Type u) [Field K] [Algebra R K] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Nontrivial (K ⊗[R] Γ(C, U)) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  haveI : (RingHom.ker (algebraMap R K)).IsPrime := RingHom.ker_isPrime _

  let y : Spec (CommRingCat.of R) := ⟨RingHom.ker (algebraMap R K), RingHom.ker_isPrime _⟩
  obtain ⟨u, hcu, hur⟩ := exists_mem_fibre_not_mem_range c ε y
  have hu : u ∈ U := (hUε u).mpr hur

  let ev : Γ(C, U) →+* C.residueField u := (C.evaluation U u hu).hom
  letI algRF : Algebra R (C.residueField u) := (ev.comp (algebraMap R Γ(C, U))).toAlgebra
  let evₐ : Γ(C, U) →ₐ[R] C.residueField u :=
    { ev with commutes' := fun _ => rfl }
  have hF : ∀ r : R, algebraMap R (C.residueField u) r = 0 ↔ r ∈ RingHom.ker (algebraMap R K) := by
    intro r
    show ev (algebraMap R Γ(C, U) r) = 0 ↔ _
    rw [eval_algebraMap_eq_zero_iff c u hu r, hcu]
  have hK : ∀ r : R, algebraMap R K r = 0 ↔ r ∈ RingHom.ker (algebraMap R K) := fun r => Iff.rfl
  haveI := nontrivial_tensor_fields (RingHom.ker (algebraMap R K)) K (C.residueField u) hK hF
  exact (Algebra.TensorProduct.map (AlgHom.id K K) evₐ).toRingHom.domain_nontrivial

end NONEMPTY

open scoped TensorProduct in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra in

theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U V : C.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (hUε : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hf : U ⊓ V = C.basicOpen f) (hg : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (K : Type u) [Field K] [Algebra R K] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Nontrivial (K ⊗[R] Γ(C, U)) :=
  NONEMPTY.main R c ε U V hU hV hUV hUε f g hf hg hfg K

end S_AlgebraicGeometry_SmoothProperCurve_nontrivial_tensor_sections_of_twoChartPoleDatum
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothProperCurve_nontrivial_tensor_sections_of_twoChartPoleDatum (solution)
