-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.flat_aeval_of_twoChartPoleDatum_global
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/feddaf9c-4104-5511-afd6-1bf0916a9624

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_injective_aeval_tensor_of_twoChartPoleDatum_global
import Theorems.Thm_AlgebraicGeometry_isDomain_tensorProduct_sections_of_geometricallyIntegral
import Theorems.Thm_Module_Flat_of_finitePresentation_of_forall_flat_residueField_tensorProduct
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_flat_aeval_of_twoChartPoleDatum_global

universe u

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_SmoothProperCurve_flat_aeval_of_twoChartPoleDatum_global.AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve P2MW.S_AlgebraicGeometry_SmoothProperCurve_flat_aeval_of_twoChartPoleDatum_global.AlgebraicGeometry.SmoothProperCurve NeronModelInfra"

p2m_open_scoped "Polynomial AlgebraicGeometry.Polynomial"

set_option maxHeartbeats 1600000

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension.smooth SmoothOfRelativeDimension IsProper GeometricallyIntegral Spec Scheme Smooth Flat HasRingHomProperty.appLE isAffineOpen_top IsAffineOpen Flat.comp LocallyOfFinitePresentation HasRingHomProperty geometrically Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom isDomain_tensorProduct_sections_of_geometricallyIntegral" namespace SmoothProperCurve p2m_export "AlgebraicGeometry.SmoothProperCurve" "injective_aeval_tensor_of_twoChartPoleDatum_global" end AlgebraicGeometry.SmoothProperCurve
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve" in

theorem AlgebraicGeometry.SmoothProperCurve.flat_aeval_of_twoChartPoleDatum_global
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U V : C.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (hUε : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hf : U ⊓ V = C.basicOpen f) (hg : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Flat := by
  letI algU := Scheme.TwoAffineOpenCover.algebraOfHom c U
  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c

  have hQfp : RingHom.FinitePresentation (c.appLE ⊤ U le_top).hom :=
    HasRingHomProperty.appLE @LocallyOfFinitePresentation c inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have hQfl : RingHom.Flat (c.appLE ⊤ U le_top).hom :=
    HasRingHomProperty.appLE @Flat c inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  haveI hfpU : Algebra.FinitePresentation R Γ(C, U) :=
    RingHom.finitePresentation_respectsIso.2 (c.appLE ⊤ U le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv hQfp
  haveI hflU : Module.Flat R Γ(C, U) :=
    RingHom.Flat.respectsIso.2 (c.appLE ⊤ U le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv hQfl

  letI algX : Algebra R[X] Γ(C, U) := (Polynomial.aeval f : R[X] →ₐ[R] Γ(C, U)).toRingHom.toAlgebra
  haveI : IsScalarTower R R[X] Γ(C, U) :=
    IsScalarTower.of_algebraMap_eq (fun r => ((Polynomial.aeval f : R[X] →ₐ[R] Γ(C, U)).commutes r).symm)
  show Module.Flat R[X] Γ(C, U)
  apply Module.Flat.of_finitePresentation_of_forall_flat_residueField_tensorProduct (R := R)
  intro p _
  have hto : IsScalarTower.toAlgHom R R[X] Γ(C, U) = Polynomial.aeval f := by
    apply Polynomial.algHom_ext
    rw [IsScalarTower.toAlgHom_apply]
    rfl
  rw [hto]

  have hcomp : (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
      (Polynomial.aeval f : R[X] →ₐ[R] Γ(C, U))).comp (polyEquivTensor' R p.ResidueField).toAlgHom =
      (Polynomial.aeval ((1 : p.ResidueField) ⊗ₜ[R] f) :
        (p.ResidueField)[X] →ₐ[p.ResidueField] p.ResidueField ⊗[R] Γ(C, U)) := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X, AlgHom.comp_apply]
    change Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField) (Polynomial.aeval f)
      (polyEquivTensor' R p.ResidueField Polynomial.X) = _
    rw [coe_polyEquivTensor', polyEquivTensor_apply, Polynomial.eval₂_X, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, Polynomial.aeval_X]
  have key : Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
      (Polynomial.aeval f : R[X] →ₐ[R] Γ(C, U)) =
      (Polynomial.aeval ((1 : p.ResidueField) ⊗ₜ[R] f) :
        (p.ResidueField)[X] →ₐ[p.ResidueField] p.ResidueField ⊗[R] Γ(C, U)).comp
        (polyEquivTensor' R p.ResidueField).symm.toAlgHom := by
    rw [← hcomp, AlgHom.comp_assoc, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.comp_symm,
      AlgHom.comp_id]

  have hflat' : (Polynomial.aeval ((1 : p.ResidueField) ⊗ₜ[R] f) :
      (p.ResidueField)[X] →ₐ[p.ResidueField] p.ResidueField ⊗[R] Γ(C, U)).toRingHom.Flat := by
    letI := (Polynomial.aeval ((1 : p.ResidueField) ⊗ₜ[R] f) :
      (p.ResidueField)[X] →ₐ[p.ResidueField] p.ResidueField ⊗[R] Γ(C, U)).toRingHom.toAlgebra
    show Module.Flat (p.ResidueField)[X] (p.ResidueField ⊗[R] Γ(C, U))
    by_cases htriv : Subsingleton (p.ResidueField ⊗[R] Γ(C, U))
    · infer_instance
    · haveI hne : Nontrivial (p.ResidueField ⊗[R] Γ(C, U)) := not_subsingleton_iff_nontrivial.mp htriv
      haveI : IsDomain (p.ResidueField ⊗[R] Γ(C, U)) :=
        isDomain_tensorProduct_sections_of_geometricallyIntegral c U hU p.ResidueField hne
      have hinj := injective_aeval_tensor_of_twoChartPoleDatum_global R c ε U V hU hV hUV hUε f g hf hg hfg
        p.ResidueField hne
      haveI : Module.IsTorsionFree (p.ResidueField)[X] (p.ResidueField ⊗[R] Γ(C, U)) :=
        Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
      infer_instance
  rw [key]
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective (polyEquivTensor' R p.ResidueField).symm.bijective) hflat'

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U V : C.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (hUε : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hf : U ⊓ V = C.basicOpen f) (hg : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Flat :=
  AlgebraicGeometry.SmoothProperCurve.flat_aeval_of_twoChartPoleDatum_global R c ε U V hU hV hUV hUε f g hf hg hfg

end S_AlgebraicGeometry_SmoothProperCurve_flat_aeval_of_twoChartPoleDatum_global
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothProperCurve_flat_aeval_of_twoChartPoleDatum_global (solution)
