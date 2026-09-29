-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.flat_aeval_of_twoChartPoleDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/a54fd224-7a03-52ff-a2eb-a169b5c18684

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Theorems.Thm_Module_Flat_of_finitePresentation_of_forall_flat_residueField_tensorProduct
import Theorems.Thm_AlgebraicGeometry_isDomain_tensorProduct_sections_of_geometricallyIntegral
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_injective_aeval_tensor_of_twoChartPoleDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_flat_aeval_of_twoChartPoleDatum

set_option autoImplicit false

universe u

open scoped TensorProduct
open Polynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace U3bFLAT

theorem flat_aeval_of_injective {κ D : Type u} [Field κ] [CommRing D] [IsDomain D] [Algebra κ D] (y : D)
    (hinj : Function.Injective (Polynomial.aeval y : κ[X] →ₐ[κ] D)) :
    (Polynomial.aeval y : κ[X] →ₐ[κ] D).toRingHom.Flat := by
  letI : Algebra κ[X] D := (Polynomial.aeval y : κ[X] →ₐ[κ] D).toRingHom.toAlgebra
  haveI : Module.IsTorsionFree κ[X] D := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  show Module.Flat κ[X] D
  infer_instance

theorem flat_of_subsingleton {A D : Type u} [CommRing A] [CommRing D] [Subsingleton D] (φ : A →+* D) :
    φ.Flat := by
  letI : Algebra A D := φ.toAlgebra
  show Module.Flat A D
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f _
  haveI : Subsingleton (N ⊗[A] D) := inferInstance
  exact Function.injective_of_subsingleton _

section Sections

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))

theorem flat_sections [Flat c] {U : X.Opens} (hU : IsAffineOpen U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Module.Flat R Γ(X, U) := by
  have h : RingHom.Flat (c.appLE ⊤ U le_top).hom :=
    HasRingHomProperty.appLE (P := @Flat) (f := c) inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h2 : RingHom.Flat ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U le_top).hom := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp
      (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact h2

theorem finitePresentation_sections [LocallyOfFinitePresentation c] {U : X.Opens} (hU : IsAffineOpen U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Algebra.FinitePresentation R Γ(X, U) := by
  have h : RingHom.FinitePresentation (c.appLE ⊤ U le_top).hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) (f := c) inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h2 : RingHom.FinitePresentation ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U le_top).hom := by
    rw [CommRingCat.hom_comp]
    exact RingHom.finitePresentation_respectsIso.2 _
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv h
  exact h2

end Sections

section FibreMap

variable {R : Type u} [CommRing R] {B : Type u} [CommRing B] [Algebra R B] (f : B)
  (κ : Type u) [Field κ] [Algebra R κ]

theorem fibreMap_comp_polyEquivTensor
    [Algebra R[X] B] [IsScalarTower R R[X] B] (hX : algebraMap R[X] B Polynomial.X = f) :
    (Algebra.TensorProduct.map (AlgHom.id κ κ) (IsScalarTower.toAlgHom R R[X] B)).toRingHom.comp
        (polyEquivTensor R κ).toRingHom =
      (Polynomial.aeval ((1 : κ) ⊗ₜ[R] f) : κ[X] →ₐ[κ] κ ⊗[R] B).toRingHom := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp [polyEquivTensor_apply, Algebra.algebraMap_eq_smul_one]
    first
    | rfl
    | (rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one])
  · simp [polyEquivTensor_apply, hX]

theorem flat_fibreMap_of_flat_aeval
    [Algebra R[X] B] [IsScalarTower R R[X] B] (hX : algebraMap R[X] B Polynomial.X = f)
    (h : (Polynomial.aeval ((1 : κ) ⊗ₜ[R] f) : κ[X] →ₐ[κ] κ ⊗[R] B).toRingHom.Flat) :
    (Algebra.TensorProduct.map (AlgHom.id κ κ) (IsScalarTower.toAlgHom R R[X] B)).toRingHom.Flat := by
  have key := fibreMap_comp_polyEquivTensor f κ hX
  have h1 : ((Algebra.TensorProduct.map (AlgHom.id κ κ) (IsScalarTower.toAlgHom R R[X] B)).toRingHom.comp
        (polyEquivTensor R κ).toRingHom).Flat := by
    rw [key]; exact h
  have h2 := RingHom.Flat.respectsIso.2 _ (polyEquivTensor R κ).symm.toRingEquiv h1

  have h3 : ((Algebra.TensorProduct.map (AlgHom.id κ κ) (IsScalarTower.toAlgHom R R[X] B)).toRingHom.comp
        (polyEquivTensor R κ).toRingHom).comp (polyEquivTensor R κ).symm.toRingEquiv.toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id κ κ) (IsScalarTower.toAlgHom R R[X] B)).toRingHom := by
    refine RingHom.ext fun y => ?_
    show (Algebra.TensorProduct.map (AlgHom.id κ κ) (IsScalarTower.toAlgHom R R[X] B))
        ((polyEquivTensor R κ) ((polyEquivTensor R κ).symm y)) = _
    rw [AlgEquiv.apply_symm_apply]
    rfl
  rw [h3] at h2
  exact h2

end FibreMap

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
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Flat := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U

  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  haveI : Module.Flat R Γ(C, U) := flat_sections c hU
  haveI : Algebra.FinitePresentation R Γ(C, U) := finitePresentation_sections c hU

  letI algXB : Algebra R[X] Γ(C, U) := (Polynomial.aeval f : R[X] →ₐ[R] Γ(C, U)).toRingHom.toAlgebra
  haveI : IsScalarTower R R[X] Γ(C, U) := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap R Γ(C, U) r = (Polynomial.aeval f : R[X] →ₐ[R] Γ(C, U)) (algebraMap R R[X] r)
    rw [AlgHom.commutes]
  have hX : algebraMap R[X] Γ(C, U) Polynomial.X = f := Polynomial.aeval_X f

  show Module.Flat R[X] Γ(C, U)
  refine Module.Flat.of_finitePresentation_of_forall_flat_residueField_tensorProduct
    (R := R) (A := R[X]) (B := Γ(C, U)) fun p _ => ?_
  refine flat_fibreMap_of_flat_aeval f p.ResidueField hX ?_
  by_cases hne : Nontrivial (p.ResidueField ⊗[R] Γ(C, U))
  · haveI := AlgebraicGeometry.isDomain_tensorProduct_sections_of_geometricallyIntegral c U hU
      p.ResidueField hne
    exact flat_aeval_of_injective _
      (AlgebraicGeometry.SmoothProperCurve.injective_aeval_tensor_of_twoChartPoleDatum
        R c ε U V hU hV hUV hUε f g hf hg hfg p.ResidueField hne)
  · haveI : Subsingleton (p.ResidueField ⊗[R] Γ(C, U)) := not_nontrivial_iff_subsingleton.mp hne
    exact flat_of_subsingleton _

end U3bFLAT

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
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Flat :=
  U3bFLAT.main R c ε U V hU hV hUV hUε f g hf hg hfg

end S_AlgebraicGeometry_SmoothProperCurve_flat_aeval_of_twoChartPoleDatum
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothProperCurve_flat_aeval_of_twoChartPoleDatum (solution)
