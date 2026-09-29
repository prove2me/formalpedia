-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.finrank_levelSet_field_of_twoChartPoleDatum_of_forall_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1c6a7a42-a969-5074-a257-063c57d29702

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_nontrivial_tensor_sections_of_twoChartPoleDatum_global
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_injective_aeval_tensor_of_twoChartPoleDatum_global
import Theorems.Thm_AlgebraicGeometry_isDomain_tensorProduct_sections_of_geometricallyIntegral
import Theorems.Thm_Algebra_finrank_quotient_span_sub_eq_of_isLocalization_away_of_mul_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_finrank_levelSet_field_of_twoChartPoleDatum_of_forall_finrank

universe u

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_SmoothProperCurve_finrank_levelSet_field_of_twoChartPoleDatum_of_forall_finrank.AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve P2MW.S_AlgebraicGeometry_SmoothProperCurve_finrank_levelSet_field_of_twoChartPoleDatum_of_forall_finrank.AlgebraicGeometry.SmoothProperCurve NeronModelInfra"

p2m_open_scoped "Polynomial AlgebraicGeometry.Polynomial"

set_option maxHeartbeats 1600000

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective SmoothOfRelativeDimension IsProper GeometricallyIntegral Spec Scheme IsAffineOpen Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.restrictAlgHom isDomain_tensorProduct_sections_of_geometricallyIntegral"
namespace SmoothProperCurve
p2m_export "AlgebraicGeometry.SmoothProperCurve" "nontrivial_tensor_sections_of_twoChartPoleDatum_global injective_aeval_tensor_of_twoChartPoleDatum_global"
namespace LevelSetGlobal
p2m_open "AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Polynomial"

theorem finite_aeval_tmul {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (L : Type u) [CommRing L] [Algebra R L] (f : A)
    (hfin : (Polynomial.aeval f : R[X] →ₐ[R] A).toRingHom.Finite) :
    (Polynomial.aeval ((1 : L) ⊗ₜ[R] f) : L[X] →ₐ[L] L ⊗[R] A).toRingHom.Finite := by
  letI algA : Algebra R[X] A := (Polynomial.aeval f : R[X] →ₐ[R] A).toRingHom.toAlgebra
  letI algD : Algebra L[X] (L ⊗[R] A) := (Polynomial.aeval ((1 : L) ⊗ₜ[R] f) : L[X] →ₐ[L] L ⊗[R] A).toRingHom.toAlgebra
  have hfinA : Module.Finite R[X] A := hfin
  show Module.Finite L[X] (L ⊗[R] A)
  obtain ⟨s, hs⟩ := hfinA
  classical
  refine ⟨⟨s.image (fun a => (1 : L) ⊗ₜ[R] a), ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  rintro z -
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul l a =>
    have ha : a ∈ Submodule.span R[X] (s : Set A) := by rw [hs]; exact Submodule.mem_top

    have key : ∀ a' ∈ Submodule.span R[X] (s : Set A),
        (1 : L) ⊗ₜ[R] a' ∈ Submodule.span L[X] ((fun a => (1 : L) ⊗ₜ[R] a) '' (s : Set A)) := by
      intro a' ha'
      induction ha' using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hx hy
      | smul p x _ hx =>
        have h1 : (1 : L) ⊗ₜ[R] (p • x) = (Polynomial.map (algebraMap R L) p) • ((1 : L) ⊗ₜ[R] x) := by
          change (1 : L) ⊗ₜ[R] (Polynomial.aeval f p * x) =
            Polynomial.aeval ((1 : L) ⊗ₜ[R] f) (Polynomial.map (algebraMap R L) p) * ((1 : L) ⊗ₜ[R] x)
          rw [Polynomial.aeval_map_algebraMap, show ((1 : L) ⊗ₜ[R] f) =
            (Algebra.TensorProduct.includeRight : A →ₐ[R] L ⊗[R] A) f from rfl, Polynomial.aeval_algHom_apply]
          change _ = ((1 : L) ⊗ₜ[R] (Polynomial.aeval f p)) * ((1 : L) ⊗ₜ[R] x)
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        rw [h1]
        exact Submodule.smul_mem _ _ hx
    have h2 : l ⊗ₜ[R] a = (Polynomial.C l : L[X]) • ((1 : L) ⊗ₜ[R] a) := by
      change l ⊗ₜ[R] a = Polynomial.aeval ((1 : L) ⊗ₜ[R] f) (Polynomial.C l) * ((1 : L) ⊗ₜ[R] a)
      rw [Polynomial.aeval_C, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [h2]
    exact Submodule.smul_mem _ _ (key a ha)

theorem finrank_tensor_quotient_span_tmul {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (L : Type u) [Field L] [Algebra R L] (g : A) :
    Module.finrank L (L ⊗[R] A ⧸ Ideal.span {(1 : L) ⊗ₜ[R] g}) =
      Module.finrank L (L ⊗[R] (A ⧸ Ideal.span {g})) := by

  let μ : A →ₗ[R] A := LinearMap.mulRight R g
  let π : A →ₗ[R] A ⧸ Ideal.span {g} := (Ideal.Quotient.mkₐ R (Ideal.span {g})).toLinearMap
  have hex : Function.Exact μ π := by
    intro y
    constructor
    · intro hy
      have hy' : y ∈ Ideal.span {g} := Ideal.Quotient.eq_zero_iff_mem.mp hy
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hy'
      exact ⟨b, hb⟩
    · rintro ⟨b, rfl⟩
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton'.mpr ⟨b, rfl⟩)
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hexL : Function.Exact (μ.baseChange L) (π.baseChange L) := by
    have := lTensor_exact L hex hπ
    simpa only [LinearMap.baseChange_eq_ltensor] using this
  have hπL : Function.Surjective (π.baseChange L) := by
    have := LinearMap.lTensor_surjective L hπ
    simpa only [LinearMap.baseChange_eq_ltensor] using this
  let e₁ : ((L ⊗[R] A) ⧸ LinearMap.range (μ.baseChange L)) ≃ₗ[L] L ⊗[R] (A ⧸ Ideal.span {g}) :=
    hexL.linearEquivOfSurjective hπL

  have hrange : LinearMap.range (μ.baseChange L) = (Ideal.span {(1 : L) ⊗ₜ[R] g}).restrictScalars L := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      change μ.baseChange L z ∈ Ideal.span {(1 : L) ⊗ₜ[R] g}
      induction z using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact Ideal.zero_mem _
      | add x y hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
      | tmul l a =>
        rw [LinearMap.baseChange_tmul]
        change l ⊗ₜ[R] (a * g) ∈ Ideal.span {(1 : L) ⊗ₜ[R] g}
        rw [show l ⊗ₜ[R] (a * g) = (l ⊗ₜ[R] a) * ((1 : L) ⊗ₜ[R] g) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    · intro z hz
      change z ∈ Ideal.span {(1 : L) ⊗ₜ[R] g} at hz
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      clear hz
      induction b using TensorProduct.induction_on with
      | zero => rw [zero_mul]; exact Submodule.zero_mem _
      | add x y hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
      | tmul l a =>
        refine ⟨l ⊗ₜ[R] a, ?_⟩
        rw [LinearMap.baseChange_tmul]
        change l ⊗ₜ[R] (a * g) = (l ⊗ₜ[R] a) * ((1 : L) ⊗ₜ[R] g)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  let e₀ : ((L ⊗[R] A) ⧸ Ideal.span {(1 : L) ⊗ₜ[R] g}) ≃ₗ[L]
      ((L ⊗[R] A) ⧸ LinearMap.range (μ.baseChange L)) :=
    (Submodule.Quotient.restrictScalarsEquiv L (Ideal.span {(1 : L) ⊗ₜ[R] g})).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hrange.symm
  exact (e₀ ≪≫ₗ e₁).finrank_eq

end AlgebraicGeometry.SmoothProperCurve.LevelSetGlobal

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Surjective SmoothOfRelativeDimension IsProper GeometricallyIntegral Spec Scheme IsAffineOpen Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.restrictAlgHom isDomain_tensorProduct_sections_of_geometricallyIntegral" namespace SmoothProperCurve p2m_export "AlgebraicGeometry.SmoothProperCurve" "nontrivial_tensor_sections_of_twoChartPoleDatum_global injective_aeval_tensor_of_twoChartPoleDatum_global" end AlgebraicGeometry.SmoothProperCurve
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve" in

theorem AlgebraicGeometry.SmoothProperCurve.finrank_levelSet_field_of_twoChartPoleDatum_of_forall_finrank
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U V : C.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (hUε : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hf : U ⊓ V = C.basicOpen f) (hg : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (m : ℕ)
    (hrank : ∀ (L : Type u) [Field L] [Algebra R L],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
      Module.finrank L (L ⊗[R] (Γ(C, V) ⧸ Ideal.span {g})) = m)
    (hfin : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U;
      (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Finite)
    (hfinV : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V;
      (Polynomial.aeval g : Polynomial R →ₐ[R] Γ(C, V)).toRingHom.Finite)
    (L : Type u) [Field L] [Algebra R L] (x : L) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Module.finrank L (L ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : L) ⊗ₜ[R] f - x ⊗ₜ[R] (1 : Γ(C, U))}) = m := by
  letI algU := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI algV := Scheme.TwoAffineOpenCover.algebraOfHom c V
  letI algW := Scheme.TwoAffineOpenCover.algebraOfHom c (U ⊓ V)
  let ρU : Γ(C, U) →ₐ[R] Γ(C, U ⊓ V) := Scheme.TwoAffineOpenCover.restrictAlgHom c inf_le_left
  let ρV : Γ(C, V) →ₐ[R] Γ(C, U ⊓ V) := Scheme.TwoAffineOpenCover.restrictAlgHom c inf_le_right
  let φ : L ⊗[R] Γ(C, U) →ₐ[L] L ⊗[R] Γ(C, U ⊓ V) := Algebra.TensorProduct.map (AlgHom.id L L) ρU
  let ψ : L ⊗[R] Γ(C, V) →ₐ[L] L ⊗[R] Γ(C, U ⊓ V) := Algebra.TensorProduct.map (AlgHom.id L L) ρV

  haveI hneU : Nontrivial (L ⊗[R] Γ(C, U)) :=
    nontrivial_tensor_sections_of_twoChartPoleDatum_global R c ε U V hU hV hUV hUε f g hf hg hfg L
  haveI hDdom : IsDomain (L ⊗[R] Γ(C, U)) :=
    isDomain_tensorProduct_sections_of_geometricallyIntegral c U hU L hneU
  have hinj : Function.Injective (Polynomial.aeval ((1 : L) ⊗ₜ[R] f) : L[X] →ₐ[L] L ⊗[R] Γ(C, U)) :=
    injective_aeval_tensor_of_twoChartPoleDatum_global R c ε U V hU hV hUV hUε f g hf hg hfg L hneU
  have hf0 : ((1 : L) ⊗ₜ[R] f : L ⊗[R] Γ(C, U)) ≠ 0 := by
    intro h0
    have h1 : (Polynomial.aeval ((1 : L) ⊗ₜ[R] f) : L[X] →ₐ[L] L ⊗[R] Γ(C, U)) Polynomial.X =
        (Polynomial.aeval ((1 : L) ⊗ₜ[R] f) : L[X] →ₐ[L] L ⊗[R] Γ(C, U)) 0 := by
      rw [Polynomial.aeval_X, map_zero, h0]
    exact Polynomial.X_ne_zero (hinj h1)

  have hlocU : @IsLocalization.Away _ _ f Γ(C, U ⊓ V) _ ρU.toRingHom.toAlgebra :=
    hU.isLocalization_of_eq_basicOpen f (homOfLE inf_le_left) hf
  have hlocV : @IsLocalization.Away _ _ g Γ(C, U ⊓ V) _ ρV.toRingHom.toAlgebra :=
    hV.isLocalization_of_eq_basicOpen g (homOfLE inf_le_right) hg
  have hφ : letI := φ.toRingHom.toAlgebra; IsLocalization.Away ((1 : L) ⊗ₜ[R] f) (L ⊗[R] Γ(C, U ⊓ V)) := by
    letI : Algebra Γ(C, U) Γ(C, U ⊓ V) := ρU.toRingHom.toAlgebra
    haveI : IsScalarTower R Γ(C, U) Γ(C, U ⊓ V) := IsScalarTower.of_algebraMap_eq (fun r => (ρU.commutes r).symm)
    haveI : IsLocalization (Submonoid.powers f) Γ(C, U ⊓ V) := hlocU
    letI : Algebra (L ⊗[R] Γ(C, U)) (L ⊗[R] Γ(C, U ⊓ V)) := φ.toRingHom.toAlgebra
    haveI : IsScalarTower L (L ⊗[R] Γ(C, U)) (L ⊗[R] Γ(C, U ⊓ V)) :=
      IsScalarTower.of_algebraMap_eq (fun r => (φ.commutes r).symm)
    have h := IsLocalization.tensorProduct_tensorProduct_right R L (Submonoid.powers f) Γ(C, U ⊓ V) (by
      ext a
      change φ ((1 : L) ⊗ₜ[R] a) = (1 : L) ⊗ₜ[R] (ρU a)
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply])
    rw [Submonoid.map_powers] at h
    exact h
  have hψ : letI := ψ.toRingHom.toAlgebra; IsLocalization.Away ((1 : L) ⊗ₜ[R] g) (L ⊗[R] Γ(C, U ⊓ V)) := by
    letI : Algebra Γ(C, V) Γ(C, U ⊓ V) := ρV.toRingHom.toAlgebra
    haveI : IsScalarTower R Γ(C, V) Γ(C, U ⊓ V) := IsScalarTower.of_algebraMap_eq (fun r => (ρV.commutes r).symm)
    haveI : IsLocalization (Submonoid.powers g) Γ(C, U ⊓ V) := hlocV
    letI : Algebra (L ⊗[R] Γ(C, V)) (L ⊗[R] Γ(C, U ⊓ V)) := ψ.toRingHom.toAlgebra
    haveI : IsScalarTower L (L ⊗[R] Γ(C, V)) (L ⊗[R] Γ(C, U ⊓ V)) :=
      IsScalarTower.of_algebraMap_eq (fun r => (ψ.commutes r).symm)
    have h := IsLocalization.tensorProduct_tensorProduct_right R L (Submonoid.powers g) Γ(C, U ⊓ V) (by
      ext a
      change ψ ((1 : L) ⊗ₜ[R] a) = (1 : L) ⊗ₜ[R] (ρV a)
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply])
    rw [Submonoid.map_powers] at h
    exact h

  have hab : φ ((1 : L) ⊗ₜ[R] f) * ψ ((1 : L) ⊗ₜ[R] g) = 1 := by
    change Algebra.TensorProduct.map (AlgHom.id L L) ρU ((1 : L) ⊗ₜ[R] f) *
      Algebra.TensorProduct.map (AlgHom.id L L) ρV ((1 : L) ⊗ₜ[R] g) = 1
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    change (1 : L) ⊗ₜ[R] ((C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g) = 1
    rw [hfg]
    rfl

  haveI hneW : Nontrivial (L ⊗[R] Γ(C, U ⊓ V)) := by
    letI : Algebra (L ⊗[R] Γ(C, U)) (L ⊗[R] Γ(C, U ⊓ V)) := φ.toRingHom.toAlgebra
    haveI : IsLocalization.Away ((1 : L) ⊗ₜ[R] f) (L ⊗[R] Γ(C, U ⊓ V)) := hφ
    have hinjO : Function.Injective (algebraMap (L ⊗[R] Γ(C, U)) (L ⊗[R] Γ(C, U ⊓ V))) :=
      IsLocalization.injective (M := Submonoid.powers ((1 : L) ⊗ₜ[R] f)) _
        (powers_le_nonZeroDivisors_of_noZeroDivisors hf0)
    exact hinjO.nontrivial
  haveI hneV : Nontrivial (L ⊗[R] Γ(C, V)) := ψ.toRingHom.domain_nontrivial
  haveI hEdom : IsDomain (L ⊗[R] Γ(C, V)) :=
    isDomain_tensorProduct_sections_of_geometricallyIntegral c V hV L hneV

  have hfinD := LevelSetGlobal.finite_aeval_tmul L f hfin
  have hfinE := LevelSetGlobal.finite_aeval_tmul L g hfinV

  have hglue := Algebra.finrank_quotient_span_sub_eq_of_isLocalization_away_of_mul_eq_one
    φ ψ ((1 : L) ⊗ₜ[R] f) ((1 : L) ⊗ₜ[R] g) hφ hψ hab hfinD hfinE hinj x
  have hx : ((1 : L) ⊗ₜ[R] f - x ⊗ₜ[R] (1 : Γ(C, U)) : L ⊗[R] Γ(C, U)) =
      (1 : L) ⊗ₜ[R] f - algebraMap L (L ⊗[R] Γ(C, U)) x := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  rw [hx, hglue, LevelSetGlobal.finrank_tensor_quotient_span_tmul L g]
  exact hrank L

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
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (m : ℕ)
    (hrank : ∀ (L : Type u) [Field L] [Algebra R L],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
      Module.finrank L (L ⊗[R] (Γ(C, V) ⧸ Ideal.span {g})) = m)
    (hfin : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U;
      (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Finite)
    (hfinV : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V;
      (Polynomial.aeval g : Polynomial R →ₐ[R] Γ(C, V)).toRingHom.Finite)
    (L : Type u) [Field L] [Algebra R L] (x : L) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Module.finrank L (L ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : L) ⊗ₜ[R] f - x ⊗ₜ[R] (1 : Γ(C, U))}) = m :=
  AlgebraicGeometry.SmoothProperCurve.finrank_levelSet_field_of_twoChartPoleDatum_of_forall_finrank R c ε U V hU hV hUV hUε f g hf hg hfg m hrank hfin hfinV L x

end S_AlgebraicGeometry_SmoothProperCurve_finrank_levelSet_field_of_twoChartPoleDatum_of_forall_finrank
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothProperCurve_finrank_levelSet_field_of_twoChartPoleDatum_of_forall_finrank (solution)
