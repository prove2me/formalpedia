-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.finrank_levelSet_field_of_twoChartPoleDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/dbe6e5cc-27ad-5831-ac2a-781c408a7c6c

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Theorems.Thm_Algebra_finrank_quotient_span_sub_eq_of_isLocalization_away_of_mul_eq_one
import Theorems.Thm_AlgebraicGeometry_isDomain_tensorProduct_sections_of_geometricallyIntegral
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_injective_aeval_tensor_of_twoChartPoleDatum
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_nontrivial_tensor_sections_of_twoChartPoleDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_finrank_levelSet_field_of_twoChartPoleDatum

set_option autoImplicit false

universe u

open scoped TensorProduct
open Polynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace U3bRANK

theorem finite_aeval_baseChange {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A] (f : A)
    (hfin : (Polynomial.aeval f : R[X] →ₐ[R] A).toRingHom.Finite)
    (L : Type u) [CommRing L] [Algebra R L] :
    (Polynomial.aeval ((1 : L) ⊗ₜ[R] f) : L[X] →ₐ[L] L ⊗[R] A).toRingHom.Finite := by
  classical
  letI algRA : Algebra R[X] A := (Polynomial.aeval f : R[X] →ₐ[R] A).toRingHom.toAlgebra
  haveI : Module.Finite R[X] A := hfin
  letI algLD : Algebra L[X] (L ⊗[R] A) :=
    (Polynomial.aeval ((1 : L) ⊗ₜ[R] f) : L[X] →ₐ[L] L ⊗[R] A).toRingHom.toAlgebra
  show Module.Finite L[X] (L ⊗[R] A)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R[X]) (M := A)
  refine ⟨⟨s.image (fun a => (1 : L) ⊗ₜ[R] a), ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]

  have key : ∀ (l : L) (a : A), l ⊗ₜ[R] a ∈
      Submodule.span L[X] ((fun a => (1 : L) ⊗ₜ[R] a) '' (s : Set A)) := by
    intro l a
    have ha : a ∈ Submodule.span R[X] (s : Set A) := by rw [hs]; trivial
    induction ha using Submodule.span_induction with
    | mem y hy =>
      have : l ⊗ₜ[R] y = (Polynomial.C l : L[X]) • ((1 : L) ⊗ₜ[R] y) := by
        show _ = (Polynomial.aeval ((1 : L) ⊗ₜ[R] f) (Polynomial.C l)) * _
        rw [Polynomial.aeval_C, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
          one_mul]
        simp
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩)
    | zero => simp
    | add y z _ _ hy hz => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hy hz
    | smul p y _ hy =>

      have : l ⊗ₜ[R] (p • y) = (p.map (algebraMap R L) : L[X]) • (l ⊗ₜ[R] y) := by
        show l ⊗ₜ[R] ((Polynomial.aeval f p) * y) = (Polynomial.aeval ((1 : L) ⊗ₜ[R] f) (p.map (algebraMap R L))) * _
        rw [Polynomial.aeval_map_algebraMap,
          show (Polynomial.aeval ((1 : L) ⊗ₜ[R] f) p : L ⊗[R] A) = (1 : L) ⊗ₜ[R] (Polynomial.aeval f p) from ?_,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        rw [show ((1 : L) ⊗ₜ[R] f : L ⊗[R] A) = Algebra.TensorProduct.includeRight f from rfl,
          Polynomial.aeval_algHom_apply]
        rfl
      rw [this]
      exact Submodule.smul_mem _ _ hy
  rintro z -
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul l a => exact key l a
  | add z w hz hw => exact Submodule.add_mem _ hz hw

section Overlap

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))

theorem isLocalization_away_of_eq_basicOpen {U W : C.Opens} (hU : IsAffineOpen U) (f : Γ(C, U))
    (hW : W ≤ U) (h : W = C.basicOpen f) :
    letI := (C.presheaf.map (homOfLE hW).op).hom.toAlgebra
    IsLocalization.Away f Γ(C, W) := by
  subst h
  exact hU.isLocalization_basicOpen f

variable (L : Type u) [CommRing L] [Algebra R L]

theorem isLocalization_away_baseChange {U W : C.Opens} (hU : IsAffineOpen U) (f : Γ(C, U))
    (hW : W ≤ U) (h : W = C.basicOpen f) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c W
    letI := (Algebra.TensorProduct.map (AlgHom.id L L)
      (Scheme.TwoAffineOpenCover.restrictAlgHom c hW)).toRingHom.toAlgebra
    IsLocalization.Away ((1 : L) ⊗ₜ[R] f) (L ⊗[R] Γ(C, W)) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c W
  letI algUW : Algebra Γ(C, U) Γ(C, W) := (C.presheaf.map (homOfLE hW).op).hom.toAlgebra
  haveI : IsScalarTower R Γ(C, U) Γ(C, W) := IsScalarTower.of_algebraMap_eq fun r =>
    ((Scheme.TwoAffineOpenCover.restrictAlgHom c hW).commutes r).symm
  haveI : IsLocalization.Away f Γ(C, W) := isLocalization_away_of_eq_basicOpen hU f hW h
  have hρ : Scheme.TwoAffineOpenCover.restrictAlgHom c hW = IsScalarTower.toAlgHom R Γ(C, U) Γ(C, W) := by
    ext x; rfl
  letI alg : Algebra (L ⊗[R] Γ(C, U)) (L ⊗[R] Γ(C, W)) :=
    (Algebra.TensorProduct.map (AlgHom.id L L)
      (Scheme.TwoAffineOpenCover.restrictAlgHom c hW)).toRingHom.toAlgebra
  have H : (algebraMap (L ⊗[R] (C.presheaf.obj (Opposite.op U))) (L ⊗[R] (C.presheaf.obj (Opposite.op W)))).comp
        Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom.comp
        (algebraMap (C.presheaf.obj (Opposite.op U)) (C.presheaf.obj (Opposite.op W))) := by
    ext t
    show (Algebra.TensorProduct.map (AlgHom.id L L) (Scheme.TwoAffineOpenCover.restrictAlgHom c hW))
      ((1 : L) ⊗ₜ[R] t) = (1 : L) ⊗ₜ[R] (algebraMap (C.presheaf.obj (Opposite.op U)) (C.presheaf.obj (Opposite.op W)) t)
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  have hloc := IsLocalization.tensorProduct_tensorProduct_right R L (Submonoid.powers f)
    (C.presheaf.obj (Opposite.op W)) H
  rw [Submonoid.map_powers] at hloc
  exact hloc

end Overlap

end U3bRANK

namespace U3bRANK

theorem finrank_quotient_tmul {R : Type u} [CommRing R] [Nontrivial R] {B : Type u} [CommRing B] [Algebra R B] (g : B)
    (L : Type u) [Field L] [Algebra R L] [Module.Free R (B ⧸ Ideal.span {g})] :
    Module.finrank L (L ⊗[R] B ⧸ Ideal.span {(1 : L) ⊗ₜ[R] g}) = Module.finrank R (B ⧸ Ideal.span {g}) := by
  let q : B →ₐ[R] B ⧸ Ideal.span {g} := Ideal.Quotient.mkₐ R (Ideal.span {g})
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  let θ : L ⊗[R] B →ₐ[L] L ⊗[R] (B ⧸ Ideal.span {g}) := Algebra.TensorProduct.map (AlgHom.id L L) q
  have hθ : Function.Surjective θ := by
    have : ⇑θ = ⇑(LinearMap.lTensor L q.toLinearMap) := by
      ext z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul l b => simp [θ, Algebra.TensorProduct.map_tmul]
      | add z w hz hw => simp only [map_add, hz, hw]
    rw [this]
    exact LinearMap.lTensor_surjective L hq
  have hker : RingHom.ker θ.toRingHom = Ideal.span {(1 : L) ⊗ₜ[R] g} := by
    have h1 : RingHom.ker θ.toRingHom = RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R L) q) := by
      ext z
      simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      try rfl
    rw [h1, Algebra.TensorProduct.lTensor_ker q hq]
    have hkq : RingHom.ker q = Ideal.span {g} := Ideal.mk_ker
    rw [hkq, Ideal.map_span, Set.image_singleton]
    rfl
  have e₁ := Ideal.quotientKerAlgEquivOfSurjective hθ
  have e₂ := Ideal.quotientEquivAlgOfEq L hker
  rw [← e₂.toLinearEquiv.finrank_eq]
  exact e₁.toLinearEquiv.finrank_eq.trans Module.finrank_baseChange

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
    (m : ℕ)
    (hfree : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V;
      Module.Free R (Γ(C, V) ⧸ Ideal.span {g}))
    (hrank : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V;
      Module.finrank R (Γ(C, V) ⧸ Ideal.span {g}) = m)
    (hfin : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U;
      (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Finite)
    (hfinV : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V;
      (Polynomial.aeval g : Polynomial R →ₐ[R] Γ(C, V)).toRingHom.Finite)
    (L : Type u) [Field L] [Algebra R L] (x : L) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Module.finrank L (L ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : L) ⊗ₜ[R] f - x ⊗ₜ[R] (1 : Γ(C, U))}) = m := by
  letI aU := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI aV := Scheme.TwoAffineOpenCover.algebraOfHom c V
  letI aW := Scheme.TwoAffineOpenCover.algebraOfHom c (U ⊓ V)

  let ρU := Scheme.TwoAffineOpenCover.restrictAlgHom c (inf_le_left : U ⊓ V ≤ U)
  let ρV := Scheme.TwoAffineOpenCover.restrictAlgHom c (inf_le_right : U ⊓ V ≤ V)
  let φ := Algebra.TensorProduct.map (AlgHom.id L L) ρU
  let ψ := Algebra.TensorProduct.map (AlgHom.id L L) ρV
  have hφ := isLocalization_away_baseChange c L hU f (inf_le_left : U ⊓ V ≤ U) hf
  have hψ := isLocalization_away_baseChange c L hV g (inf_le_right : U ⊓ V ≤ V) hg
  have hab : φ ((1 : L) ⊗ₜ[R] f) * ψ ((1 : L) ⊗ₜ[R] g) = 1 := by
    show (Algebra.TensorProduct.map (AlgHom.id L L) ρU) ((1 : L) ⊗ₜ[R] f) *
      (Algebra.TensorProduct.map (AlgHom.id L L) ρV) ((1 : L) ⊗ₜ[R] g) = 1
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    show ((AlgHom.id L L) 1 * (AlgHom.id L L) 1) ⊗ₜ[R] ((C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g) = 1
    rw [hfg, map_one, one_mul]
    rfl

  haveI hneU := AlgebraicGeometry.SmoothProperCurve.nontrivial_tensor_sections_of_twoChartPoleDatum
    R c ε U V hU hV hUV hUε f g hf hg hfg L
  haveI : IsDomain (L ⊗[R] Γ(C, U)) :=
    AlgebraicGeometry.isDomain_tensorProduct_sections_of_geometricallyIntegral c U hU L hneU
  have hinj := AlgebraicGeometry.SmoothProperCurve.injective_aeval_tensor_of_twoChartPoleDatum
    R c ε U V hU hV hUV hUε f g hf hg hfg L hneU
  have ha0 : ((1 : L) ⊗ₜ[R] f : L ⊗[R] Γ(C, U)) ≠ 0 := by
    intro h
    have : (Polynomial.aeval ((1 : L) ⊗ₜ[R] f) : L[X] →ₐ[L] L ⊗[R] Γ(C, U)) X =
        (Polynomial.aeval ((1 : L) ⊗ₜ[R] f) : L[X] →ₐ[L] L ⊗[R] Γ(C, U)) 0 := by
      rw [Polynomial.aeval_X, map_zero, h]
    exact Polynomial.X_ne_zero (hinj this)
  have hφinj : Function.Injective φ := by
    letI := φ.toRingHom.toAlgebra
    exact IsLocalization.injective (M := Submonoid.powers ((1 : L) ⊗ₜ[R] f)) _
      (powers_le_nonZeroDivisors_of_noZeroDivisors ha0)
  haveI : Nontrivial (L ⊗[R] Γ(C, U ⊓ V)) := hφinj.nontrivial
  haveI hneV : Nontrivial (L ⊗[R] Γ(C, V)) := ψ.toRingHom.domain_nontrivial
  haveI : IsDomain (L ⊗[R] Γ(C, V)) :=
    AlgebraicGeometry.isDomain_tensorProduct_sections_of_geometricallyIntegral c V hV L hneV

  have hfinD := finite_aeval_baseChange f hfin L
  have hfinE := finite_aeval_baseChange g hfinV L

  have key := Algebra.finrank_quotient_span_sub_eq_of_isLocalization_away_of_mul_eq_one
    φ ψ ((1 : L) ⊗ₜ[R] f) ((1 : L) ⊗ₜ[R] g) hφ hψ hab hfinD hfinE hinj x
  have hx : (algebraMap L (L ⊗[R] Γ(C, U)) x) = x ⊗ₜ[R] (1 : Γ(C, U)) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [hx] at key
  rw [key, finrank_quotient_tmul g L, hrank]

end U3bRANK

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
    (m : ℕ)
    (hfree : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V;
      Module.Free R (Γ(C, V) ⧸ Ideal.span {g}))
    (hrank : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V;
      Module.finrank R (Γ(C, V) ⧸ Ideal.span {g}) = m)
    (hfin : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U;
      (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Finite)
    (hfinV : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V;
      (Polynomial.aeval g : Polynomial R →ₐ[R] Γ(C, V)).toRingHom.Finite)
    (L : Type u) [Field L] [Algebra R L] (x : L) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Module.finrank L (L ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : L) ⊗ₜ[R] f - x ⊗ₜ[R] (1 : Γ(C, U))}) = m :=
  U3bRANK.main R c ε U V hU hV hUV hUε f g hf hg hfg m hfree hrank hfin hfinV L x

end S_AlgebraicGeometry_SmoothProperCurve_finrank_levelSet_field_of_twoChartPoleDatum
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothProperCurve_finrank_levelSet_field_of_twoChartPoleDatum (solution)
