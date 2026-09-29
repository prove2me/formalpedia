-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.finite_and_forall_finrank_baseChange_quotient_span_of_generates_ker_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/585810f0-d24e-52e3-ab52-1eea0d7e9a97

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_finite_and_forall_finrank_baseChange_quotient_span_of_generates_ker_pow
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"

set_option maxHeartbeats 800000

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (m : ℕ) (hm : 1 ≤ m)
    (V : C.Opens) (hV : IsAffineOpen V) (hεV : ∀ x ∈ Set.range ε.1.base, x ∈ V) (g : Γ(C, V))
    (hg : ∀ W : C.affineOpens, ∀ hW : (W : C.Opens) ≤ V,
      (ε.1.ker ^ m).ideal W = Ideal.span {(C.presheaf.map (homOfLE hW).op).hom g}) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
    Module.Finite R (Γ(C, V) ⧸ Ideal.span {g}) ∧
      ∀ (L : Type u) [Field L] [Algebra R L], Module.finrank L (L ⊗[R] (Γ(C, V) ⧸ Ideal.span {g})) = m := by
  classical
  letI algV := Scheme.TwoAffineOpenCover.algebraOfHom c V

  obtain ⟨hfin, hrk, hflat, -⟩ :=
    Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id (p := c) ε.1 ε.2 m
  set I : C.IdealSheafData := ε.1.ker ^ m with hI
  haveI : IsFinite (I.subschemeι ≫ c) := hfin
  haveI : Flat (I.subschemeι ≫ c) := hflat
  haveI : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ c)

  haveI : IsClosedImmersion ε.1 := by
    have : IsClosedImmersion (ε.1 ≫ c) := by rw [ε.2]; infer_instance
    exact .of_comp ε.1 c
  have hsupp : (I.support : Set C) = Set.range ε.1.base := by
    rw [hI, Scheme.IdealSheafData.support_pow _ _ (by omega), Scheme.Hom.support_ker,
      ε.1.isClosedEmbedding.isClosed_range.closure_eq]
  have hpre : I.subschemeι ⁻¹ᵁ V = ⊤ := by
    ext x
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe,
      TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    apply hεV
    rw [← hsupp, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨x, rfl⟩

  letI algZ := Scheme.TwoAffineOpenCover.algebraOfHom (I.subschemeι ≫ c) ⊤
  have happ : (I.subschemeι ≫ c).appLE ⊤ ⊤ le_top = (I.subschemeι ≫ c).appTop :=
    (Scheme.Hom.app_eq_appLE _).symm
  have hψ : (algebraMap R Γ(I.subscheme, ⊤)) =
      ((Scheme.ΓSpecIso (.of R)).inv ≫ (I.subschemeι ≫ c).appTop).hom := by
    rw [← happ]; rfl
  have hfinA : (algebraMap R Γ(I.subscheme, ⊤)).Finite := by
    rw [hψ, CommRingCat.hom_comp]
    exact (Scheme.Hom.finite_appTop _).comp
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).surjective)
  have hflatA : (algebraMap R Γ(I.subscheme, ⊤)).Flat := by
    rw [hψ, CommRingCat.hom_comp]
    have hiso : ((Scheme.ΓSpecIso (.of R)).inv.hom).Flat :=
      .of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv)
    exact hiso.comp (Scheme.Hom.flat_appTop _)
  haveI : Module.Finite R Γ(I.subscheme, ⊤) := RingHom.finite_algebraMap.mp hfinA
  haveI : Module.Flat R Γ(I.subscheme, ⊤) := RingHom.flat_algebraMap_iff.mp hflatA
  have hrank : ∀ t, Module.rankAtStalk (R := R) Γ(I.subscheme, ⊤) t = m := by
    intro t
    have hfac : I.subschemeι ≫ c = I.subscheme.toSpecΓ ≫
        Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ (I.subschemeι ≫ c).appTop) := by
      rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom,
        ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
    have h1 := hrk t
    haveI : IsFinite (Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ (I.subschemeι ≫ c).appTop)) :=
      (IsFinite.SpecMap_iff _).mpr (hψ ▸ hfinA)
    haveI : Flat (Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ (I.subschemeι ≫ c).appTop)) :=
      Flat.SpecMap_iff.mpr (hψ ▸ hflatA)
    rw [hfac, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_eq_finrank
      (hψ ▸ hfinA) (hψ ▸ hflatA), ← hψ, RingHom.finrank_algebraMap] at h1
    exact h1

  letI algW := Scheme.TwoAffineOpenCover.algebraOfHom (I.subschemeι ≫ c) (I.subschemeι ⁻¹ᵁ V)
  let φ : Γ(C, V) →ₐ[R] Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V) :=
    { (I.subschemeι.app V).hom with
      commutes' := fun r => by
        show (c.appLE ⊤ V le_top ≫ I.subschemeι.app V).hom _ =
          ((I.subschemeι ≫ c).appLE ⊤ (I.subschemeι ⁻¹ᵁ V) le_top).hom _
        rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE] }
  have hφsurj : Function.Surjective φ := I.subschemeι_app_surjective ⟨V, hV⟩
  have hφker : RingHom.ker φ.toRingHom = Ideal.span {g} := by
    show RingHom.ker (I.subschemeι.app V).hom = _
    rw [I.ker_subschemeι_app ⟨V, hV⟩, hI, hg ⟨V, hV⟩ le_rfl]
    simp
  let e₁ : (Γ(C, V) ⧸ Ideal.span {g}) ≃ₐ[R] Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V) :=
    (Ideal.quotientEquivAlgOfEq R hφker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hφsurj)
  let e₂ : Γ(I.subscheme, ⊤) ≃ₐ[R] Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V) :=
    { (I.subscheme.presheaf.mapIso (eqToIso hpre).op).commRingCatIsoToRingEquiv with
      commutes' := fun r => by
        show ((I.subschemeι ≫ c).appLE ⊤ ⊤ le_top ≫ I.subscheme.presheaf.map _).hom _ =
          ((I.subschemeι ≫ c).appLE ⊤ (I.subschemeι ⁻¹ᵁ V) le_top).hom _
        rw [Scheme.Hom.appLE_map] }
  have e : (Γ(C, V) ⧸ Ideal.span {g}) ≃ₗ[R] Γ(I.subscheme, ⊤) := (e₁.trans e₂.symm).toLinearEquiv
  refine ⟨Module.Finite.equiv e.symm, fun L _ _ => ?_⟩
  rw [LinearEquiv.finrank_eq (e.baseChange R L _ _)]
  have h := Module.rankAtStalk_baseChange (R := R) (M := Γ(I.subscheme, ⊤)) (S := L) (IsLocalRing.closedPoint L)
  rw [Module.rankAtStalk_eq_finrank_of_free, hrank] at h
  simpa using h

end S_AlgebraicGeometry_SmoothProperCurve_finite_and_forall_finrank_baseChange_quotient_span_of_generates_ker_pow
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothProperCurve_finite_and_forall_finrank_baseChange_quotient_span_of_generates_ker_pow (solution)
