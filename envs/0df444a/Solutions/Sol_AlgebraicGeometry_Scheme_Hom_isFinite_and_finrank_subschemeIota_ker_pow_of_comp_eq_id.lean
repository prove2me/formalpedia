-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/d6570157-93a2-5209-bfc6-28d0664eea5f

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso Scheme.Hom.finrank_comp_left_of_isIso SmoothOfRelativeDimension Scheme.IdealSheafData.one_eq_top IsClosedImmersion.of_comp Scheme.Hom Scheme.IdealSheafData.comapIso Scheme.IdealSheafData.comapIso_hom_fst_assoc IsFinite Scheme Scheme.IdealSheafData.comap_top Scheme.IdealSheafData.ker_fst_of_isClosedImmersion Flat IsClosedImmersion IsSeparated LocallyOfFinitePresentation Scheme.IdealSheafData graphOver graphOver_fst RelEffCartierDiv RelEffCartierDiv.exists_I_eq_prodKerGraph Scheme.IdealSheafData.comap_mul"
namespace SectionPowDivisor
p2m_open "AlgebraicGeometry"

variable {X T : Scheme.{u}}

lemma comap_pow {Y : Scheme.{u}} (J : Y.IdealSheafData) (f : X ⟶ Y) (n : ℕ) :
    (J ^ n).comap f = J.comap f ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.comap_top]
  | succ n ih => rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

lemma ker_graphOver_eq_comap {p : X ⟶ T} [IsSeparated p] (σ : T ⟶ X) (hσ : σ ≫ p = 𝟙 T) :
    (graphOver p σ hσ).ker = σ.ker.comap (pullback.fst p (𝟙 T)) := by
  haveI : IsClosedImmersion (σ ≫ p) := by rw [hσ]; infer_instance
  haveI : IsClosedImmersion σ := IsClosedImmersion.of_comp σ p
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have h : pullback.fst (pullback.fst p (𝟙 T)) σ =
      pullback.snd (pullback.fst p (𝟙 T)) σ ≫ graphOver p σ hσ := by
    rw [← cancel_mono (pullback.fst p (𝟙 T)), Category.assoc, graphOver_fst]
    exact pullback.condition
  rw [h, Scheme.Hom.ker_comp_of_isIso]

lemma transport {P : Scheme.{u}} (e : P ⟶ X) [IsIso e] (p : X ⟶ T) (J : X.IdealSheafData) (r : ℕ)
    (hfin : IsFinite ((J.comap e).subschemeι ≫ e ≫ p))
    (hflat : Flat ((J.comap e).subschemeι ≫ e ≫ p))
    (hlfp : LocallyOfFinitePresentation ((J.comap e).subschemeι ≫ e ≫ p))
    (hrk : ∀ t : T, ((J.comap e).subschemeι ≫ e ≫ p).finrank t = r) :
    IsFinite (J.subschemeι ≫ p) ∧ (∀ t : T, (J.subschemeι ≫ p).finrank t = r) ∧
      Flat (J.subschemeι ≫ p) ∧ LocallyOfFinitePresentation (J.subschemeι ≫ p) := by
  obtain ⟨φ, hφiso, hφ⟩ : ∃ φ : (J.comap e).subscheme ⟶ J.subscheme,
      IsIso φ ∧ φ ≫ J.subschemeι ≫ p = (J.comap e).subschemeι ≫ e ≫ p :=
    ⟨(J.comapIso e).hom ≫ pullback.snd e J.subschemeι, inferInstance, by
      rw [Category.assoc, ← pullback.condition_assoc,
        Scheme.IdealSheafData.comapIso_hom_fst_assoc]⟩
  haveI := hφiso
  rw [← hφ] at hfin hflat hlfp hrk
  have h1 : IsFinite (J.subschemeι ≫ p) :=
    (MorphismProperty.cancel_left_of_respectsIso @IsFinite φ _).mp hfin
  have h3 : Flat (J.subschemeι ≫ p) :=
    (MorphismProperty.cancel_left_of_respectsIso @Flat φ _).mp hflat
  have h4 : LocallyOfFinitePresentation (J.subschemeι ≫ p) :=
    (MorphismProperty.cancel_left_of_respectsIso @LocallyOfFinitePresentation φ _).mp hlfp
  refine ⟨h1, fun t => ?_, h3, h4⟩
  rw [← Scheme.Hom.finrank_comp_left_of_isIso φ (J.subschemeι ≫ p)]
  exact hrk t

theorem main {p : X ⟶ T} [IsSeparated p] [SmoothOfRelativeDimension 1 p]
    (σ : T ⟶ X) (hσ : σ ≫ p = 𝟙 T) (r : ℕ) :
    IsFinite ((σ.ker ^ r).subschemeι ≫ p) ∧
      (∀ t : T, ((σ.ker ^ r).subschemeι ≫ p).finrank t = r) ∧
      Flat ((σ.ker ^ r).subschemeι ≫ p) ∧
      LocallyOfFinitePresentation ((σ.ker ^ r).subschemeι ≫ p) := by
  obtain ⟨⟨I, hfin, hflat, hlfp, hrk⟩, hI⟩ :=
    RelEffCartierDiv.exists_I_eq_prodKerGraph (f := p) (g := 𝟙 T) (fun _ : Fin r => σ) (fun _ => hσ)
  have hI' : I = (σ.ker ^ r).comap (pullback.fst p (𝟙 T)) := by
    rw [comap_pow, ← ker_graphOver_eq_comap σ hσ, ← Fin.prod_const]
    exact hI
  subst hI'
  have hsnd : pullback.fst p (𝟙 T) ≫ p = pullback.snd p (𝟙 T) := by
    rw [pullback.condition, Category.comp_id]
  rw [← hsnd] at hfin hflat hlfp hrk
  exact transport (pullback.fst p (𝟙 T)) p (σ.ker ^ r) r hfin hflat hlfp hrk

end AlgebraicGeometry.SectionPowDivisor

theorem solution
    {X T : Scheme.{u}} {p : X ⟶ T} [IsSeparated p] [SmoothOfRelativeDimension 1 p]
    (σ : T ⟶ X) (hσ : σ ≫ p = 𝟙 T) (r : ℕ) :
    IsFinite ((σ.ker ^ r).subschemeι ≫ p) ∧
      (∀ t : T, ((σ.ker ^ r).subschemeι ≫ p).finrank t = r) ∧
      Flat ((σ.ker ^ r).subschemeι ≫ p) ∧
      LocallyOfFinitePresentation ((σ.ker ^ r).subschemeι ≫ p) :=
  AlgebraicGeometry.SectionPowDivisor.main σ hσ r

end S_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id (solution)
