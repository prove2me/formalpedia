-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a1f19f5d-60b0-5382-b32b-cf4d5a1b8cab

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isOpenImmersion
import Theorems.Thm_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_DescentAction
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible

set_option autoImplicit false

universe u

p2m_open "CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian"

noncomputable section

namespace CategoryTheory
p2m_export "CategoryTheory" "Category Iso.inv_hom_id_assoc eqToIso IsIso.hom_inv_id Category.comp_id IsPullback.of_horiz_isIso MorphismProperty types_comp_apply Quotient NatIso.ofComponents Injective Functor inv over IsIso.inv_comp_eq Over.map Functor.map_comp Iso.trans_inv Over.homMk IsIso uliftYonedaEquiv_naturality Iso.hom_inv_id Iso.refl Category.id_comp Over Iso.trans_hom comp_apply Over.mk MonoidalCategory Over.w sum IsPullback cancel_mono Functor.RepresentableBy uliftYonedaEquiv Iso IsIso.inv_hom_id Functor.map_preimage uliftYoneda asIso Category.assoc op_comp Quotient.mk MorphismProperty.presheafULift"
namespace Functor
p2m_export "CategoryTheory.Functor" "kernel ext preimage representableBy map_id map sum closed map_injective empty map_comp mapIso hom sections obj inv of comp RepresentableBy map_preimage mk OverTotal map_op_apply_eq_self OverTotal.ext' overTotal OverTotal.toFibre"
namespace RepresentableBy
p2m_export "CategoryTheory.Functor.RepresentableBy" "mk homEquiv homEquiv_comp ext ofIso toIso"
p2m_open "CategoryTheory.Functor.RepresentableBy CategoryTheory.Functor CategoryTheory"

p2m_open "CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory CategoryTheory.Category Opposite"

universe w v u₀

variable {C : Type u₀} [Category.{v} C] {S : C} {G : (Over S)ᵒᵖ ⥤ Type (max w v)} {Y : C} {p : Y ⟶ S}
  (e : G.RepresentableBy (Over.mk p))

private def _root_.CategoryTheory.Functor.RepresentableBy.toOverTotalFun {T : C} (k : T ⟶ Y) : G.OverTotal T :=
  ⟨k ≫ p, e.homEquiv (Over.homMk k rfl : Over.mk (k ≫ p) ⟶ Over.mk p)⟩

p2m_export "CategoryTheory.Functor.RepresentableBy" "toOverTotalFun"
@[scoped simp] lemma toOverTotalFun_fst {T : C} (k : T ⟶ Y) : (e.toOverTotalFun k).1 = k ≫ p := rfl

private lemma _root_.CategoryTheory.Functor.RepresentableBy.toOverTotalFun_comp {T T' : C} (φ : T' ⟶ T) (k : T ⟶ Y) :
    e.toOverTotalFun (φ ≫ k) = G.overTotal.map φ.op (e.toOverTotalFun k) := by
  refine OverTotal.ext' (by simp) ?_
  change G.map _ (e.homEquiv _) = G.map _ (e.homEquiv _)
  erw [← e.homEquiv_comp, ← e.homEquiv_comp]
  congr 1
  ext
  simp

p2m_export "CategoryTheory.Functor.RepresentableBy" "toOverTotalFun_comp"

private noncomputable def _root_.CategoryTheory.Functor.RepresentableBy.ofOverTotalFun {T : C} (b : G.OverTotal T) : T ⟶ Y :=
  (e.homEquiv.symm (OverTotal.toFibre (Over.mk b.1) b rfl)).left

p2m_export "CategoryTheory.Functor.RepresentableBy" "ofOverTotalFun"
lemma toFibre_mk_eq {T : C} (b : G.OverTotal T) : OverTotal.toFibre (Over.mk b.1) b rfl = b.2 :=
  map_op_apply_eq_self _ (by simp) b.2

private lemma _root_.CategoryTheory.Functor.RepresentableBy.ofOverTotalFun_comp {T : C} (b : G.OverTotal T) : e.ofOverTotalFun b ≫ p = b.1 :=
  Over.w (e.homEquiv.symm (OverTotal.toFibre (Over.mk b.1) b rfl))

p2m_export "CategoryTheory.Functor.RepresentableBy" "ofOverTotalFun_comp"
private lemma _root_.CategoryTheory.Functor.RepresentableBy.ofOverTotalFun_toOverTotalFun {T : C} (k : T ⟶ Y) : e.ofOverTotalFun (e.toOverTotalFun k) = k := by
  unfold ofOverTotalFun
  rw [toFibre_mk_eq]
  change (e.homEquiv.symm (e.homEquiv (Over.homMk k rfl : Over.mk (k ≫ p) ⟶ Over.mk p))).left = k
  rw [Equiv.symm_apply_apply]
  rfl

p2m_export "CategoryTheory.Functor.RepresentableBy" "ofOverTotalFun_toOverTotalFun"
private lemma _root_.CategoryTheory.Functor.RepresentableBy.toOverTotalFun_ofOverTotalFun {T : C} (b : G.OverTotal T) : e.toOverTotalFun (e.ofOverTotalFun b) = b := by
  refine OverTotal.ext' (e.ofOverTotalFun_comp b) ?_
  change G.map _ (e.homEquiv _) = b.2
  rw [← e.homEquiv_comp]
  have key : (Over.homMk (𝟙 T) (show 𝟙 T ≫ (e.ofOverTotalFun b ≫ p) = b.1 by rw [Category.id_comp]; exact e.ofOverTotalFun_comp b) :
        Over.mk b.1 ⟶ Over.mk (e.ofOverTotalFun b ≫ p)) ≫
      (Over.homMk (e.ofOverTotalFun b) rfl : Over.mk (e.ofOverTotalFun b ≫ p) ⟶ Over.mk p) =
      e.homEquiv.symm (OverTotal.toFibre (Over.mk b.1) b rfl) := by
    ext
    change 𝟙 T ≫ e.ofOverTotalFun b = _
    rw [Category.id_comp]
    rfl
  erw [key, Equiv.apply_symm_apply, toFibre_mk_eq]

p2m_export "CategoryTheory.Functor.RepresentableBy" "toOverTotalFun_ofOverTotalFun"

private noncomputable def _root_.CategoryTheory.Functor.RepresentableBy.toOverTotalIso : uliftYoneda.{max w v}.obj Y ≅ G.overTotal :=
  NatIso.ofComponents
    (fun T => Equiv.toIso
      { toFun := fun k => e.toOverTotalFun k.down
        invFun := fun b => ULift.up (e.ofOverTotalFun b)
        left_inv := fun k => by
          apply ULift.ext
          exact e.ofOverTotalFun_toOverTotalFun k.down
        right_inv := fun b => e.toOverTotalFun_ofOverTotalFun b })
    (fun {T T'} φ => by
      ext k
      exact e.toOverTotalFun_comp φ.unop k.down)

p2m_export "CategoryTheory.Functor.RepresentableBy" "toOverTotalIso"
@[scoped simp] lemma toOverTotalIso_hom_app_apply {T : C} (k : ULift.{max w v} (T ⟶ Y)) :
    e.toOverTotalIso.hom.app (op T) k = e.toOverTotalFun k.down := rfl

lemma uliftYonedaEquiv_toOverTotalIso_hom :
    uliftYonedaEquiv.{max w v} e.toOverTotalIso.hom = e.toOverTotalFun (𝟙 Y) := rfl

lemma uliftYoneda_map_comp_toOverTotalIso_hom {T : C} (k : T ⟶ Y) :
    uliftYonedaEquiv.{max w v} (uliftYoneda.{max w v}.map k ≫ e.toOverTotalIso.hom) = e.toOverTotalFun k := by
  have h := uliftYonedaEquiv_naturality e.toOverTotalIso.hom k.op
  rw [Quiver.Hom.unop_op] at h
  rw [← h, uliftYonedaEquiv_toOverTotalIso_hom, ← toOverTotalFun_comp, comp_id]

lemma toOverTotalFun_id : e.toOverTotalFun (𝟙 Y) = ⟨p, e.homEquiv (𝟙 (Over.mk p))⟩ := by
  refine OverTotal.ext' (by simp) ?_
  change G.map _ (e.homEquiv _) = e.homEquiv _
  erw [← e.homEquiv_comp]
  congr 1
  ext
  simp

lemma uliftYonedaEquiv_symm_eq_toOverTotalIso_hom :
    (uliftYonedaEquiv.{max w v} (X := Y) (F := G.overTotal)).symm ⟨p, e.homEquiv (𝟙 (Over.mk p))⟩ = e.toOverTotalIso.hom := by
  apply uliftYonedaEquiv.injective
  rw [Equiv.apply_symm_apply, uliftYonedaEquiv_toOverTotalIso_hom, toOverTotalFun_id]

scoped instance isIso_uliftYonedaEquiv_symm :
    IsIso ((uliftYonedaEquiv.{max w v} (X := Y) (F := G.overTotal)).symm ⟨p, e.homEquiv (𝟙 (Over.mk p))⟩) := by
  rw [uliftYonedaEquiv_symm_eq_toOverTotalIso_hom]; infer_instance

end CategoryTheory.Functor.RepresentableBy
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor.RepresentableBy"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory"

p2m_open "CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian"

section S0sec
open TensorProduct
namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.ker_comp_of_isIso Spec.map_preimage Scheme.Hom.fiberι_fiberHomeo_symm Scheme.IdealSheafData.ideal_mul pullbackSpecIso_inv_fst' Scheme.IdealSheafData.comap_comp Scheme.Modules.pullback Scheme.Hom Scheme.range_fromSpecResidueField Scheme.homeoOfIso LocallyOfFiniteType Spec Spec.map Scheme pullbackSpecIso Scheme.IdealSheafData.comap_top IsOpenImmersion Scheme.IdealSheafData.ker_fst_of_isClosedImmersion Spec.map_injective IsClosedImmersion IsSeparated Spec.preimage Scheme.Modules.pullbackCongr Etale Scheme.Modules.pullbackId IsAffineOpen Scheme.Modules Scheme.IdealSheafData.ext Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion Scheme.Modules.IsInvertible Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso RelEffCartierDiv mapOnProdOver Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison prodKerGraph_comap_mapOnProdOver prodKerGraph prodKerGraph_eq_prod graphOver graphOver_fst graphOver_snd Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover SmoothProperCurve.specMap SmoothProperCurve.baseChange SmoothProperCurve.sectionBaseChange RelPicard.BaseChange.κ RelPicard.BaseChange.overR RelPicard.BaseChange.toR RelPicard.BaseChange.toR_pullbackAlong_iso RelPicard.BaseChange.restrict RelPicard.BaseChange.restrict_algEquivZeroCut RelPicard.BaseChange.classesEquiv RelPicard.BaseChange.relSubPicPresheafRestrictIso RelPicard.BaseChange.relSubPicPresheafAlgEquivZeroCutIso RelPicard.BaseChange.representableByRestrict DescentAction DescentAction.univ DescentAction.map_repActOver_univ DescentAction.ofRepresentableBy DescentAction.act_comp DescentAction.act" end AlgebraicGeometry
p2m_open_scoped "AlgebraicGeometry" in
set_option synthInstance.maxHeartbeats 480000 in
set_option maxHeartbeats 1600000 in
theorem AlgebraicGeometry.finite_preimage_fst_singleton_and_exists_geometric_lifts
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] [Module.Finite R R']
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of R)) (x : P) :
    ((pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R R')))).base ⁻¹' {x}).Finite ∧
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (xb : Spec (CommRingCat.of Ω) ⟶ P),
      Set.range xb.base = {x} ∧
      ∀ r : ↥(pullback q (Spec.map (CommRingCat.ofHom (algebraMap R R')))),
        (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R R')))).base r = x →
        ∃ rb : Spec (CommRingCat.of Ω) ⟶ pullback q (Spec.map (CommRingCat.ofHom (algebraMap R R'))),
          r ∈ Set.range rb.base ∧ rb ≫ pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = xb := by
  classical
  let κ := P.residueField x
  letI : Algebra R κ := (Spec.preimage (P.fromSpecResidueField x ≫ q)).hom.toAlgebra
  have hι : Spec.map (CommRingCat.ofHom (algebraMap R κ)) = P.fromSpecResidueField x ≫ q := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]

  let A := κ ⊗[R] R'
  let F : (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R R')))).fiber x ≅ Spec (CommRingCat.of A) :=
    (pullbackSymmetry (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (P.fromSpecResidueField x)) ≪≫
      pullbackRightPullbackFstIso q (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (P.fromSpecResidueField x) ≪≫
      pullback.congrHom hι.symm rfl ≪≫ pullbackSpecIso R κ R'
  have hFsnd : F.inv ≫ (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R R')))).fiberToSpecResidueField x =
      Spec.map (CommRingCat.ofHom (algebraMap κ A)) := by
    show F.inv ≫ pullback.snd (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (P.fromSpecResidueField x) = _
    simp only [F, Iso.trans_inv, Category.assoc]
    erw [pullbackSymmetry_inv_comp_snd]
    erw [pullbackRightPullbackFstIso_inv_fst]
    rw [pullback.congrHom_inv]
    erw [pullback.lift_fst]
    rw [Category.comp_id]
    exact pullbackSpecIso_inv_fst' R κ R'

  haveI : Module.Finite κ A := inferInstance
  haveI : IsArtinianRing A := isArtinian_of_tower κ (inferInstance : IsArtinian κ A)
  have e : ↥((pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R R')))).base ⁻¹' {x}) ≃ PrimeSpectrum A :=
    ((pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R R')))).fiberHomeo x).symm.toEquiv.trans
      (Scheme.homeoOfIso F).toEquiv
  refine ⟨Set.finite_coe_iff.mp (Finite.of_equiv _ e.symm), ?_⟩

  let Ω := AlgebraicClosure κ
  let xb : Spec (CommRingCat.of Ω) ⟶ P := Spec.map (CommRingCat.ofHom (algebraMap κ Ω)) ≫ P.fromSpecResidueField x
  have hsub : Set.range xb.base ⊆ {x} := by
    rintro _ ⟨p, hp⟩
    rw [← hp, ← Scheme.range_fromSpecResidueField x]
    exact Set.mem_range_self ((Spec.map (CommRingCat.ofHom (algebraMap κ Ω))).base p)
  have hxb : Set.range xb.base = {x} := by
    apply Set.Subset.antisymm hsub
    obtain ⟨p⟩ : Nonempty (PrimeSpectrum Ω) := ⟨⊥⟩
    have hp : xb.base p ∈ ({x} : Set P) := hsub ⟨p, rfl⟩
    rw [Set.mem_singleton_iff] at hp
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact ⟨p, hp⟩
  refine ⟨Ω, inferInstance, inferInstance, xb, hxb, fun r hr => ?_⟩

  let y : (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R R')))).fiber x :=
    ((pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R R')))).fiberHomeo x).symm ⟨r, hr⟩
  have hy : ((pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R R')))).fiberι x).base y = r :=
    Scheme.Hom.fiberι_fiberHomeo_symm _ x ⟨r, hr⟩
  let 𝔮 : PrimeSpectrum A := F.hom.base y
  have hmax : 𝔮.asIdeal.IsMaximal := IsArtinianRing.isMaximal_of_isPrime 𝔮.asIdeal
  haveI : Algebra.IsAlgebraic κ (A ⧸ 𝔮.asIdeal) := Algebra.IsAlgebraic.of_finite κ _
  let φ : (A ⧸ 𝔮.asIdeal) →ₐ[κ] Ω := IsAlgClosed.lift (R := κ) (S := A ⧸ 𝔮.asIdeal) (M := Ω)
  let g : A →+* Ω := φ.toRingHom.comp (Ideal.Quotient.mk 𝔮.asIdeal)
  have hgker : RingHom.ker g = 𝔮.asIdeal := by
    refine (hmax.eq_of_le (RingHom.ker_ne_top g) fun a ha => ?_).symm
    rw [RingHom.mem_ker]
    show φ (Ideal.Quotient.mk 𝔮.asIdeal a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  have hgκ : g.comp (algebraMap κ A) = algebraMap κ Ω := by
    ext cst
    show φ (Ideal.Quotient.mk 𝔮.asIdeal (algebraMap κ A cst)) = algebraMap κ Ω cst
    rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply, AlgHom.commutes]
  let rb : Spec (CommRingCat.of Ω) ⟶ pullback q (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    Spec.map (CommRingCat.ofHom g) ≫ F.inv ≫ (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R R')))).fiberι x
  let pt : PrimeSpectrum Ω := ⊥
  refine ⟨rb, ⟨pt, ?_⟩, ?_⟩
  ·
    have h1 : (Spec.map (CommRingCat.ofHom g)).base pt = 𝔮 := by
      apply PrimeSpectrum.ext
      show Ideal.comap g ⊥ = 𝔮.asIdeal
      rw [← RingHom.ker_eq_comap_bot, hgker]
    have h2 : F.inv.base 𝔮 = y := by
      show (F.hom ≫ F.inv).base y = y
      rw [Iso.hom_inv_id]; rfl
    show ((pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R R')))).fiberι x).base
      (F.inv.base ((Spec.map (CommRingCat.ofHom g)).base pt)) = r
    rw [h1, h2, hy]
  ·
    show (Spec.map (CommRingCat.ofHom g) ≫ F.inv ≫ (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R R')))).fiberι x) ≫
        pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R R'))) =
      Spec.map (CommRingCat.ofHom (algebraMap κ Ω)) ≫ P.fromSpecResidueField x
    have hcond : (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R R')))).fiberι x ≫
        pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R R'))) =
        (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R R')))).fiberToSpecResidueField x ≫ P.fromSpecResidueField x :=
      pullback.condition
    rw [Category.assoc, Category.assoc, hcond, ← Category.assoc F.inv, hFsnd, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, hgκ]

end S0sec
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor.RepresentableBy"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.ker_comp_of_isIso Spec.map_preimage Scheme.Hom.fiberι_fiberHomeo_symm Scheme.IdealSheafData.ideal_mul pullbackSpecIso_inv_fst' Scheme.IdealSheafData.comap_comp Scheme.Modules.pullback Scheme.Hom Scheme.range_fromSpecResidueField Scheme.homeoOfIso LocallyOfFiniteType Spec Spec.map Scheme pullbackSpecIso Scheme.IdealSheafData.comap_top IsOpenImmersion Scheme.IdealSheafData.ker_fst_of_isClosedImmersion Spec.map_injective IsClosedImmersion IsSeparated Spec.preimage Scheme.Modules.pullbackCongr Etale Scheme.Modules.pullbackId IsAffineOpen Scheme.Modules Scheme.IdealSheafData.ext Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion Scheme.Modules.IsInvertible Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso RelEffCartierDiv mapOnProdOver Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison prodKerGraph_comap_mapOnProdOver prodKerGraph prodKerGraph_eq_prod graphOver graphOver_fst graphOver_snd Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover SmoothProperCurve.specMap SmoothProperCurve.baseChange SmoothProperCurve.sectionBaseChange RelPicard.BaseChange.κ RelPicard.BaseChange.overR RelPicard.BaseChange.toR RelPicard.BaseChange.toR_pullbackAlong_iso RelPicard.BaseChange.restrict RelPicard.BaseChange.restrict_algEquivZeroCut RelPicard.BaseChange.classesEquiv RelPicard.BaseChange.relSubPicPresheafRestrictIso RelPicard.BaseChange.relSubPicPresheafAlgEquivZeroCutIso RelPicard.BaseChange.representableByRestrict DescentAction DescentAction.univ DescentAction.map_repActOver_univ DescentAction.ofRepresentableBy DescentAction.act_comp DescentAction.act" namespace RelPicard p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle SubPicCondition RepresentsRelSubPic fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso algEquivZeroCut relSubPicPresheaf relSubPicPresheaf_map_coe sectionIdeal sectionTwist fibreModule BaseChange.κ BaseChange.κ_hom_snd BaseChange.κ_hom_fst BaseChange.rigSection_fst' BaseChange.rigSection_snd' BaseChange.overR BaseChange.toR BaseChange.toR_pullbackAlong_iso BaseChange.restrict BaseChange.restrict_algEquivZeroCut BaseChange.classesEquiv BaseChange.relSubPicPresheafRestrictIso BaseChange.relSubPicPresheafAlgEquivZeroCutIso BaseChange.representableByRestrict sectionFibrePoint" end AlgebraicGeometry.RelPicard
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.RelPicard" in
theorem AlgebraicGeometry.RelPicard.isAlgEquivZero_pullbackAlong_L_of_fibrewiseAlgEquivZero
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] (ψ : SchemeHomOver (specMap R Ω) t) :
    IsAlgEquivZero (pullback.snd c (specMap R Ω)) (M.pullbackAlong ψ).L := by

  have h1 := (hM.pullback ψ) Ω (𝟙 (Spec (CommRingCat.of Ω)))

  set f₁ := pullback.fst (pullback.snd c (specMap R Ω)) (𝟙 (Spec (CommRingCat.of Ω))) with hf₁
  haveI : IsIso f₁ := by rw [hf₁]; infer_instance
  have he : inv f₁ ≫ fibreAt c (specMap R Ω) (𝟙 _) = pullback.snd c (specMap R Ω) := by
    rw [IsIso.inv_comp_eq]
    show pullback.snd (pullback.snd c (specMap R Ω)) (𝟙 _) = f₁ ≫ pullback.snd c (specMap R Ω)
    rw [hf₁, pullback.condition, Category.comp_id]
  refine IsAlgEquivZero.of_iso ?_ (h1.pullback (inv f₁) he)

  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id f₁)).app _ ≪≫
    (Scheme.Modules.pullbackId _).app _

p2m_open "CategoryTheory.MonoidalCategory"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.ker_comp_of_isIso Spec.map_preimage Scheme.Hom.fiberι_fiberHomeo_symm Scheme.IdealSheafData.ideal_mul pullbackSpecIso_inv_fst' Scheme.IdealSheafData.comap_comp Scheme.Modules.pullback Scheme.Hom Scheme.range_fromSpecResidueField Scheme.homeoOfIso LocallyOfFiniteType Spec Spec.map Scheme pullbackSpecIso Scheme.IdealSheafData.comap_top IsOpenImmersion Scheme.IdealSheafData.ker_fst_of_isClosedImmersion Spec.map_injective IsClosedImmersion IsSeparated Spec.preimage Scheme.Modules.pullbackCongr Etale Scheme.Modules.pullbackId IsAffineOpen Scheme.Modules Scheme.IdealSheafData.ext Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion Scheme.Modules.IsInvertible Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso RelEffCartierDiv mapOnProdOver Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison prodKerGraph_comap_mapOnProdOver prodKerGraph prodKerGraph_eq_prod graphOver graphOver_fst graphOver_snd Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover SmoothProperCurve.specMap SmoothProperCurve.baseChange SmoothProperCurve.sectionBaseChange RelPicard.BaseChange.κ RelPicard.BaseChange.overR RelPicard.BaseChange.toR RelPicard.BaseChange.toR_pullbackAlong_iso RelPicard.BaseChange.restrict RelPicard.BaseChange.restrict_algEquivZeroCut RelPicard.BaseChange.classesEquiv RelPicard.BaseChange.relSubPicPresheafRestrictIso RelPicard.BaseChange.relSubPicPresheafAlgEquivZeroCutIso RelPicard.BaseChange.representableByRestrict DescentAction DescentAction.univ DescentAction.map_repActOver_univ DescentAction.ofRepresentableBy DescentAction.act_comp DescentAction.act"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle SubPicCondition RepresentsRelSubPic fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso algEquivZeroCut relSubPicPresheaf relSubPicPresheaf_map_coe sectionIdeal sectionTwist fibreModule BaseChange.κ BaseChange.κ_hom_snd BaseChange.κ_hom_fst BaseChange.rigSection_fst' BaseChange.rigSection_snd' BaseChange.overR BaseChange.toR BaseChange.toR_pullbackAlong_iso BaseChange.restrict BaseChange.restrict_algEquivZeroCut BaseChange.classesEquiv BaseChange.relSubPicPresheafRestrictIso BaseChange.relSubPicPresheafAlgEquivZeroCutIso BaseChange.representableByRestrict sectionFibrePoint"
namespace G2
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (R' : Type u) [CommRing R'] [Algebra R R']
  {Ω : Type u} [Field Ω] [Algebra R Ω]
  (t' : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R')) (ht' : t' ≫ specMap R R' = specMap R Ω)

def Ψ : pullback (baseChange R c R') t' ≅ pullback c (specMap R Ω) :=
  BaseChange.κ c R' t' ≪≫ pullback.congrHom rfl ht'

@[reassoc (attr := simp)]
theorem Ψ_hom_snd : (Ψ c R' t' ht').hom ≫ pullback.snd c (specMap R Ω) = pullback.snd (baseChange R c R') t' := by
  simp only [Ψ, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
  exact BaseChange.κ_hom_snd c R' t'

@[reassoc (attr := simp)]
theorem Ψ_hom_fst : (Ψ c R' t' ht').hom ≫ pullback.fst c (specMap R Ω) =
    pullback.fst (baseChange R c R') t' ≫ pullback.fst c (specMap R R') := by
  simp only [Ψ, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]
  exact BaseChange.κ_hom_fst c R' t'

@[reassoc (attr := simp)]
theorem Ψ_inv_fst : (Ψ c R' t' ht').inv ≫ pullback.fst (baseChange R c R') t' ≫ pullback.fst c (specMap R R') =
    pullback.fst c (specMap R Ω) := by
  rw [← Ψ_hom_fst c R' t' ht', Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
theorem Ψ_inv_snd : (Ψ c R' t' ht').inv ≫ pullback.snd (baseChange R c R') t' = pullback.snd c (specMap R Ω) := by
  rw [← Ψ_hom_snd c R' t' ht', Iso.inv_hom_id_assoc]

theorem graphOver_comp_Ψ_hom (a : Spec (CommRingCat.of Ω) ⟶ pullback c (specMap R R')) (ha : a ≫ baseChange R c R' = t') :
    graphOver (baseChange R c R') a ha ≫ (Ψ c R' t' ht').hom =
      graphOver c (a ≫ pullback.fst c (specMap R R'))
        (by rw [Category.assoc, pullback.condition, ← Category.assoc, ha, ht']) := by
  apply pullback.hom_ext
  · rw [Category.assoc, Ψ_hom_fst, graphOver_fst, ← Category.assoc, graphOver_fst]
  · rw [Category.assoc, Ψ_hom_snd, graphOver_snd, graphOver_snd]

theorem graphOver_section_comp_Ψ_hom (σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (baseChange R c R')) :
    graphOver (baseChange R c R') (t' ≫ σ.1) (by rw [Category.assoc, σ.2, Category.comp_id]) ≫ (Ψ c R' t' ht').hom =
      graphOver c (t' ≫ σ.1 ≫ pullback.fst c (specMap R R'))
        (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc σ.1, σ.2, Category.id_comp, ht']) := by
  rw [graphOver_comp_Ψ_hom]
  simp only [Category.assoc]

theorem rigSection_comp_Ψ_hom (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    rigSection (baseChange R c R') t' (sectionBaseChange R' ε) ≫ (Ψ c R' t' ht').hom = rigSection c (specMap R Ω) ε := by
  apply pullback.hom_ext
  · rw [Category.assoc, Ψ_hom_fst, ← Category.assoc, BaseChange.rigSection_fst', Category.assoc,
      sectionBaseChange_coe_fst, ← Category.assoc, ht', BaseChange.rigSection_fst']
  · rw [Category.assoc, Ψ_hom_snd, BaseChange.rigSection_snd', BaseChange.rigSection_snd']

end AlgebraicGeometry.RelPicard.G2
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor.RepresentableBy"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor.RepresentableBy"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor.RepresentableBy"

section K1
open AlgebraicGeometry.RelPicard.G2

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
  (R' : Type u) [CommRing R'] [Algebra R R']
  {Ω : Type u} [Field Ω] [Algebra R Ω]
  (t' : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R')) (ht' : t' ≫ specMap R R' = specMap R Ω)

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.ker_comp_of_isIso Spec.map_preimage Scheme.Hom.fiberι_fiberHomeo_symm Scheme.IdealSheafData.ideal_mul pullbackSpecIso_inv_fst' Scheme.IdealSheafData.comap_comp Scheme.Modules.pullback Scheme.Hom Scheme.range_fromSpecResidueField Scheme.homeoOfIso LocallyOfFiniteType Spec Spec.map Scheme pullbackSpecIso Scheme.IdealSheafData.comap_top IsOpenImmersion Scheme.IdealSheafData.ker_fst_of_isClosedImmersion Spec.map_injective IsClosedImmersion IsSeparated Spec.preimage Scheme.Modules.pullbackCongr Etale Scheme.Modules.pullbackId IsAffineOpen Scheme.Modules Scheme.IdealSheafData.ext Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion Scheme.Modules.IsInvertible Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso RelEffCartierDiv mapOnProdOver Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison prodKerGraph_comap_mapOnProdOver prodKerGraph prodKerGraph_eq_prod graphOver graphOver_fst graphOver_snd Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover SmoothProperCurve.specMap SmoothProperCurve.baseChange SmoothProperCurve.sectionBaseChange RelPicard.BaseChange.κ RelPicard.BaseChange.overR RelPicard.BaseChange.toR RelPicard.BaseChange.toR_pullbackAlong_iso RelPicard.BaseChange.restrict RelPicard.BaseChange.restrict_algEquivZeroCut RelPicard.BaseChange.classesEquiv RelPicard.BaseChange.relSubPicPresheafRestrictIso RelPicard.BaseChange.relSubPicPresheafAlgEquivZeroCutIso RelPicard.BaseChange.representableByRestrict DescentAction DescentAction.univ DescentAction.map_repActOver_univ DescentAction.ofRepresentableBy DescentAction.act_comp DescentAction.act" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.ker_comp_of_isIso fromSpecResidueField Hom.fiberι_fiberHomeo_symm IdealSheafData.ideal_mul IdealSheafData.comap_comp Modules.pullback Hom mk Γ empty range_fromSpecResidueField homeoOfIso IdealSheafData.comap_top IdealSheafData.ker_fst_of_isClosedImmersion residueField Modules.pullbackCongr Modules.pullbackId Modules Opens residue IdealSheafData.ext restrict Hom.comp_apply IdealSheafData Modules.pullbackComp IdealSheafData.ideal_comap_of_isOpenImmersion Modules.IsInvertible Modules.pullbackTensorObjIso Modules.pullbackTensorUnitObjIso IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso IdealSheafData.IsInvertible IdealSheafData.IsInvertible.isIso_pullbackModuleComparison TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso TwoAffineOpenCover" namespace Hom p2m_export "AlgebraicGeometry.Scheme.Hom" "ker_comp_of_isIso image fiberι_fiberHomeo_symm app injective fiber mk appIso fiberι cover ker fiberHomeo fiberToSpecResidueField comp_apply" end AlgebraicGeometry.Scheme.Hom
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

theorem AlgebraicGeometry.Scheme.Hom.ker_comap_inv_of_iso {T Y X : Scheme.{u}} (q : T ⟶ Y) [IsClosedImmersion q] (e : Y ≅ X) :
    q.ker.comap e.inv = (q ≫ e.hom).ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion q e.inv]

  have h : pullback.lift (q ≫ e.hom) (𝟙 T) (by simp) ≫ pullback.fst e.inv q = q ≫ e.hom := pullback.lift_fst _ _ _
  haveI : IsIso (pullback.lift (q ≫ e.hom) (𝟙 T) (by simp) : T ⟶ pullback e.inv q) := by
    refine ⟨⟨pullback.snd e.inv q, ?_, ?_⟩⟩
    · rw [pullback.lift_snd]
    · apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
        have := pullback.condition (f := e.inv) (g := q)
        rw [← cancel_mono e.hom] at this
        simpa using this.symm
      · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  rw [← h, Scheme.Hom.ker_comp_of_isIso]

theorem ker_graphOver_section_comap_Ψ_inv (σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (baseChange R c R')) :
    ((graphOver (baseChange R c R') (t' ≫ σ.1) (by rw [Category.assoc, σ.2, Category.comp_id])).ker).comap
        (Ψ c R' t' ht').inv =
      (graphOver c (t' ≫ σ.1 ≫ pullback.fst c (specMap R R'))
        (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc σ.1, σ.2, Category.id_comp, ht'])).ker := by
  haveI : IsSeparated (baseChange R c R') := inferInstance
  rw [Scheme.Hom.ker_comap_inv_of_iso, graphOver_section_comp_Ψ_hom]

end K1
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor.RepresentableBy"

section D
open AlgebraicGeometry.RelPicard.G2

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.ker_comp_of_isIso Spec.map_preimage Scheme.Hom.fiberι_fiberHomeo_symm Scheme.IdealSheafData.ideal_mul pullbackSpecIso_inv_fst' Scheme.IdealSheafData.comap_comp Scheme.Modules.pullback Scheme.Hom Scheme.range_fromSpecResidueField Scheme.homeoOfIso LocallyOfFiniteType Spec Spec.map Scheme pullbackSpecIso Scheme.IdealSheafData.comap_top IsOpenImmersion Scheme.IdealSheafData.ker_fst_of_isClosedImmersion Spec.map_injective IsClosedImmersion IsSeparated Spec.preimage Scheme.Modules.pullbackCongr Etale Scheme.Modules.pullbackId IsAffineOpen Scheme.Modules Scheme.IdealSheafData.ext Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion Scheme.Modules.IsInvertible Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso RelEffCartierDiv mapOnProdOver Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison prodKerGraph_comap_mapOnProdOver prodKerGraph prodKerGraph_eq_prod graphOver graphOver_fst graphOver_snd Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover SmoothProperCurve.specMap SmoothProperCurve.baseChange SmoothProperCurve.sectionBaseChange RelPicard.BaseChange.κ RelPicard.BaseChange.overR RelPicard.BaseChange.toR RelPicard.BaseChange.toR_pullbackAlong_iso RelPicard.BaseChange.restrict RelPicard.BaseChange.restrict_algEquivZeroCut RelPicard.BaseChange.classesEquiv RelPicard.BaseChange.relSubPicPresheafRestrictIso RelPicard.BaseChange.relSubPicPresheafAlgEquivZeroCutIso RelPicard.BaseChange.representableByRestrict DescentAction DescentAction.univ DescentAction.map_repActOver_univ DescentAction.ofRepresentableBy DescentAction.act_comp DescentAction.act" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.ker_comp_of_isIso fromSpecResidueField Hom.fiberι_fiberHomeo_symm IdealSheafData.ideal_mul IdealSheafData.comap_comp Modules.pullback Hom mk Γ empty range_fromSpecResidueField homeoOfIso IdealSheafData.comap_top IdealSheafData.ker_fst_of_isClosedImmersion residueField Modules.pullbackCongr Modules.pullbackId Modules Opens residue IdealSheafData.ext restrict Hom.comp_apply IdealSheafData Modules.pullbackComp IdealSheafData.ideal_comap_of_isOpenImmersion Modules.IsInvertible Modules.pullbackTensorObjIso Modules.pullbackTensorUnitObjIso IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso IdealSheafData.IsInvertible IdealSheafData.IsInvertible.isIso_pullbackModuleComparison TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso TwoAffineOpenCover" namespace IdealSheafData p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "ideal_mul comap_comp mk map subscheme map_id comap_top ker_fst_of_isClosedImmersion ideal map_comp comap ideal_comap_of_isOpenImmersion pullbackModuleComparison module invModule IsInvertible.nonempty_pullback_invModule_iso IsInvertible IsInvertible.isIso_pullbackModuleComparison" end AlgebraicGeometry.Scheme.IdealSheafData
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData" in

theorem AlgebraicGeometry.Scheme.IdealSheafData.comap_mul_of_isIso {X Y : Scheme.{u}} (φ : Y ⟶ X) [IsIso φ] (I J : X.IdealSheafData) :
    (I * J).comap φ = I.comap φ * J.comap φ := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  set e : Γ(Y, U) ≃+* Γ(X, φ ''ᵁ U) := (φ.appIso U).symm.commRingCatIsoToRingEquiv with he
  have hinv : (φ.appIso U).inv.hom = e.toRingHom := rfl
  rw [hinv]
  change Ideal.comap (e : Γ(Y, U) →+* Γ(X, φ ''ᵁ U)) _ =
    Ideal.comap (e : Γ(Y, U) →+* Γ(X, φ ''ᵁ U)) _ * Ideal.comap (e : Γ(Y, U) →+* Γ(X, φ ''ᵁ U)) _
  rw [Ideal.comap_coe, Ideal.comap_coe, Ideal.comap_coe, ← Ideal.map_symm, ← Ideal.map_symm, ← Ideal.map_symm,
    Ideal.map_mul]

p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData" in
theorem AlgebraicGeometry.Scheme.IdealSheafData.comap_prod_of_isIso {X Y : Scheme.{u}} (φ : Y ⟶ X) [IsIso φ] {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) : (∏ i ∈ s, I i).comap φ = ∏ i ∈ s, (I i).comap φ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Scheme.IdealSheafData.comap_top]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Scheme.IdealSheafData.comap_mul_of_isIso, ih]

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
  (R' : Type u) [CommRing R'] [Algebra R R']
  {Ω : Type u} [Field Ω] [Algebra R Ω]
  (t' : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R')) (ht' : t' ≫ specMap R R' = specMap R Ω)

theorem prodKerGraph_sections_comap_Ψ_inv {n : ℕ} (σs : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (baseChange R c R')) :
    (prodKerGraph (baseChange R c R') (fun j => t' ≫ (σs j).1)
        (fun j => by rw [Category.assoc, (σs j).2, Category.comp_id])).comap (Ψ c R' t' ht').inv =
      prodKerGraph c (fun j => t' ≫ (σs j).1 ≫ pullback.fst c (specMap R R'))
        (fun j => by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (σs j).1, (σs j).2,
          Category.id_comp, ht']) := by
  rw [prodKerGraph_eq_prod, prodKerGraph_eq_prod, Scheme.IdealSheafData.comap_prod_of_isIso]
  exact Finset.prod_congr rfl fun j _ => ker_graphOver_section_comap_Ψ_inv c R' t' ht' (σs j)

theorem pullbackAlong_I_comap_Ψ_inv {n : ℕ} (σs : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (baseChange R c R'))
    (E : RelEffCartierDiv (baseChange R c R') n (𝟙 (Spec (CommRingCat.of R'))))
    (hE : E.I = prodKerGraph (baseChange R c R') (fun j => (σs j).1) (fun j => (σs j).2))
    (hcomap : (prodKerGraph (baseChange R c R') (fun j => (σs j).1) (fun j => (σs j).2)).comap
        (mapOnProdOver (baseChange R c R') t' (Category.comp_id t')) =
      prodKerGraph (baseChange R c R') (fun j => t' ≫ (σs j).1) (fun j => by rw [Category.assoc, (σs j).2, Category.comp_id])) :
    ((E.pullbackAlong t' (Category.comp_id t')).I).comap (Ψ c R' t' ht').inv =
      prodKerGraph c (fun j => t' ≫ (σs j).1 ≫ pullback.fst c (specMap R R'))
        (fun j => by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (σs j).1, (σs j).2,
          Category.id_comp, ht']) := by
  rw [← prodKerGraph_sections_comap_Ψ_inv c R' t' ht' σs, ← hcomap, ← hE]
  rfl

end D
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor.RepresentableBy"

section T
open AlgebraicGeometry.RelPicard.G2

p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData" in
theorem AlgebraicGeometry.Scheme.IdealSheafData.comap_pow_of_isIso {X Y : Scheme.{u}} (φ : Y ⟶ X) [IsIso φ] (I : X.IdealSheafData) (n : ℕ) :
    (I ^ n).comap φ = I.comap φ ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact Scheme.IdealSheafData.comap_top φ
  | succ n ih => rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul_of_isIso, ih]

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
  (R' : Type u) [CommRing R'] [Algebra R R']
  {Ω : Type u} [Field Ω] [Algebra R Ω]
  (t' : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R')) (ht' : t' ≫ specMap R R' = specMap R Ω)

omit [IsSeparated c] in

theorem rigSection_eq_sectionFibrePoint :
    rigSection c (specMap R Ω) ε = (sectionFibrePoint ε (specMap R Ω)).1 := rfl

theorem sectionIdeal_comap_Ψ_inv :
    (sectionIdeal (baseChange R c R') (sectionBaseChange R' ε) t').comap (Ψ c R' t' ht').inv =
      (sectionFibrePoint ε (specMap R Ω)).1.ker := by
  haveI : IsSeparated (baseChange R c R') := inferInstance
  have hrig : rigSection (baseChange R c R') t' (sectionBaseChange R' ε) =
      graphOver (baseChange R c R') (t' ≫ (sectionBaseChange R' ε).1)
        (by rw [Category.assoc, (sectionBaseChange R' ε).2, Category.comp_id]) := rfl
  show (rigSection (baseChange R c R') t' (sectionBaseChange R' ε)).ker.comap (Ψ c R' t' ht').inv = _
  rw [hrig, Scheme.Hom.ker_comap_inv_of_iso, ← hrig, rigSection_comp_Ψ_hom]
  rfl

theorem sectionIdeal_pow_comap_Ψ_inv (r : ℕ) :
    ((sectionIdeal (baseChange R c R') (sectionBaseChange R' ε) t') ^ r).comap (Ψ c R' t' ht').inv =
      ((sectionFibrePoint ε (specMap R Ω)).1.ker) ^ r := by
  rw [Scheme.IdealSheafData.comap_pow_of_isIso, sectionIdeal_comap_Ψ_inv]

end T
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor.RepresentableBy"

section Package
open AlgebraicGeometry.RelPicard.G2

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (R' : Type u) [CommRing R'] [Algebra R R']
  {Ω : Type u} [Field Ω] [Algebra R Ω]
  (t' : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R')) (ht' : t' ≫ specMap R R' = specMap R Ω)

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.ker_comp_of_isIso Spec.map_preimage Scheme.Hom.fiberι_fiberHomeo_symm Scheme.IdealSheafData.ideal_mul pullbackSpecIso_inv_fst' Scheme.IdealSheafData.comap_comp Scheme.Modules.pullback Scheme.Hom Scheme.range_fromSpecResidueField Scheme.homeoOfIso LocallyOfFiniteType Spec Spec.map Scheme pullbackSpecIso Scheme.IdealSheafData.comap_top IsOpenImmersion Scheme.IdealSheafData.ker_fst_of_isClosedImmersion Spec.map_injective IsClosedImmersion IsSeparated Spec.preimage Scheme.Modules.pullbackCongr Etale Scheme.Modules.pullbackId IsAffineOpen Scheme.Modules Scheme.IdealSheafData.ext Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion Scheme.Modules.IsInvertible Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso RelEffCartierDiv mapOnProdOver Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison prodKerGraph_comap_mapOnProdOver prodKerGraph prodKerGraph_eq_prod graphOver graphOver_fst graphOver_snd Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover SmoothProperCurve.specMap SmoothProperCurve.baseChange SmoothProperCurve.sectionBaseChange RelPicard.BaseChange.κ RelPicard.BaseChange.overR RelPicard.BaseChange.toR RelPicard.BaseChange.toR_pullbackAlong_iso RelPicard.BaseChange.restrict RelPicard.BaseChange.restrict_algEquivZeroCut RelPicard.BaseChange.classesEquiv RelPicard.BaseChange.relSubPicPresheafRestrictIso RelPicard.BaseChange.relSubPicPresheafAlgEquivZeroCutIso RelPicard.BaseChange.representableByRestrict DescentAction DescentAction.univ DescentAction.map_repActOver_univ DescentAction.ofRepresentableBy DescentAction.act_comp DescentAction.act"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle SubPicCondition RepresentsRelSubPic fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso algEquivZeroCut relSubPicPresheaf relSubPicPresheaf_map_coe sectionIdeal sectionTwist fibreModule BaseChange.κ BaseChange.κ_hom_snd BaseChange.κ_hom_fst BaseChange.rigSection_fst' BaseChange.rigSection_snd' BaseChange.overR BaseChange.toR BaseChange.toR_pullbackAlong_iso BaseChange.restrict BaseChange.restrict_algEquivZeroCut BaseChange.classesEquiv BaseChange.relSubPicPresheafRestrictIso BaseChange.relSubPicPresheafAlgEquivZeroCutIso BaseChange.representableByRestrict sectionFibrePoint"
namespace G2
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

def v (σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (baseChange R c R')) :
    {q : Spec (CommRingCat.of Ω) ⟶ pullback c (specMap R Ω) // q ≫ pullback.snd c (specMap R Ω) = 𝟙 _} :=
  ⟨graphOver c (t' ≫ σ.1 ≫ pullback.fst c (specMap R R'))
      (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc σ.1, σ.2, Category.id_comp, ht']),
    graphOver_snd _ _ _⟩

@[scoped simp] theorem v_fst (σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (baseChange R c R')) :
    (v c R' t' ht' σ).1 ≫ pullback.fst c (specMap R Ω) = t' ≫ σ.1 ≫ pullback.fst c (specMap R R') :=
  pullback.lift_fst _ _ _

theorem v_eq_graphOver_comp_Ψ (σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (baseChange R c R')) :
    (v c R' t' ht' σ).1 = graphOver (baseChange R c R') (t' ≫ σ.1) (by rw [Category.assoc, σ.2, Category.comp_id]) ≫
      (Ψ c R' t' ht').hom :=
  (graphOver_section_comp_Ψ_hom c R' t' ht' σ).symm

theorem nonempty_pullback_Ψ_inv_twist_iso [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (r : ℕ) {n : ℕ}
    (σs : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (baseChange R c R'))
    (E : RelEffCartierDiv (baseChange R c R') n (𝟙 (Spec (CommRingCat.of R'))))
    (hE : E.I = prodKerGraph (baseChange R c R') (fun j => (σs j).1) (fun j => (σs j).2))
    (hT : ((sectionIdeal (baseChange R c R') (sectionBaseChange R' ε) t') ^ r).IsInvertible)
    (hD : (E.pullbackAlong t' (Category.comp_id t')).I.IsInvertible) :
    Nonempty ((Scheme.Modules.pullback (Ψ c R' t' ht').inv).obj
        (sectionTwist (baseChange R c R') (sectionBaseChange R' ε) t' r ⊗ (E.pullbackAlong t' (Category.comp_id t')).idealModule) ≅
      ((((sectionFibrePoint ε (specMap R Ω)).1.ker) ^ r).invModule ⊗ (∏ j, (v c R' t' ht' (σs j)).1.ker).module)) := by

  have hcT := sectionIdeal_pow_comap_Ψ_inv c ε R' t' ht' r
  have hcD : ((E.pullbackAlong t' (Category.comp_id t')).I).comap (Ψ c R' t' ht').inv =
      ∏ j, (v c R' t' ht' (σs j)).1.ker := by
    rw [pullbackAlong_I_comap_Ψ_inv c R' t' ht' σs E hE
      (prodKerGraph_comap_mapOnProdOver (f := baseChange R c R') (fun j => (σs j).1) (fun j => (σs j).2) t'
        (Category.comp_id t')), prodKerGraph_eq_prod]
    rfl

  have hT' := hT.comap_of_isOpenImmersion (Ψ c R' t' ht').inv
  have hD' := hD.comap_of_isOpenImmersion (Ψ c R' t' ht').inv
  obtain ⟨eT⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso (Ψ c R' t' ht').inv hT hT'
  haveI := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison (Ψ c R' t' ht').inv hD hD'
  let eD := asIso (((E.pullbackAlong t' (Category.comp_id t')).I).pullbackModuleComparison (Ψ c R' t' ht').inv)
  refine ⟨Scheme.Modules.pullbackTensorObjIso (Ψ c R' t' ht').inv _ _ ≪≫ (eT ⊗ᵢ eD) ≪≫
    (eqToIso (by rw [hcT]) ⊗ᵢ eqToIso (by rw [hcD]))⟩

theorem exists_algHom_v_fst_eq {Bi : Type u} [CommRing Bi] [Algebra R Bi]
    (z : Spec (CommRingCat.of Bi) ⟶ C) (hz : z ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R Bi)))
    (σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (baseChange R c R'))
    (hσ : ∃ y : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of Bi), σ.1 ≫ pullback.fst c (specMap R R') = y ≫ z) :
    ∃ ψ : Bi →ₐ[R] Ω,
      (v c R' t' ht' σ).1 ≫ pullback.fst c (specMap R Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z := by
  obtain ⟨y, hy⟩ := hσ

  let ψ₀ : Bi →+* Ω := (Spec.preimage (t' ≫ y)).hom
  have hψ₀ : Spec.map (CommRingCat.ofHom ψ₀) = t' ≫ y := by
    simp only [ψ₀, CommRingCat.ofHom_hom, Spec.map_preimage]

  have hcomp : ψ₀.comp (algebraMap R Bi) = algebraMap R Ω := by
    have h1 : Spec.map (CommRingCat.ofHom (ψ₀.comp (algebraMap R Bi))) = Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, hψ₀, ← hz]
      simp only [Category.assoc]
      rw [← Category.assoc y, ← hy, Category.assoc, pullback.condition, ← Category.assoc σ.1, σ.2, Category.id_comp, ht']
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  have hcomm : ∀ a : R, ψ₀.toFun (algebraMap R Bi a) = algebraMap R Ω a := fun a => by
    have := congrArg (fun h : R →+* Ω => h a) hcomp
    simpa using this
  refine ⟨AlgHom.mk ψ₀ hcomm, ?_⟩
  show _ = Spec.map (CommRingCat.ofHom ψ₀) ≫ z
  rw [hψ₀, v_fst, hy, Category.assoc]

end AlgebraicGeometry.RelPicard.G2
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor.RepresentableBy P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry.RelPicard.G2"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor.RepresentableBy P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry.RelPicard"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor.RepresentableBy P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry"

end Package
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor.RepresentableBy P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry.RelPicard.G2"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.ker_comp_of_isIso Spec.map_preimage Scheme.Hom.fiberι_fiberHomeo_symm Scheme.IdealSheafData.ideal_mul pullbackSpecIso_inv_fst' Scheme.IdealSheafData.comap_comp Scheme.Modules.pullback Scheme.Hom Scheme.range_fromSpecResidueField Scheme.homeoOfIso LocallyOfFiniteType Spec Spec.map Scheme pullbackSpecIso Scheme.IdealSheafData.comap_top IsOpenImmersion Scheme.IdealSheafData.ker_fst_of_isClosedImmersion Spec.map_injective IsClosedImmersion IsSeparated Spec.preimage Scheme.Modules.pullbackCongr Etale Scheme.Modules.pullbackId IsAffineOpen Scheme.Modules Scheme.IdealSheafData.ext Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion Scheme.Modules.IsInvertible Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso RelEffCartierDiv mapOnProdOver Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison prodKerGraph_comap_mapOnProdOver prodKerGraph prodKerGraph_eq_prod graphOver graphOver_fst graphOver_snd Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover SmoothProperCurve.specMap SmoothProperCurve.baseChange SmoothProperCurve.sectionBaseChange RelPicard.BaseChange.κ RelPicard.BaseChange.overR RelPicard.BaseChange.toR RelPicard.BaseChange.toR_pullbackAlong_iso RelPicard.BaseChange.restrict RelPicard.BaseChange.restrict_algEquivZeroCut RelPicard.BaseChange.classesEquiv RelPicard.BaseChange.relSubPicPresheafRestrictIso RelPicard.BaseChange.relSubPicPresheafAlgEquivZeroCutIso RelPicard.BaseChange.representableByRestrict DescentAction DescentAction.univ DescentAction.map_repActOver_univ DescentAction.ofRepresentableBy DescentAction.act_comp DescentAction.act"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle SubPicCondition RepresentsRelSubPic fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso algEquivZeroCut relSubPicPresheaf relSubPicPresheaf_map_coe sectionIdeal sectionTwist fibreModule BaseChange.κ BaseChange.κ_hom_snd BaseChange.κ_hom_fst BaseChange.rigSection_fst' BaseChange.rigSection_snd' BaseChange.overR BaseChange.toR BaseChange.toR_pullbackAlong_iso BaseChange.restrict BaseChange.restrict_algEquivZeroCut BaseChange.classesEquiv BaseChange.relSubPicPresheafRestrictIso BaseChange.relSubPicPresheafAlgEquivZeroCutIso BaseChange.representableByRestrict sectionFibrePoint"
namespace G2
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

def isoPullbackInvOfIso {X Y : Scheme.{u}} (φ : X ≅ Y) {M : X.Modules} {N : Y.Modules}
    (e : M ≅ (Scheme.Modules.pullback φ.hom).obj N) : N ≅ (Scheme.Modules.pullback φ.inv).obj M :=
  ((Scheme.Modules.pullbackId Y).app N).symm ≪≫
    (Scheme.Modules.pullbackCongr φ.inv_hom_id.symm).app N ≪≫
    ((Scheme.Modules.pullbackComp φ.inv φ.hom).app N).symm ≪≫
    (Scheme.Modules.pullback φ.inv).mapIso e.symm

section FibreIso

variable {R' : Type u} [CommRing R'] {C'' : Scheme.{u}} (c'' : C'' ⟶ Spec (CommRingCat.of R'))
  {P : Scheme.{u}} (t₀ : P ⟶ Spec (CommRingCat.of R'))
  {Ω : Type u} [Field Ω] (y : Spec (CommRingCat.of Ω) ⟶ P) (x : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R'))
  (hx : y ≫ t₀ = x)

def fibreIso : pullback (pullback.snd c'' t₀) y ≅ pullback c'' x :=
  pullbackLeftPullbackSndIso c'' t₀ y ≪≫ pullback.congrHom rfl hx

@[reassoc]
theorem fibreIso_hom_snd : (fibreIso c'' t₀ y x hx).hom ≫ pullback.snd c'' x = fibreAt c'' t₀ y := by
  subst hx
  simp [fibreIso, fibreAt, pullback.congrHom_hom]

@[reassoc]
theorem fibreIso_hom_fst :
    (fibreIso c'' t₀ y x hx).hom ≫ pullback.fst c'' x = pullback.fst (pullback.snd c'' t₀) y ≫ pullback.fst c'' t₀ := by
  subst hx
  simp [fibreIso, pullback.congrHom_hom]

theorem fibreIso_inv_fibreAt : (fibreIso c'' t₀ y x hx).inv ≫ fibreAt c'' t₀ y = pullback.snd c'' x := by
  rw [← fibreIso_hom_snd c'' t₀ y x hx, Iso.inv_hom_id_assoc]

theorem fibreIso_hom_baseChangeSnd :
    (fibreIso c'' t₀ y x hx).hom ≫ baseChangeSnd c'' (⟨y, hx⟩ : SchemeHomOver x t₀)
      = pullback.fst (pullback.snd c'' t₀) y := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    unfold baseChangeSnd
    rw [pullback.lift_fst, ← Category.assoc, fibreIso_hom_fst, Category.assoc, Category.comp_id]
  · rw [Category.assoc]
    unfold baseChangeSnd
    rw [pullback.lift_snd, ← Category.assoc, fibreIso_hom_snd, pullback.condition]
    try rfl

def fibreModuleIso (M : (pullback c'' t₀).Modules) :
    fibreModule c'' t₀ y M ≅ (Scheme.Modules.pullback (fibreIso c'' t₀ y x hx).hom).obj
      ((Scheme.Modules.pullback (baseChangeSnd c'' (⟨y, hx⟩ : SchemeHomOver x t₀))).obj M) :=
  (Scheme.Modules.pullbackCongr (fibreIso_hom_baseChangeSnd c'' t₀ y x hx).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (fibreIso c'' t₀ y x hx).hom
      (baseChangeSnd c'' (⟨y, hx⟩ : SchemeHomOver x t₀))).app M).symm

def fibreUnitIso :
    (𝟙_ (pullback (pullback.snd c'' t₀) y).Modules) ≅
      (Scheme.Modules.pullback (fibreIso c'' t₀ y x hx).hom).obj (𝟙_ (pullback c'' x).Modules) :=
  (Scheme.Modules.pullbackTensorUnitObjIso (fibreIso c'' t₀ y x hx).hom).symm

def fibreModuleTensorIso (M N : (pullback c'' t₀).Modules) :
    fibreModule c'' t₀ y (M ⊗ N) ≅ (Scheme.Modules.pullback (fibreIso c'' t₀ y x hx).hom).obj
      (((Scheme.Modules.pullback (baseChangeSnd c'' (⟨y, hx⟩ : SchemeHomOver x t₀))).obj M) ⊗
        ((Scheme.Modules.pullback (baseChangeSnd c'' (⟨y, hx⟩ : SchemeHomOver x t₀))).obj N)) :=
  fibreModuleIso c'' t₀ y x hx (M ⊗ N) ≪≫
    (Scheme.Modules.pullback (fibreIso c'' t₀ y x hx).hom).mapIso (Scheme.Modules.pullbackTensorObjIso _ M N)

theorem forall_subsingleton_H1_fibre_of_iso {Z : Scheme.{u}} (Φ : pullback (pullback.snd c'' t₀) y ≅ Z)
    (z : Z ⟶ Spec (CommRingCat.of Ω)) (hΦ : Φ.hom ≫ z = fibreAt c'' t₀ y)
    (F : (pullback c'' t₀).Modules) (F' : Z.Modules)
    (eF : fibreModule c'' t₀ y F ≅ (Scheme.Modules.pullback Φ.hom).obj F')
    (h : ∀ 𝒱 : Z.TwoAffineOpenCover, Subsingleton (𝒱.sectionsOf z F').H1)
    (𝒲 : (pullback (pullback.snd c'' t₀) y).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c'' t₀ y) (fibreModule c'' t₀ y F)).H1 := by
  have hΦ' : Φ.inv ≫ fibreAt c'' t₀ y = z := by rw [← hΦ, Iso.inv_hom_id_assoc]
  obtain ⟨𝒱, -, -, -, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    z (fibreAt c'' t₀ y) Φ.symm hΦ' 𝒲 _ _ (isoPullbackInvOfIso Φ eF)
  haveI := h 𝒱
  exact e1.symm.toEquiv.subsingleton

end FibreIso
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor.RepresentableBy P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry.RelPicard.G2"

end AlgebraicGeometry.RelPicard.G2
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor.RepresentableBy P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry.RelPicard.G2"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor.RepresentableBy P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry.RelPicard.G2"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor.RepresentableBy P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry.RelPicard.G2"

p2m_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_forall_exists_lift_chart
    {P X : Scheme.{u}} (F : Scheme.{u}ᵒᵖ ⥤ Type (u + 1))
    (x : uliftYoneda.{u + 1}.obj P ⟶ F) [IsIso x]
    (f : uliftYoneda.{u + 1}.obj X ⟶ F) (hf : MorphismProperty.presheafULift.{u + 1} @IsOpenImmersion f)
    (hfin : ∀ S : Finset X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ s ∈ S, s ∈ U)
    (S : Finset P)
    (hS : ∀ s ∈ S, ∃ (k : Type u) (_ : Field k) (y : Spec (CommRingCat.of k) ⟶ P) (φ' : Spec (CommRingCat.of k) ⟶ X),
      s ∈ Set.range y ∧ uliftYoneda.{u + 1}.map φ' ≫ f = uliftYoneda.{u + 1}.map y ≫ x) :
    ∃ W : P.Opens, IsAffineOpen W ∧ ∀ s ∈ S, s ∈ W := by
  classical

  obtain ⟨j, hj⟩ : ∃ j : X ⟶ P, uliftYoneda.{u + 1}.map j = f ≫ inv x :=
    ⟨uliftYoneda.{u + 1}.preimage (f ≫ inv x), Functor.map_preimage _ _⟩
  have sq : IsPullback (𝟙 (uliftYoneda.{u + 1}.obj X)) (uliftYoneda.{u + 1}.map j) f x :=
    IsPullback.of_horiz_isIso ⟨by rw [hj, Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]⟩
  haveI : IsOpenImmersion j := hf.property x (𝟙 _) j sq

  have key : ∀ s ∈ S, ∃ p : X, j p = s := by
    intro s hs
    obtain ⟨k, _, y, φ', ⟨q, hq⟩, hcomm⟩ := hS s hs
    have hy : φ' ≫ j = y := by
      apply uliftYoneda.{u + 1}.map_injective
      rw [Functor.map_comp, hj, ← Category.assoc, hcomm, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    exact ⟨φ' q, by rw [← Scheme.Hom.comp_apply, hy, hq]⟩
  choose p hp using key
  have hfin' := hfin (S.attach.image fun s => p s.1 s.2)
  obtain ⟨U, hU, hSU⟩ := hfin'
  refine ⟨j ''ᵁ U, hU.image_of_isOpenImmersion j, fun s hs => ?_⟩
  exact ⟨p s hs, hSU _ (Finset.mem_image_of_mem _ (Finset.mem_attach S ⟨s, hs⟩)), hp s hs⟩

namespace WGEN

theorem nonempty_pullbackAlong_act_iso_pullbackAlong_fst
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (D' : RelativePic0Designation R' (SmoothProperCurve.baseChange R c R'))
    (h' : RepresentsRelSubPic (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
      (algEquivZeroCut (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)) D')
    (𝓛 : RigidifiedLineBundle c ε (D'.toBase ≫ SmoothProperCurve.specMap R R'))
    (h𝓛 : Quotient.mk _ 𝓛 =
      (DescentAction.univ (SmoothProperCurve.specMap R R') (relSubPicPresheaf c ε (algEquivZeroCut c ε)) D'.toBase
        (AlgebraicGeometry.RelPicard.BaseChange.representableByRestrict c ε R' h')).1)
    {T : Scheme.{u}}
    (g : T ⟶ pullback (D'.toBase ≫ SmoothProperCurve.specMap R R') (SmoothProperCurve.specMap R R'))
    {b : T ⟶ Spec (CommRingCat.of R)}
    (hb : g ≫ pullback.snd (D'.toBase ≫ SmoothProperCurve.specMap R R') (SmoothProperCurve.specMap R R') ≫
      SmoothProperCurve.specMap R R' = b) :
    Nonempty
      ((𝓛.pullbackAlong
          (⟨g ≫ (DescentAction.ofRepresentableBy (SmoothProperCurve.specMap R R')
              (relSubPicPresheaf c ε (algEquivZeroCut c ε)) D'.toBase
              (AlgebraicGeometry.RelPicard.BaseChange.representableByRestrict c ε R' h')).act,
            by rw [← hb, Category.assoc, ← Category.assoc (DescentAction.act _), DescentAction.act_comp]⟩ :
            SchemeHomOver b (D'.toBase ≫ SmoothProperCurve.specMap R R'))).L ≅
        (𝓛.pullbackAlong
          (⟨g ≫ pullback.fst (D'.toBase ≫ SmoothProperCurve.specMap R R') (SmoothProperCurve.specMap R R'),
            by rw [← hb, Category.assoc, pullback.condition]⟩ :
            SchemeHomOver b (D'.toBase ≫ SmoothProperCurve.specMap R R'))).L) := by
  set s := SmoothProperCurve.specMap R R' with hs
  set G := relSubPicPresheaf c ε (algEquivZeroCut c ε) with hG
  set hX' := AlgebraicGeometry.RelPicard.BaseChange.representableByRestrict c ε R' h' with hhX'
  have H := DescentAction.map_repActOver_univ s G D'.toBase hX'

  let g' : Over.mk b ⟶ (Over.map s).obj (Over.mk (pullback.snd (D'.toBase ≫ s) s)) :=
    Over.homMk g hb
  have H' := congrArg (G.map g'.op) H
  simp only [← types_comp_apply (G.map _) (G.map _), ← G.map_comp, ← op_comp] at H'
  have H'' := congrArg Subtype.val H'
  rw [relSubPicPresheaf_map_coe, relSubPicPresheaf_map_coe, ← h𝓛] at H''
  exact Quotient.exact H''

end WGEN
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor.RepresentableBy P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry.RelPicard.G2"

namespace WGEN

theorem nonempty_pullbackAlong_L_iso_of_val_eq {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {b : T' ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t) (ψ₁ ψ₂ : SchemeHomOver b t) (h : ψ₁.1 = ψ₂.1) :
    Nonempty ((M.pullbackAlong ψ₁).L ≅ (M.pullbackAlong ψ₂).L) := by
  obtain rfl : ψ₁ = ψ₂ := Subtype.ext h
  exact ⟨Iso.refl _⟩

theorem nonempty_pullback_congrHom_inv_pullbackAlong_L_iso {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} {b₁ b₂ : T' ⟶ Spec (CommRingCat.of R)} (hb : b₁ = b₂) (M : RigidifiedLineBundle c ε t)
    (ψ₁ : SchemeHomOver b₁ t) (ψ₂ : SchemeHomOver b₂ t) (h : ψ₁.1 = ψ₂.1) :
    Nonempty ((Scheme.Modules.pullback (pullback.congrHom (rfl : c = c) hb).inv).obj (M.pullbackAlong ψ₁).L ≅
      (M.pullbackAlong ψ₂).L) := by
  subst hb
  obtain rfl : ψ₁ = ψ₂ := Subtype.ext h
  have hid : (pullback.congrHom (rfl : c = c) (rfl : b₁ = b₁)).inv = 𝟙 _ := by
    rw [pullback.congrHom_inv]
    exact pullback.map_id
  exact ⟨(Scheme.Modules.pullbackCongr hid).app _ ≪≫ (Scheme.Modules.pullbackId _).app _⟩

end WGEN
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor.RepresentableBy P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry.RelPicard.G2"

theorem WGEN.eqToIso_trans_restrictIso_hom_app_coe (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (R' : Type u) [CommRing R'] [Algebra R R']
    (P : SubPicCondition c ε)
    {P₁ : SubPicCondition (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)}
    (h : P₁ = AlgebraicGeometry.RelPicard.BaseChange.restrict c ε R' P)
    (X : (Over (Spec (CommRingCat.of R')))ᵒᵖ)
    (w : (relSubPicPresheaf (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε) P₁).obj X) :
    ((eqToIso (congrArg (relSubPicPresheaf (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)) h) ≪≫
        AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso c ε R' P).hom.app X w).1 =
      AlgebraicGeometry.RelPicard.BaseChange.classesEquiv c ε R' X.unop.hom w.1 := by
  subst h
  rfl

theorem WGEN.relSubPicPresheafAlgEquivZeroCutIso_hom_app_coe (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (R' : Type u) [CommRing R'] [Algebra R R']
    (X : (Over (Spec (CommRingCat.of R')))ᵒᵖ)
    (w : (relSubPicPresheaf (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
      (algEquivZeroCut (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε))).obj X) :
    ((AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafAlgEquivZeroCutIso c ε R').hom.app X w).1 =
      AlgebraicGeometry.RelPicard.BaseChange.classesEquiv c ε R' X.unop.hom w.1 := by
  have hI : AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafAlgEquivZeroCutIso c ε R' =
      eqToIso (congrArg (relSubPicPresheaf (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε))
        (AlgebraicGeometry.RelPicard.BaseChange.restrict_algEquivZeroCut c ε R').symm) ≪≫
        AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso c ε R' (algEquivZeroCut c ε) := rfl
  rw [hI]
  exact WGEN.eqToIso_trans_restrictIso_hom_app_coe R c ε R' (algEquivZeroCut c ε)
    (AlgebraicGeometry.RelPicard.BaseChange.restrict_algEquivZeroCut c ε R').symm X w

theorem WGEN.ofIso_homEquiv_apply.{w', v', u'} {𝒞 : Type u'} [Category.{v'} 𝒞] {F F' : 𝒞ᵒᵖ ⥤ Type w'} {Y : 𝒞}
    (e : F.RepresentableBy Y) (I : F ≅ F') {X : 𝒞} (g : X ⟶ Y) :
    (e.ofIso I).homEquiv g = I.hom.app _ (e.homEquiv g) := rfl

theorem WGEN.mk_toR_poincare_eq_univ (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (R' : Type u) [CommRing R'] [Algebra R R']
    (D' : RelativePic0Designation R' (SmoothProperCurve.baseChange R c R'))
    (h' : RepresentsRelSubPic (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
      (algEquivZeroCut (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)) D') :
    Quotient.mk _ (AlgebraicGeometry.RelPicard.BaseChange.toR c ε R' (h'.poincare.pullbackAlong ⟨𝟙 _, Category.id_comp _⟩)) =
      (DescentAction.univ (SmoothProperCurve.specMap R R') (relSubPicPresheaf c ε (algEquivZeroCut c ε)) D'.toBase
        (AlgebraicGeometry.RelPicard.BaseChange.representableByRestrict c ε R' h')).1 := by
  change _ = ((AlgebraicGeometry.RelPicard.BaseChange.representableByRestrict c ε R' h').homEquiv (𝟙 (Over.mk D'.toBase))).1
  have e1 : (AlgebraicGeometry.RelPicard.BaseChange.representableByRestrict c ε R' h').homEquiv (𝟙 (Over.mk D'.toBase)) =
      (AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafAlgEquivZeroCutIso c ε R').hom.app _
        (h'.representableBy.homEquiv (𝟙 (Over.mk D'.toBase))) :=
    WGEN.ofIso_homEquiv_apply _ _ _
  rw [e1, WGEN.relSubPicPresheafAlgEquivZeroCutIso_hom_app_coe]
  have e2 : (h'.representableBy.homEquiv (𝟙 (Over.mk D'.toBase))).1 =
      Quotient.mk _ (h'.poincare.pullbackAlong ⟨𝟙 _, Category.id_comp _⟩) := rfl
  change _ = AlgebraicGeometry.RelPicard.BaseChange.classesEquiv c ε R' D'.toBase ((h'.representableBy.homEquiv (𝟙 (Over.mk D'.toBase))).1)
  rw [e2]
  rfl

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Algebra.Etale R R']
    [Module.FaithfullyFlat R R']
    (D' : RelativePic0Designation R' (SmoothProperCurve.baseChange R c R'))
    (h' : RepresentsRelSubPic (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
      (algEquivZeroCut (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)) D')
    (hlft : LocallyOfFiniteType D'.toBase)

    {M : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C)
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))

    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i)
    (σ : ∀ i, Fin (deg i) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (SmoothProperCurve.baseChange R c R'))
    (hσ : ∀ i m, ∃ y : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of (B i)),
      (σ i m).1 ≫ pullback.fst c (SmoothProperCurve.specMap R R') = y ≫ z i)

    (r g : ℕ) {ι : Type u}
    (idx : {a : Fin (r - g) → Fin M // Function.Injective a} → (∀ i, Fin (deg i)) → ι)
    (X : ι → Scheme.{u})
    (f : ∀ i, uliftYoneda.{u + 1}.obj (X i) ⟶
      (relSubPicPresheaf (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
        (algEquivZeroCut (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε))).overTotal)
    (hf : ∀ i, MorphismProperty.presheafULift.{u + 1} @IsOpenImmersion (f i))
    (hfin : ∀ (i : ι) (F : Finset (X i)), ∃ U : (X i).Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    (Dγ : ι → RelEffCartierDiv (SmoothProperCurve.baseChange R c R') (r - g) (𝟙 (Spec (CommRingCat.of R'))))
    (hDγ : ∀ (a : {a : Fin (r - g) → Fin M // Function.Injective a}) (m : ∀ i, Fin (deg i)),
      (Dγ (idx a m)).I = prodKerGraph (SmoothProperCurve.baseChange R c R')
        (fun j => (σ (a.1 j) (m (a.1 j))).1) (fun j => (σ (a.1 j) (m (a.1 j))).2))

    (hεinv : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R')),
      (sectionIdeal (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε) t).IsInvertible)
    (hTw : ∀ ⦃T T' : Scheme.{u}⦄ {t : T ⟶ Spec (CommRingCat.of R')} {t' : T' ⟶ Spec (CommRingCat.of R')}
      (ψ : SchemeHomOver t' t),
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd (SmoothProperCurve.baseChange R c R') ψ)).obj
        (sectionTwist (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε) t r) ≅
        sectionTwist (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε) t' r))
    (hDγinv : ∀ (i : ι) ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R')),
      ((Dγ i).pullbackAlong t (Category.comp_id t)).I.IsInvertible)

    (hmem : ∀ (i : ι) ⦃T : Scheme.{u}⦄
      (x : uliftYoneda.{u + 1}.obj T ⟶
        (relSubPicPresheaf (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
          (algEquivZeroCut (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε))).overTotal),
      LocallyOfFiniteType (uliftYonedaEquiv x).1 →
      ∀ (L : RigidifiedLineBundle (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
        (uliftYonedaEquiv x).1), Quotient.mk _ L = (uliftYonedaEquiv x).2.1 →
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
        (∀ (𝒲 : (pullback (pullback.snd (SmoothProperCurve.baseChange R c R') (uliftYonedaEquiv x).1) s).TwoAffineOpenCover),
          Subsingleton (𝒲.sectionsOf (fibreAt (SmoothProperCurve.baseChange R c R') (uliftYonedaEquiv x).1 s)
            (fibreModule (SmoothProperCurve.baseChange R c R') (uliftYonedaEquiv x).1 s
            (L.L ⊗ (sectionTwist (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
              (uliftYonedaEquiv x).1 r ⊗
              ((Dγ i).pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).idealModule)))).H1) →
        ∃ φ' : Spec (CommRingCat.of k) ⟶ X i,
          uliftYoneda.{u + 1}.map φ' ≫ f i = uliftYoneda.{u + 1}.map s ≫ x)

    (hgp : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
      (L₀ : (pullback c (SmoothProperCurve.specMap R Ω)).Modules), Scheme.Modules.IsInvertible L₀ →
      IsAlgEquivZero (pullback.snd c (SmoothProperCurve.specMap R Ω)) L₀ →
      ∃ a : Fin (r - g) → Fin M, Function.Injective a ∧
        ∀ v : Fin (r - g) → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
            q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _},
          (∀ j, ∃ ψ : B (a j) →ₐ[R] Ω,
            (v j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) =
              Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z (a j)) →
          ∀ 𝒲 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover,
            Subsingleton (𝒲.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
              (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r).invModule ⊗
                (∏ j, (v j).1.ker).module))).H1) :
    ∀ x : D'.P, ∃ W : D'.P.Opens, IsAffineOpen W ∧
      ∀ r : ↑(pullback (D'.toBase ≫ SmoothProperCurve.specMap R R') (SmoothProperCurve.specMap R R')),
        (pullback.fst (D'.toBase ≫ SmoothProperCurve.specMap R R') (SmoothProperCurve.specMap R R')) r = x →
        (DescentAction.ofRepresentableBy (SmoothProperCurve.specMap R R')
          (relSubPicPresheaf c ε (algEquivZeroCut c ε)) D'.toBase
          (AlgebraicGeometry.RelPicard.BaseChange.representableByRestrict c ε R' h')).act r ∈ W := by
  intro xP
  classical

  obtain ⟨hfinorb, Ω, _, _, xb, hxb, hlift⟩ := AlgebraicGeometry.finite_preimage_fst_singleton_and_exists_geometric_lifts (R' := R') (D'.toBase ≫ SmoothProperCurve.specMap R R') xP

  letI : Algebra R Ω :=
    (Spec.preimage (xb ≫ D'.toBase ≫ SmoothProperCurve.specMap R R')).hom.toAlgebra
  have hω : SmoothProperCurve.specMap R Ω = xb ≫ D'.toBase ≫ SmoothProperCurve.specMap R R' :=
    Spec.map_preimage _

  let L : RigidifiedLineBundle (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε) D'.toBase :=
    h'.poincare.pullbackAlong ⟨𝟙 _, Category.id_comp _⟩
  let x := (uliftYonedaEquiv.{u + 1} (X := D'.P)
    (F := (relSubPicPresheaf (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
      (algEquivZeroCut (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε))).overTotal)).symm
    ⟨D'.toBase, h'.representableBy.homEquiv (𝟙 _)⟩
  haveI : IsIso x := Functor.RepresentableBy.isIso_uliftYonedaEquiv_symm.{u + 1, u, u + 1} _
  have hxe : uliftYonedaEquiv.{u + 1} x = ⟨D'.toBase, h'.representableBy.homEquiv (𝟙 _)⟩ := Equiv.apply_symm_apply _ _
  have hLcls : Quotient.mk _ L = (h'.representableBy.homEquiv (𝟙 (Over.mk D'.toBase))).1 := rfl

  have hmem' : ∀ (i : ι) (y : Spec (CommRingCat.of Ω) ⟶ D'.P),
      (∀ 𝒲 : (pullback (pullback.snd (SmoothProperCurve.baseChange R c R') D'.toBase) y).TwoAffineOpenCover,
        Subsingleton (𝒲.sectionsOf (fibreAt (SmoothProperCurve.baseChange R c R') D'.toBase y)
          (fibreModule (SmoothProperCurve.baseChange R c R') D'.toBase y
          (L.L ⊗ (sectionTwist (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
            D'.toBase r ⊗ ((Dγ i).pullbackAlong D'.toBase (Category.comp_id _)).idealModule)))).H1) →
      ∃ φ' : Spec (CommRingCat.of Ω) ⟶ X i, uliftYoneda.{u + 1}.map φ' ≫ f i = uliftYoneda.{u + 1}.map y ≫ x := by
    intro i y hH
    have h := hmem i x
    rw [hxe] at h
    exact h hlft L hLcls Ω y hH

  let 𝓛 : RigidifiedLineBundle c ε (D'.toBase ≫ SmoothProperCurve.specMap R R') :=
    AlgebraicGeometry.RelPicard.BaseChange.toR c ε R' L
  have h𝓛 := WGEN.mk_toR_poincare_eq_univ R c ε R' D' h'
  have h𝓛aez : FibrewiseAlgEquivZero 𝓛 := by
    have h2 := (DescentAction.univ (SmoothProperCurve.specMap R R') (relSubPicPresheaf c ε (algEquivZeroCut c ε)) D'.toBase
      (AlgebraicGeometry.RelPicard.BaseChange.representableByRestrict c ε R' h')).2
    rw [← h𝓛] at h2
    exact h2
  let xb' : SchemeHomOver (SmoothProperCurve.specMap R Ω) (D'.toBase ≫ SmoothProperCurve.specMap R R') :=
    ⟨xb, by rw [hω]⟩
  let L₀ : (pullback c (SmoothProperCurve.specMap R Ω)).Modules := (𝓛.pullbackAlong xb').L
  have hL₀ : Scheme.Modules.IsInvertible L₀ := (𝓛.pullbackAlong xb').isInvertible
  have hL₀aez : IsAlgEquivZero (pullback.snd c (SmoothProperCurve.specMap R Ω)) L₀ :=
    AlgebraicGeometry.RelPicard.isAlgEquivZero_pullbackAlong_L_of_fibrewiseAlgEquivZero 𝓛 h𝓛aez xb'
  obtain ⟨a, ha, hgood⟩ := hgp Ω L₀ hL₀ hL₀aez
  let m₀ : ∀ i, Fin (deg i) := fun i => ⟨0, hdeg i⟩
  let i₀ : ι := idx ⟨a, ha⟩ m₀

  have key : ∀ q : ↥(pullback (D'.toBase ≫ SmoothProperCurve.specMap R R') (SmoothProperCurve.specMap R R')),
      pullback.fst (D'.toBase ≫ SmoothProperCurve.specMap R R') (SmoothProperCurve.specMap R R') q = xP →
      ∃ y : Spec (CommRingCat.of Ω) ⟶ D'.P,
        (DescentAction.ofRepresentableBy (SmoothProperCurve.specMap R R')
          (relSubPicPresheaf c ε (algEquivZeroCut c ε)) D'.toBase
          (AlgebraicGeometry.RelPicard.BaseChange.representableByRestrict c ε R' h')).act q ∈ Set.range y ∧
        ∀ 𝒲 : (pullback (pullback.snd (SmoothProperCurve.baseChange R c R') D'.toBase) y).TwoAffineOpenCover,
          Subsingleton (𝒲.sectionsOf (fibreAt (SmoothProperCurve.baseChange R c R') D'.toBase y)
            (fibreModule (SmoothProperCurve.baseChange R c R') D'.toBase y
            (L.L ⊗ (sectionTwist (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
              D'.toBase r ⊗ ((Dγ i₀).pullbackAlong D'.toBase (Category.comp_id _)).idealModule)))).H1 := by
    intro q hq
    obtain ⟨rb, ⟨pt, hpt⟩, hrbx⟩ := hlift q hq
    refine ⟨rb ≫ (DescentAction.ofRepresentableBy (SmoothProperCurve.specMap R R')
          (relSubPicPresheaf c ε (algEquivZeroCut c ε)) D'.toBase
          (AlgebraicGeometry.RelPicard.BaseChange.representableByRestrict c ε R' h')).act, ⟨pt, ?_⟩, ?_⟩
    · rw [Scheme.Hom.comp_apply, hpt]
    ·

      have hrbω : rb ≫ pullback.snd (D'.toBase ≫ SmoothProperCurve.specMap R R') (SmoothProperCurve.specMap R R') ≫
          SmoothProperCurve.specMap R R' = SmoothProperCurve.specMap R Ω := by
        rw [← pullback.condition, ← Category.assoc, hrbx, hω]
      have hyt : ((rb ≫ (DescentAction.ofRepresentableBy (SmoothProperCurve.specMap R R')
          (relSubPicPresheaf c ε (algEquivZeroCut c ε)) D'.toBase
          (AlgebraicGeometry.RelPicard.BaseChange.representableByRestrict c ε R' h')).act) ≫ D'.toBase) ≫
            SmoothProperCurve.specMap R R' = SmoothProperCurve.specMap R Ω := by
        rw [← hrbω, Category.assoc, Category.assoc, ← Category.assoc (DescentAction.act _), DescentAction.act_comp]

      let act := (DescentAction.ofRepresentableBy (SmoothProperCurve.specMap R R')
          (relSubPicPresheaf c ε (algEquivZeroCut c ε)) D'.toBase
          (AlgebraicGeometry.RelPicard.BaseChange.representableByRestrict c ε R' h')).act
      let y : Spec (CommRingCat.of Ω) ⟶ D'.P := rb ≫ act
      let t' : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R') := y ≫ D'.toBase
      have ht' : t' ≫ SmoothProperCurve.specMap R R' = SmoothProperCurve.specMap R Ω := hyt

      let σs : Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (SmoothProperCurve.baseChange R c R') :=
        fun j => σ (a j) (m₀ (a j))
      have hE : (Dγ i₀).I = prodKerGraph (SmoothProperCurve.baseChange R c R') (fun j => (σs j).1) (fun j => (σs j).2) :=
        hDγ ⟨a, ha⟩ m₀

      obtain ⟨eTD⟩ := AlgebraicGeometry.RelPicard.G2.nonempty_pullback_Ψ_inv_twist_iso c R' t' ht' ε r σs (Dγ i₀) hE
        ((hεinv t').pow r) (hDγinv i₀ t')

      have hmemv : ∀ j, ∃ ψ : B (a j) →ₐ[R] Ω,
          (AlgebraicGeometry.RelPicard.G2.v c R' t' ht' (σs j)).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) =
            Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z (a j) := fun j =>
        AlgebraicGeometry.RelPicard.G2.exists_algHom_v_fst_eq c R' t' ht' (z (a j)) (hz (a j)) (σs j) (hσ (a j) (m₀ (a j)))
      have hg := hgood (fun j => AlgebraicGeometry.RelPicard.G2.v c R' t' ht' (σs j)) hmemv

      obtain ⟨eL⟩ : Nonempty ((Scheme.Modules.pullback (AlgebraicGeometry.RelPicard.G2.Ψ c R' t' ht').inv).obj
          (L.pullbackAlong (⟨y, rfl⟩ : SchemeHomOver t' D'.toBase)).L ≅ L₀) := by

        let e1 : (Scheme.Modules.pullback (AlgebraicGeometry.RelPicard.G2.Ψ c R' t' ht').inv).obj
            (L.pullbackAlong (⟨y, rfl⟩ : SchemeHomOver t' D'.toBase)).L ≅
            (Scheme.Modules.pullback (pullback.congrHom rfl ht').inv).obj
              (AlgebraicGeometry.RelPicard.BaseChange.toR c ε R' (L.pullbackAlong (⟨y, rfl⟩ : SchemeHomOver t' D'.toBase))).L :=
          ((Scheme.Modules.pullbackComp (pullback.congrHom rfl ht').inv
            (AlgebraicGeometry.RelPicard.BaseChange.κ c R' t').inv).app _).symm
        let e2 := (Scheme.Modules.pullback (pullback.congrHom (rfl : c = c) ht').inv).mapIso
          (AlgebraicGeometry.RelPicard.BaseChange.toR_pullbackAlong_iso c ε R' (⟨y, rfl⟩ : SchemeHomOver t' D'.toBase) L).symm
        obtain ⟨e3⟩ := WGEN.nonempty_pullback_congrHom_inv_pullbackAlong_L_iso ht' 𝓛
          (AlgebraicGeometry.RelPicard.BaseChange.overR R' (⟨y, rfl⟩ : SchemeHomOver t' D'.toBase))
          (⟨y, by rw [← ht']; exact (Category.assoc _ _ _).symm⟩ :
            SchemeHomOver (SmoothProperCurve.specMap R Ω) (D'.toBase ≫ SmoothProperCurve.specMap R R'))
          rfl
        obtain ⟨e4⟩ := WGEN.nonempty_pullbackAlong_act_iso_pullbackAlong_fst R c ε R' D' h' 𝓛 h𝓛 rb
          (b := SmoothProperCurve.specMap R Ω) hrbω
        obtain ⟨e5⟩ := WGEN.nonempty_pullbackAlong_L_iso_of_val_eq 𝓛
          (⟨rb ≫ pullback.fst (D'.toBase ≫ SmoothProperCurve.specMap R R') (SmoothProperCurve.specMap R R'),
            by rw [Category.assoc, pullback.condition, hrbω]⟩ :
            SchemeHomOver (SmoothProperCurve.specMap R Ω) (D'.toBase ≫ SmoothProperCurve.specMap R R'))
          xb' hrbx
        exact ⟨e1 ≪≫ e2 ≪≫ e3 ≪≫ e4 ≪≫ e5⟩

      obtain ⟨eTw⟩ := hTw (⟨y, rfl⟩ : SchemeHomOver t' D'.toBase)
      have hIc : (((Dγ i₀).pullbackAlong D'.toBase (Category.comp_id _)).I).comap
          (baseChangeSnd (SmoothProperCurve.baseChange R c R') (⟨y, rfl⟩ : SchemeHomOver t' D'.toBase)) =
          ((Dγ i₀).pullbackAlong t' (Category.comp_id t')).I := by
        change ((Dγ i₀).I.comap _).comap _ = (Dγ i₀).I.comap _
        rw [← Scheme.IdealSheafData.comap_comp]
        congr 1
        apply pullback.hom_ext
        · simp only [baseChangeSnd, mapOnProdOver, pullback.map, Category.assoc, pullback.lift_fst,
            pullback.lift_fst_assoc, Category.comp_id]
        · simp only [baseChangeSnd, mapOnProdOver, pullback.map, Category.assoc, pullback.lift_snd,
            pullback.lift_snd_assoc, Category.comp_id]
          rfl
      haveI := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison
        (baseChangeSnd (SmoothProperCurve.baseChange R c R') (⟨y, rfl⟩ : SchemeHomOver t' D'.toBase))
        (hDγinv i₀ D'.toBase) (by rw [hIc]; exact hDγinv i₀ t')
      let eDbc : (Scheme.Modules.pullback (baseChangeSnd (SmoothProperCurve.baseChange R c R')
          (⟨y, rfl⟩ : SchemeHomOver t' D'.toBase))).obj ((Dγ i₀).pullbackAlong D'.toBase (Category.comp_id _)).idealModule ≅
          ((Dγ i₀).pullbackAlong t' (Category.comp_id t')).idealModule :=
        asIso ((((Dγ i₀).pullbackAlong D'.toBase (Category.comp_id _)).I).pullbackModuleComparison
          (baseChangeSnd (SmoothProperCurve.baseChange R c R') (⟨y, rfl⟩ : SchemeHomOver t' D'.toBase))) ≪≫
          eqToIso (by rw [hIc])

      let Mt : (pullback (SmoothProperCurve.baseChange R c R') t').Modules :=
        (L.pullbackAlong (⟨y, rfl⟩ : SchemeHomOver t' D'.toBase)).L ⊗
          (sectionTwist (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε) t' r ⊗
            ((Dγ i₀).pullbackAlong t' (Category.comp_id t')).idealModule)
      let F' : (pullback c (SmoothProperCurve.specMap R Ω)).Modules :=
        L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r).invModule ⊗
          (∏ j, (AlgebraicGeometry.RelPicard.G2.v c R' t' ht' (σs j)).1.ker).module)
      let eF1 : F' ≅ (Scheme.Modules.pullback (AlgebraicGeometry.RelPicard.G2.Ψ c R' t' ht').inv).obj Mt :=
        ((eL ⊗ᵢ eTD)).symm ≪≫ (Scheme.Modules.pullbackTensorObjIso _ _ _).symm
      let Φ : pullback (pullback.snd (SmoothProperCurve.baseChange R c R') D'.toBase) y ≅ pullback c (SmoothProperCurve.specMap R Ω) :=
        AlgebraicGeometry.RelPicard.G2.fibreIso (SmoothProperCurve.baseChange R c R') D'.toBase y t' rfl ≪≫
          AlgebraicGeometry.RelPicard.G2.Ψ c R' t' ht'
      have hΦ : Φ.hom ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) =
          fibreAt (SmoothProperCurve.baseChange R c R') D'.toBase y := by
        rw [Iso.trans_hom, Category.assoc, AlgebraicGeometry.RelPicard.G2.Ψ_hom_snd,
          AlgebraicGeometry.RelPicard.G2.fibreIso_hom_snd]
      let eF : fibreModule (SmoothProperCurve.baseChange R c R') D'.toBase y
          (L.L ⊗ (sectionTwist (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
            D'.toBase r ⊗ ((Dγ i₀).pullbackAlong D'.toBase (Category.comp_id _)).idealModule)) ≅
          (Scheme.Modules.pullback Φ.hom).obj F' :=
        AlgebraicGeometry.RelPicard.G2.fibreModuleTensorIso (SmoothProperCurve.baseChange R c R') D'.toBase y t' rfl _ _ ≪≫
          (Scheme.Modules.pullback (AlgebraicGeometry.RelPicard.G2.fibreIso (SmoothProperCurve.baseChange R c R')
            D'.toBase y t' rfl).hom).mapIso
            (whiskerLeftIso _ (Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (eTw ⊗ᵢ eDbc)) ≪≫
              AlgebraicGeometry.RelPicard.G2.isoPullbackInvOfIso (AlgebraicGeometry.RelPicard.G2.Ψ c R' t' ht').symm eF1) ≪≫
          (Scheme.Modules.pullbackComp _ _).app F'
      intro 𝒲
      exact AlgebraicGeometry.RelPicard.G2.forall_subsingleton_H1_fibre_of_iso (SmoothProperCurve.baseChange R c R')
        D'.toBase y Φ (pullback.snd c (SmoothProperCurve.specMap R Ω)) hΦ _ F' eF hg 𝒲

  let act := (DescentAction.ofRepresentableBy (SmoothProperCurve.specMap R R')
    (relSubPicPresheaf c ε (algEquivZeroCut c ε)) D'.toBase
    (AlgebraicGeometry.RelPicard.BaseChange.representableByRestrict c ε R' h')).act
  let S : Finset D'.P := hfinorb.toFinset.image act
  have hS : ∀ sP ∈ S, ∃ (k : Type u) (_ : Field k) (y : Spec (CommRingCat.of k) ⟶ D'.P) (φ' : Spec (CommRingCat.of k) ⟶ X i₀),
      sP ∈ Set.range y ∧ uliftYoneda.{u + 1}.map φ' ≫ f i₀ = uliftYoneda.{u + 1}.map y ≫ x := by
    intro sP hsP
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hsP
    have hq' : pullback.fst (D'.toBase ≫ SmoothProperCurve.specMap R R') (SmoothProperCurve.specMap R R') q = xP := by
      simpa using hq
    obtain ⟨y, hy, hH⟩ := key q hq'
    obtain ⟨φ', hφ'⟩ := hmem' i₀ y hH
    exact ⟨Ω, inferInstance, y, φ', hy, hφ'⟩
  obtain ⟨W, hW, hSW⟩ := AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_forall_exists_lift_chart _ x (f i₀) (hf i₀)
    (hfin i₀) S hS
  refine ⟨W, hW, fun q hq => hSW _ (Finset.mem_image.mpr ⟨q, ?_, rfl⟩)⟩
  simpa using hq

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.CategoryTheory.Functor.RepresentableBy P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible.AlgebraicGeometry.RelPicard.G2"

end S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_forall_exists_isAffineOpen_forall_act_mem_of_blocks_of_isInvertible (solution)
