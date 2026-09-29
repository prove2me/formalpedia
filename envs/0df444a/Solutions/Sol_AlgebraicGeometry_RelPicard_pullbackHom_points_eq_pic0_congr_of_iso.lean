-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.pullbackHom_points_eq_pic0_congr_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/45d9b93b-2a51-5fcf-b890-f6975135b742

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_mul_comp_eq_of_classifies_rigidify_pullback_of_ofPoint_of_isIso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_pullbackHom_points_eq_pic0_congr_of_iso
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicCurve"

universe u v

namespace PtsIntertwineIso

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

noncomputable def gen (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ P : Place K F) : Divisor.degZero (K := K) (F := F) :=
  ⟨Finsupp.single P 1 - Finsupp.single Q₀ 1, by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg, hdeg]; simp⟩

@[scoped simp] theorem coe_gen (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ P : Place K F) :
    (gen hdeg Q₀ P : Divisor K F) = Finsupp.single P 1 - Finsupp.single Q₀ 1 := rfl

theorem closure_range_mk_gen_eq_top (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ : Place K F) :
    AddSubgroup.closure (Set.range fun P : Place K F => Pic0.mk (gen hdeg Q₀ P)) = ⊤ := by
  classical
  set S := AddSubgroup.closure (Set.range fun P : Place K F => Pic0.mk (gen hdeg Q₀ P)) with hS
  let θ : Divisor K F →+ Divisor K F :=
    AddMonoidHom.id _ - (zmultiplesHom (Divisor K F) (Finsupp.single Q₀ 1)).comp Divisor.degree
  have hθ : ∀ E : Divisor K F, θ E = E - Divisor.degree E • Finsupp.single Q₀ 1 := fun E => by
    simp [θ]
  have hθmem : ∀ E : Divisor K F, θ E ∈ Divisor.degZero (K := K) (F := F) := by
    intro E
    rw [Divisor.mem_degZero, hθ, map_sub, map_zsmul, Divisor.degree_single, hdeg]
    simp
  let ψ : Divisor K F →+ Pic0 K F := (QuotientAddGroup.mk' _).comp (θ.codRestrict _ hθmem)
  have hψ : ∀ E : Divisor K F, ψ E = Pic0.mk ⟨θ E, hθmem E⟩ := fun E => rfl
  have hψS : ∀ E : Divisor K F, ψ E ∈ S := by
    intro E
    induction E using Finsupp.induction with
    | zero => rw [map_zero]; exact S.zero_mem
    | single_add a b f _ _ ih =>
      rw [map_add]
      refine S.add_mem ?_ ih
      have h1 : ψ (Finsupp.single a 1) = Pic0.mk (gen hdeg Q₀ a) := by
        rw [hψ]; congr 1; apply Subtype.ext
        simp only [coe_gen, hθ, Divisor.degree_single, hdeg, Nat.cast_one, mul_one, one_smul]
      have hb : Finsupp.single a b = b • Finsupp.single a (1 : ℤ) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hb, map_zsmul, h1]
      exact S.zsmul_mem (AddSubgroup.subset_closure ⟨a, rfl⟩) b
  rw [eq_top_iff]
  rintro c -
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  have hD : Pic0.mk D = ψ (D : Divisor K F) := by
    rw [hψ]; congr 1; apply Subtype.ext
    simp only [hθ, (Divisor.mem_degZero.mp D.2), zero_smul, sub_zero]
  rw [hD]; exact hψS _

theorem addMonoidHom_ext_of_gen {G : Type*} [AddGroup G] (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ : Place K F)
    {f g : Pic0 K F →+ G} (h : ∀ P : Place K F, f (Pic0.mk (gen hdeg Q₀ P)) = g (Pic0.mk (gen hdeg Q₀ P))) :
    f = g :=
  AddMonoidHom.eq_of_eqOn_dense (closure_range_mk_gen_eq_top hdeg Q₀) (by rintro _ ⟨P, rfl⟩; exact h P)

end Generic

end PtsIntertwineIso
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_pullbackHom_points_eq_pic0_congr_of_iso.PtsIntertwineIso"

open PtsIntertwineIso

namespace RepIsoPII

section PullbackHomMul

open scoped CategoryTheory.MonObj

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
  {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}

theorem nonempty_tensor_pullbackCurve_iso (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (L M : RigidifiedLineBundle c ε t) :
    Nonempty (((L.tensor M).pullbackCurve f hf hε).L ≅ ((L.pullbackCurve f hf hε).tensor (M.pullbackCurve f hf hε)).L) :=
  ⟨Scheme.Modules.pullbackTensorObjIso _ _ _⟩

theorem nonempty_pullbackAlong_mul_iso (P : SubPicGroupCondition c ε) (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : SchemeHomOver t D.toBase) :
    Nonempty ((h.poincare.pullbackAlong (h.relativeGroupLaw.mul t a b)).L ≅
      ((h.poincare.pullbackAlong a).tensor (h.poincare.pullbackAlong b)).L) := by
  letI := h.grpObj
  letI := P.commGroupObj (Opposite.op (Over.mk t))
  have key := congrArg Subtype.val (h.homEquiv_mul (Over.mk t) (schemeHomOverToOverHom a) (schemeHomOverToOverHom b))

  have hl : (h.representableBy.homEquiv (schemeHomOverToOverHom a * schemeHomOverToOverHom b)).1 =
      Quotient.mk _ (h.poincare.pullbackAlong (h.relativeGroupLaw.mul t a b)) := rfl
  have hr : ((h.representableBy.homEquiv (schemeHomOverToOverHom a)) *
      (h.representableBy.homEquiv (schemeHomOverToOverHom b))).1 =
      Quotient.mk _ ((h.poincare.pullbackAlong a).tensor (h.poincare.pullbackAlong b)) := rfl
  rw [hl, hr] at key
  exact Quotient.exact key

theorem nonempty_pullbackAlong_postComp_pullbackHom_iso (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t D.toBase) :
    Nonempty ((h'.poincare.pullbackAlong (postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') x)).L ≅
      ((h.poincare.pullbackAlong x).pullbackCurve f hf hε).L) := by
  have hPx : (algEquivZeroCut c ε).P t (h.poincare.pullbackAlong x) :=
    (algEquivZeroCut c ε).pullback_mem _ _ x _ h.poincare_mem
  have hx : x = h.classify t (h.poincare.pullbackAlong x) hPx := h.classify_unique t _ hPx x ⟨Iso.refl _⟩
  have hx' : postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') x =
      h'.classify t ((h.poincare.pullbackAlong x).pullbackCurve f hf hε)
        (FibrewiseAlgEquivZero.pullbackCurve f hf hε hPx) := by
    conv_lhs => rw [hx]
    exact RepresentsRelSubPic.postComp_pullbackHom_classify f hf hε h h' t _ hPx
  rw [hx']
  exact h'.classify_spec t _ _

theorem postComp_pullbackHom_mul (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : SchemeHomOver t D.toBase) :
    postComp (RepresentsRelSubPic.pullbackHom f hf hε h h')
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t a b) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c' ε') h').mul t
        (postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') a)
        (postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') b) := by
  refine h'.ext_of_iso t _ _ ?_
  obtain ⟨i1⟩ := nonempty_pullbackAlong_postComp_pullbackHom_iso f hf hε h h' t
    ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t a b)
  obtain ⟨i2⟩ := nonempty_pullbackAlong_mul_iso (algEquivZeroGroupCut c ε) h t a b
  obtain ⟨i3⟩ := nonempty_tensor_pullbackCurve_iso f hf hε (h.poincare.pullbackAlong a) (h.poincare.pullbackAlong b)
  obtain ⟨ia⟩ := nonempty_pullbackAlong_postComp_pullbackHom_iso f hf hε h h' t a
  obtain ⟨ib⟩ := nonempty_pullbackAlong_postComp_pullbackHom_iso f hf hε h h' t b
  obtain ⟨i4⟩ := nonempty_pullbackAlong_mul_iso (algEquivZeroGroupCut c' ε') h' t
    (postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') a) (postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') b)
  exact ⟨i1 ≪≫ (Scheme.Modules.pullback _).mapIso i2 ≪≫ i3 ≪≫ (ia.symm ⊗ᵢ ib.symm) ≪≫ i4.symm⟩

end PullbackHomMul
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_pullbackHom_points_eq_pic0_congr_of_iso.PtsIntertwineIso"

end RepIsoPII
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_pullbackHom_points_eq_pic0_congr_of_iso.PtsIntertwineIso"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (R : Type u) [CommRing R]
    {C C' : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (c' : C' ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    [IsProper c'] [SmoothOfRelativeDimension 1 c'] [GeometricallyIntegral c']
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c')
    (f : C' ≅ C) (hf : f.hom ≫ c = c') (hε : ε'.1 ≫ f.hom = ε.1)
    (D : RelativePic0Designation R c) (D' : RelativePic0Designation R c')
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    (aj : SchemeHomOver c D.toBase) (aj' : SchemeHomOver c' D'.toBase)
    (haj : ∀ (K : Type u) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t c),
        Nonempty ((h.poincare.pullbackAlong
            ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (haj' : ∀ (K : Type u) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t c'),
        Nonempty ((h'.poincare.pullbackAlong
            ⟨x.1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj'.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c' x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c' (t ≫ ε'.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε'.2).trans (Category.comp_id t)))).idealModule))
    (K : Type u) [Field K] [IsAlgClosed K] (i : R →+* K)
    (F F' : Type v) [Field F] [Field F'] [Algebra K F] [Algebra K F'] [IsCurveOver K F] [IsCurveOver K F']
    (eF : F ≃+* F') (heF : ∀ a : K, eF (algebraMap K F a) = algebraMap K F' a)
    (M : CurveModel K F) (M' : CurveModel K F')
    (e : M.C ⟶ pullback c (Spec.map (CommRingCat.ofHom i))) [IsIso e]
    (he : e ≫ pullback.snd c (Spec.map (CommRingCat.ofHom i)) = M.toBase)
    (e' : M'.C ⟶ pullback c' (Spec.map (CommRingCat.ofHom i))) [IsIso e']
    (he' : e' ≫ pullback.snd c' (Spec.map (CommRingCat.ofHom i)) = M'.toBase)

    (hfK : ∀ (y : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
      x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) =
        y.1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i)) ≫ f.hom →
      M'.pointEquivPlace y = AlgebraicCurve.Place.congrRingEquiv eF heF (M.pointEquivPlace x))
    (pts : Pic0 K F ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D.toBase)
    (hadd : ∀ x y : Pic0 K F,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul (Spec.map (CommRingCat.ofHom i)) (pts x) (pts y))
    (hnorm : ∀ (x s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
      s.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) =
        Spec.map (CommRingCat.ofHom i) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := K) (F := F),
        (Dv : Divisor K F) =
          Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 =
          x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) ≫ aj.1)
    (pts' : Pic0 K F' ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D'.toBase)
    (hadd' : ∀ x y : Pic0 K F',
      pts' (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c' ε') h').mul (Spec.map (CommRingCat.ofHom i)) (pts' x) (pts' y))
    (hnorm' : ∀ (x s : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _}),
      s.1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i)) =
        Spec.map (CommRingCat.ofHom i) ≫ ε'.1 →
      ∃ Dv : Divisor.degZero (K := K) (F := F'),
        (Dv : Divisor K F') =
          Finsupp.single (M'.pointEquivPlace x) 1 - Finsupp.single (M'.pointEquivPlace s) 1 ∧
        (pts' (Pic0.mk Dv)).1 =
          x.1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i)) ≫ aj'.1) :
    ∀ z : Pic0 K F,
      (pts' (Pic0.congr eF heF z)).1 = (pts z).1 ≫ (RepresentsRelSubPic.pullbackHom f.hom hf hε h h').1 := by
  classical

  let L' := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c' ε') h'
  let N : SchemeHomOver D.toBase D'.toBase := RepresentsRelSubPic.pullbackHom f.hom hf hε h h'
  have hfinv : f.inv ≫ c' = c := by rw [← hf, Iso.inv_hom_id_assoc]
  have hεinv : ε.1 ≫ f.inv = ε'.1 := by rw [← hε, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hinve : inv e ≫ M.toBase = pullback.snd c (Spec.map (CommRingCat.ofHom i)) := by rw [IsIso.inv_comp_eq, he]
  have hinve' : inv e' ≫ M'.toBase = pullback.snd c' (Spec.map (CommRingCat.ofHom i)) := by rw [IsIso.inv_comp_eq, he']

  let X : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _} → SchemeHomOver (Spec.map (CommRingCat.ofHom i)) c := fun x ↦
    ⟨x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)), by
      rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% he, reassoc_of% x.2]⟩
  let X' : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _} → SchemeHomOver (Spec.map (CommRingCat.ofHom i)) c' := fun y ↦
    ⟨y.1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i)), by
      rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% he', reassoc_of% y.2]⟩

  let under : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _} →
      {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _} := fun x ↦
    ⟨pullback.lift (x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) ≫ f.inv) (x.1 ≫ e ≫ pullback.snd c (Spec.map (CommRingCat.ofHom i)))
        (by simp only [Category.assoc, hfinv]; rw [pullback.condition]) ≫ inv e', by
      rw [Category.assoc, hinve', pullback.lift_snd, he]; exact x.2⟩
  have hunder : ∀ x, (under x).1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i)) = x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) ≫ f.inv := by
    intro x; simp only [under, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]
  have hunder' : ∀ x, x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) = (under x).1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i)) ≫ f.hom := by
    intro x; rw [reassoc_of% (hunder x)]; simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

  let s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _} :=
    ⟨pullback.lift ((Spec.map (CommRingCat.ofHom i)) ≫ ε.1) (𝟙 _) (by rw [Category.assoc, ε.2, Category.comp_id, Category.id_comp]) ≫ inv e, by
      rw [Category.assoc, hinve, pullback.lift_snd]⟩
  have hs : s.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) = (Spec.map (CommRingCat.ofHom i)) ≫ ε.1 := by
    simp only [s, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]
  have hs' : (under s).1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i)) = (Spec.map (CommRingCat.ofHom i)) ≫ ε'.1 := by
    rw [hunder, reassoc_of% hs, hεinv]

  let Φ : Pic0 K F → Pic0 K F' := fun z ↦ pts'.symm (NeronModelInfra.schemeHomOverComp (pts z) N)
  have hΦ : ∀ z, pts' (Φ z) = NeronModelInfra.schemeHomOverComp (pts z) N := fun z ↦ pts'.apply_symm_apply _
  have hNhom : ∀ x y : SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D.toBase,
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul _ x y) N =
        L'.mul _ (NeronModelInfra.schemeHomOverComp x N) (NeronModelInfra.schemeHomOverComp y N) :=
    fun x y ↦ RepIsoPII.postComp_pullbackHom_mul f.hom hf hε h h' (Spec.map (CommRingCat.ofHom i)) x y
  have hΦadd : ∀ z w, Φ (z + w) = Φ z + Φ w := by
    intro z w; apply pts'.injective
    rw [hadd', hΦ, hΦ, hΦ, hadd, hNhom]
  let Φh : Pic0 K F →+ Pic0 K F' := AddMonoidHom.mk' Φ hΦadd
  suffices hfun : (Pic0.congr eF heF).toAddMonoidHom = Φh by
    intro z
    have h1 : Pic0.congr eF heF z = Φ z := DFunLike.congr_fun hfun z
    rw [h1]; show (pts' (Φ z)).1 = _; rw [hΦ]; rfl

  have hdeg : ∀ v : Place K F, v.deg = 1 := fun v ↦ AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed v
  refine addMonoidHom_ext_of_gen hdeg (M.pointEquivPlace s) fun P ↦ ?_
  obtain ⟨x, hPx⟩ := M.pointEquivPlace.surjective P
  subst hPx

  obtain ⟨Dv, hDv, hptsDv⟩ := hnorm x s hs
  obtain ⟨Dv', hDv', hptsDv'⟩ := hnorm' (under x) (under s) hs'
  obtain ⟨Dv₀, hDv₀, hptsDv₀⟩ := hnorm' (under s) (under s) hs'
  have hgen : gen hdeg (M.pointEquivPlace s) (M.pointEquivPlace x) = Dv := Subtype.ext (by rw [coe_gen, hDv])

  have hcongr : Pic0.congr eF heF (Pic0.mk (gen hdeg (M.pointEquivPlace s) (M.pointEquivPlace x))) = Pic0.mk Dv' := by
    show Pic0.mk (Pic0.degZeroCongr eF heF _) = _
    congr 1
    apply Subtype.ext
    rw [Pic0.coe_degZeroCongr, coe_gen, map_sub, Divisor.congr_single, Divisor.congr_single,
      ← hfK (under x) x (hunder' x), ← hfK (under s) s (hunder' s), hDv']

  haveI : IsSeparated c := inferInstance
  haveI : IsSeparated c' := inferInstance
  let a : SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D.toBase :=
    ⟨(X x).1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg ((X x).1 ≫ ·) aj.2).trans (X x).2)⟩
  let b : SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D'.toBase :=
    ⟨(X' (under s)).1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg ((X' (under s)).1 ≫ ·) aj'.2).trans (X' (under s)).2)⟩
  let g : SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D'.toBase :=
    ⟨(X' (under x)).1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg ((X' (under x)).1 ≫ ·) aj'.2).trans (X' (under x)).2)⟩
  have hmul : L'.mul (Spec.map (CommRingCat.ofHom i)) (NeronModelInfra.schemeHomOverComp a N) b = g :=
    AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mul_comp_eq_of_classifies_rigidify_pullback_of_ofPoint_of_isIso
      h h' f.hom hf N
      (fun t' a' ↦ AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify
        f.hom hf hε h h' t' a')
      (Spec.map (CommRingCat.ofHom i)) (X x) (X' (under x)) (X' (under s))
      (by show ((under x).1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i))) ≫ f.hom = x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i))
          simp only [Category.assoc]; exact (hunder' x).symm)
      (by show ((under s).1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i))) ≫ f.hom = (Spec.map (CommRingCat.ofHom i)) ≫ ε.1
          simp only [Category.assoc]; rw [← hunder' s, hs])
      a (haj K (Spec.map (CommRingCat.ofHom i)) (X x)) b g (haj' K (Spec.map (CommRingCat.ofHom i)) (X' (under s))) (haj' K (Spec.map (CommRingCat.ofHom i)) (X' (under x)))

  have hb0 : b = pts' 0 := by
    have h0 : Pic0.mk Dv₀ = 0 := by
      rw [show Dv₀ = 0 from Subtype.ext (by rw [hDv₀, sub_self]; rfl), Pic0.mk_zero]
    apply Subtype.ext
    rw [← h0, hptsDv₀]
    show ((under s).1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i))) ≫ aj'.1 = _
    simp only [Category.assoc]

  have hkey : NeronModelInfra.schemeHomOverComp a N = g := by
    rw [← hmul, hb0, ← pts'.apply_symm_apply (NeronModelInfra.schemeHomOverComp a N), ← hadd', add_zero]

  show Pic0.congr eF heF (Pic0.mk _) = Φ _
  apply pts'.injective
  rw [hΦ, hcongr]
  apply Subtype.ext
  rw [hptsDv', NeronModelInfra.schemeHomOverComp_coe, hgen, hptsDv]
  have hkey1 := congrArg Subtype.val hkey
  simp only [NeronModelInfra.schemeHomOverComp_coe, a, g, X, X', Category.assoc] at hkey1
  simp only [Category.assoc]
  exact hkey1.symm

end S_AlgebraicGeometry_RelPicard_pullbackHom_points_eq_pic0_congr_of_iso
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_pullbackHom_points_eq_pic0_congr_of_iso (solution)
