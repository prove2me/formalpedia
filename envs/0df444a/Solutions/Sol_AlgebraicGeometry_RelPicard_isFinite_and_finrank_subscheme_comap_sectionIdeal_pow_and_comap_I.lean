-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.isFinite_and_finrank_subscheme_comap_sectionIdeal_pow_and_comap_I
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/83f5af88-9e32-53cd-aaa9-8c5e021ed263

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_iso_subscheme_comap_of_support_subset_range
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isFinite_and_finrank_subscheme_comap_sectionIdeal_pow_and_comap_I
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero"
p2m_attr_erase "simp" "AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve NeronModelInfra"

noncomputable section

namespace ChildB

variable {R : Type u} [CommRing R]

section FibreIso

variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
  {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
  (hx : s ≫ t = x)

def fibreIso : pullback (pullback.snd c t) s ≅ pullback c x :=
  pullbackLeftPullbackSndIso c t s ≪≫ pullback.congrHom rfl hx

@[reassoc]
theorem fibreIso_hom_snd : (fibreIso c t s x hx).hom ≫ pullback.snd c x = fibreAt c t s := by
  subst hx
  simp [fibreIso, fibreAt, pullback.congrHom_hom]

@[reassoc]
theorem fibreIso_hom_fst :
    (fibreIso c t s x hx).hom ≫ pullback.fst c x = pullback.fst (pullback.snd c t) s ≫ pullback.fst c t := by
  subst hx
  simp [fibreIso, pullback.congrHom_hom]

theorem fibreIso_inv_fibreAt : (fibreIso c t s x hx).inv ≫ fibreAt c t s = pullback.snd c x := by
  rw [← fibreIso_hom_snd c t s x hx, Iso.inv_hom_id_assoc]

theorem fibreIso_hom_baseChangeSnd :
    (fibreIso c t s x hx).hom ≫ baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t)
      = pullback.fst (pullback.snd c t) s := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    unfold baseChangeSnd
    rw [pullback.lift_fst, ← Category.assoc, fibreIso_hom_fst, Category.assoc, Category.comp_id]
  · rw [Category.assoc]
    unfold baseChangeSnd
    rw [pullback.lift_snd, ← Category.assoc, fibreIso_hom_snd, pullback.condition]
    rfl

end FibreIso

theorem comap_pow {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (n : ℕ) :
    (I ^ n).comap f = (I.comap f) ^ n := by
  induction n with
  | zero => simp [Scheme.IdealSheafData.comap_top]
  | succ n ih => rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

variable {R : Type u} [CommRing R] {C : Scheme.{u}}

theorem sectionIdeal_comap (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) :
    (RelPicard.sectionIdeal c ε t).comap (RelPicard.baseChangeSnd c ψ) =
      RelPicard.sectionIdeal c ε t' := by
  have hpt : (t ≫ ε.1) ≫ c = t := by rw [Category.assoc, ε.2, Category.comp_id]
  have hpt'' : (t' ≫ ε.1) ≫ c = t' := by rw [Category.assoc, ε.2, Category.comp_id]
  have hpt' : ψ.1 ≫ t ≫ ε.1 = t' ≫ ε.1 := by rw [← Category.assoc, ψ.2]
  have key := congrArg RelEffCartierDiv.I
    (RelEffCartierDiv.pullbackAlong_ofPoint c (t ≫ ε.1) hpt ψ.1 ψ.2)
  have e₁ : RelPicard.sectionIdeal c ε t = (RelEffCartierDiv.ofPoint c (t ≫ ε.1) hpt).I := rfl
  have e₂ : RelPicard.sectionIdeal c ε t' = (RelEffCartierDiv.ofPoint c (t' ≫ ε.1) hpt'').I := rfl
  have e₃ : (RelEffCartierDiv.ofPoint c (t ≫ ε.1) hpt).I.comap (RelPicard.baseChangeSnd c ψ) =
      ((RelEffCartierDiv.ofPoint c (t ≫ ε.1) hpt).pullbackAlong ψ.1 ψ.2).I := rfl
  rw [e₁, e₂, e₃, key]
  simp only [hpt']

theorem exists_sectionU (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1 ⊆ (U : Set C))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    ∃ σU : T ⟶ pullback (U.ι ≫ c) t,
      σU ≫ pullback.snd (U.ι ≫ c) t = 𝟙 T ∧
      (RelPicard.sectionIdeal c ε t).comap (pullback.map (U.ι ≫ c) t c t U.ι (𝟙 T) (𝟙 _) (by simp) (by simp)) = σU.ker ∧
      ((RelPicard.sectionIdeal c ε t).support : Set ↥(pullback c t)) ⊆
        Set.range (pullback.map (U.ι ≫ c) t c t U.ι (𝟙 T) (𝟙 _) (by simp) (by simp)) := by
  set j := pullback.map (U.ι ≫ c) t c t U.ι (𝟙 T) (𝟙 _) (by simp) (by simp) with hj
  let εU : Spec (CommRingCat.of R) ⟶ (U : Scheme.{u}) :=
    IsOpenImmersion.lift U.ι ε.1 (by rwa [Scheme.Opens.range_ι])
  have hεU' : εU ≫ U.ι = ε.1 := IsOpenImmersion.lift_fac _ _ _
  set σU : T ⟶ pullback (U.ι ≫ c) t := pullback.lift (t ≫ εU) (𝟙 T)
    (by rw [Category.assoc, ← Category.assoc εU, hεU', ε.2, Category.comp_id, Category.id_comp]) with hσUdef
  have hσU : σU ≫ pullback.snd (U.ι ≫ c) t = 𝟙 T := by rw [hσUdef, pullback.lift_snd]
  have hσj : σU ≫ j = RelPicard.rigSection c t ε := by
    apply pullback.hom_ext
    · simp only [RelPicard.rigSection, hj, Category.assoc, pullback.lift_fst]
      rw [hσUdef, pullback.lift_fst_assoc, Category.assoc, hεU']
    · simp only [RelPicard.rigSection, hj, Category.assoc, pullback.lift_snd, Category.comp_id]
      exact hσU
  haveI : IsClosedImmersion (RelPicard.rigSection c t ε) := by
    have : IsClosedImmersion (RelPicard.rigSection c t ε ≫ pullback.snd c t) := by
      rw [RelPicard.rigSection, pullback.lift_snd]; infer_instance
    exact .of_comp (RelPicard.rigSection c t ε) (pullback.snd c t)
  have hcomap : (RelPicard.sectionIdeal c ε t).comap j = σU.ker := by
    change (RelPicard.rigSection c t ε).ker.comap j = σU.ker
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    have hsurj : IsIso (pullback.snd j (RelPicard.rigSection c t ε)) := by
      refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
      ext z
      simp only [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      rw [Scheme.Pullback.range_snd, ← hσj]
      exact ⟨σU z, (Scheme.Hom.comp_apply _ _ z).symm⟩
    have hfst : pullback.fst j (RelPicard.rigSection c t ε) = pullback.snd j (RelPicard.rigSection c t ε) ≫ σU := by
      rw [← cancel_mono j, Category.assoc, hσj]
      exact pullback.condition
    rw [hfst, Scheme.Hom.ker_comp_of_isIso]
  refine ⟨σU, hσU, hcomap, ?_⟩
  change ((RelPicard.rigSection c t ε).ker.support : Set ↥(pullback c t)) ⊆ Set.range ⇑j
  rw [Scheme.Hom.support_ker, (RelPicard.rigSection c t ε).isClosedEmbedding.isClosed_range.closure_eq, ← hσj]
  rintro _ ⟨z, rfl⟩
  exact ⟨σU z, (Scheme.Hom.comp_apply _ _ z).symm⟩

theorem transport_line {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {k : Type u} [Field k] (pt : Spec (CommRingCat.of k) ⟶ T)
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k)) (i₁ : Y ⟶ pullback (pullback.snd c t) pt)
    (hi₁ : i₁ ≫ fibreAt c t pt = y)
    (W₁ : (pullback (pullback.snd c t) pt).Opens) [IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁)]
    (hW₁ : (W₁ : Set ↥(pullback (pullback.snd c t) pt)) ⊆ Set.range i₁.base)
    (K : (pullback c t).IdealSheafData)
    (hW : ∀ z : ↥(pullback (pullback.snd c t) pt), (pullback.fst (pullback.snd c t) pt).base z ∈ K.support → z ∈ W₁)
    (K' : (pullback (pullback.snd c t) pt).IdealSheafData) (hK' : K' = K.comap (pullback.fst (pullback.snd c t) pt))
    {n : ℕ} (hfin : IsFinite (K'.subschemeι ≫ fibreAt c t pt))
    (hdeg : ∀ q : Spec (CommRingCat.of k), (K'.subschemeι ≫ fibreAt c t pt).finrank q = n) :
    IsFinite ((K.comap (i₁ ≫ pullback.fst (pullback.snd c t) pt)).subschemeι ≫ y) ∧
      ∀ q : Spec (CommRingCat.of k), ((K.comap (i₁ ≫ pullback.fst (pullback.snd c t) pt)).subschemeι ≫ y).finrank q = n := by
  subst hK'
  set Kψ := K.comap (i₁ ≫ pullback.fst (pullback.snd c t) pt) with hKψ

  have h1 : (Kψ.support : Set Y) ⊆ Set.range (i₁ ⁻¹ᵁ W₁).ι := by
    intro x hx
    rw [hKψ, Scheme.IdealSheafData.support_comap] at hx
    rw [Scheme.Opens.range_ι]
    exact hW (i₁.base x) hx
  obtain ⟨e₁, he₁⟩ := Scheme.IdealSheafData.exists_iso_subscheme_comap_of_support_subset_range Kψ (i₁ ⁻¹ᵁ W₁).ι h1

  have hcomp : (K.comap (pullback.fst (pullback.snd c t) pt)).comap ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁) = Kψ.comap (i₁ ⁻¹ᵁ W₁).ι := by
    rw [hKψ, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, Category.assoc]
  have h2 : ((K.comap (pullback.fst (pullback.snd c t) pt)).support : Set ↥(pullback (pullback.snd c t) pt)) ⊆
      Set.range ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁) := by
    intro z hz
    rw [Scheme.IdealSheafData.support_comap] at hz
    have hzW : z ∈ W₁ := hW z hz
    obtain ⟨y0, hy0⟩ := hW₁ hzW
    have hy0W : y0 ∈ i₁ ⁻¹ᵁ W₁ := by
      show i₁.base y0 ∈ W₁
      rw [hy0]; exact hzW
    exact ⟨⟨y0, hy0W⟩, by rw [Scheme.Hom.comp_apply]; exact hy0⟩
  have h3 := Scheme.IdealSheafData.exists_iso_subscheme_comap_of_support_subset_range
    (K.comap (pullback.fst (pullback.snd c t) pt)) ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁) h2
  rw [hcomp] at h3
  obtain ⟨e₂, he₂⟩ := h3

  have hfac : Kψ.subschemeι ≫ y = (e₁.inv ≫ e₂.hom) ≫
      ((K.comap (pullback.fst (pullback.snd c t) pt)).subschemeι ≫ fibreAt c t pt) := by
    have hι : Kψ.subschemeι = e₁.inv ≫ (Kψ.comap (i₁ ⁻¹ᵁ W₁).ι).subschemeι ≫ (i₁ ⁻¹ᵁ W₁).ι := by
      rw [← he₁, Iso.inv_hom_id_assoc]
    rw [← hi₁, hι]
    simp only [Category.assoc]
    rw [← Category.assoc e₂.hom, he₂]
    simp only [Category.assoc]
  refine ⟨?_, ?_⟩
  · rw [hfac]
    haveI := hfin
    infer_instance
  · intro q
    rw [hfac, Scheme.Hom.finrank_comp_left_of_isIso]
    exact hdeg q

theorem transport_fibreIso {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {k : Type u} [Field k] (pt : Spec (CommRingCat.of k) ⟶ T)
    (Kk : (pullback c (pt ≫ t)).IdealSheafData) {n : ℕ}
    (hfin : IsFinite (Kk.subschemeι ≫ pullback.snd c (pt ≫ t)))
    (hdeg : ∀ q : Spec (CommRingCat.of k), (Kk.subschemeι ≫ pullback.snd c (pt ≫ t)).finrank q = n) :
    IsFinite ((Kk.comap (fibreIso c t pt (pt ≫ t) rfl).hom).subschemeι ≫ fibreAt c t pt) ∧
      ∀ q : Spec (CommRingCat.of k),
        ((Kk.comap (fibreIso c t pt (pt ≫ t) rfl).hom).subschemeι ≫ fibreAt c t pt).finrank q = n := by
  obtain ⟨e, he⟩ := Scheme.IdealSheafData.exists_iso_subscheme_comap_of_support_subset_range Kk
    (fibreIso c t pt (pt ≫ t) rfl).hom (by
      intro z _
      exact ⟨(fibreIso c t pt (pt ≫ t) rfl).inv.base z, by
        rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl⟩)
  have hfac : (Kk.comap (fibreIso c t pt (pt ≫ t) rfl).hom).subschemeι ≫ fibreAt c t pt =
      e.hom ≫ (Kk.subschemeι ≫ pullback.snd c (pt ≫ t)) := by
    rw [← fibreIso_hom_snd c t pt (pt ≫ t) rfl, ← Category.assoc, ← he, Category.assoc]
  refine ⟨?_, ?_⟩
  · rw [hfac]; haveI := hfin; infer_instance
  · intro q; rw [hfac, Scheme.Hom.finrank_comp_left_of_isIso]; exact hdeg q

end ChildB

open ChildB in
theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1 ⊆ (U : Set C))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (r : ℕ) {e : ℕ} (D : RelEffCartierDiv c e t) (hDU : D.SupportedIn U)
    {k : Type u} [Field k] (pt : Spec (CommRingCat.of k) ⟶ T)
    {F₁ : Type u} [Field F₁] [Algebra k F₁] (M₁ : CurveModel k F₁)
    (i₁ : M₁.C ⟶ pullback (pullback.snd c t) pt) (hi₁ : i₁ ≫ fibreAt c t pt = M₁.toBase)
    (W₁ : (pullback (pullback.snd c t) pt).Opens) [IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁)]
    (hW₁ : (W₁ : Set ↥(pullback (pullback.snd c t) pt)) ⊆ Set.range i₁.base)
    (hD : ∀ y : ↥(pullback (pullback.snd c t) pt), (pullback.fst (pullback.snd c t) pt).base y ∈ D.I.support → y ∈ W₁)
    (hε : ∀ y : ↥(pullback (pullback.snd c t) pt), (pullback.fst (pullback.snd c t) pt).base y ∈ Set.range (rigSection c t ε).base → y ∈ W₁) :
    IsFinite ((((sectionIdeal c ε t) ^ r).comap (i₁ ≫ pullback.fst (pullback.snd c t) pt)).subschemeι ≫ M₁.toBase) ∧
      (∀ q : Spec (CommRingCat.of k),
        ((((sectionIdeal c ε t) ^ r).comap (i₁ ≫ pullback.fst (pullback.snd c t) pt)).subschemeι ≫ M₁.toBase).finrank q = r) ∧
      IsFinite (((D.I.comap (i₁ ≫ pullback.fst (pullback.snd c t) pt))).subschemeι ≫ M₁.toBase) ∧
      (∀ q : Spec (CommRingCat.of k),
        (((D.I.comap (i₁ ≫ pullback.fst (pullback.snd c t) pt))).subschemeι ≫ M₁.toBase).finrank q = e) := by
  let φ := fibreIso c t pt (pt ≫ t) rfl
  have hpr : pullback.fst (pullback.snd c t) pt = φ.hom ≫ baseChangeSnd c (⟨pt, rfl⟩ : SchemeHomOver (pt ≫ t) t) :=
    (fibreIso_hom_baseChangeSnd c t pt (pt ≫ t) rfl).symm

  have hε1 : ((sectionIdeal c ε t) ^ r).comap (pullback.fst (pullback.snd c t) pt)
      = ((sectionIdeal c ε (pt ≫ t)) ^ r).comap φ.hom := by
    rw [hpr, Scheme.IdealSheafData.comap_comp, comap_pow, sectionIdeal_comap, comap_pow]
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  haveI : SmoothOfRelativeDimension 1 (pullback.snd (U.ι ≫ c) (pt ≫ t)) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  obtain ⟨σU, hσU, hcomapU, hsuppU⟩ := exists_sectionU c U ε hεU (pt ≫ t)
  obtain ⟨hfinU, hdegU, -, -⟩ := Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id σU hσU r
  have hcomapUr : ((sectionIdeal c ε (pt ≫ t)) ^ r).comap
      (pullback.map (U.ι ≫ c) (pt ≫ t) c (pt ≫ t) U.ι (𝟙 _) (𝟙 _) (by simp) (by simp)) = σU.ker ^ r := by
    rw [comap_pow, hcomapU]
  rw [← hcomapUr] at hfinU hdegU
  have hsuppUr : (((sectionIdeal c ε (pt ≫ t)) ^ r).support : Set ↥(pullback c (pt ≫ t))) ⊆
      Set.range (pullback.map (U.ι ≫ c) (pt ≫ t) c (pt ≫ t) U.ι (𝟙 _) (𝟙 _) (by simp) (by simp)) := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      rw [pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top]
      intro z hz; exact absurd hz (fun h => h)
    · rw [Scheme.IdealSheafData.support_pow _ _ hr.ne']; exact hsuppU
  obtain ⟨eU, heU⟩ := Scheme.IdealSheafData.exists_iso_subscheme_comap_of_support_subset_range
    ((sectionIdeal c ε (pt ≫ t)) ^ r) _ hsuppUr
  have hsndU : pullback.map (U.ι ≫ c) (pt ≫ t) c (pt ≫ t) U.ι (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.snd c (pt ≫ t)
      = pullback.snd (U.ι ≫ c) (pt ≫ t) := by
    rw [pullback.lift_snd, Category.comp_id]
  have hfacU : ((sectionIdeal c ε (pt ≫ t)) ^ r).subschemeι ≫ pullback.snd c (pt ≫ t) =
      eU.inv ≫ ((((sectionIdeal c ε (pt ≫ t)) ^ r).comap
        (pullback.map (U.ι ≫ c) (pt ≫ t) c (pt ≫ t) U.ι (𝟙 _) (𝟙 _) (by simp) (by simp))).subschemeι ≫
          pullback.snd (U.ι ≫ c) (pt ≫ t)) := by
    rw [← hsndU, ← Category.assoc _ _ (pullback.snd c (pt ≫ t)), ← heU]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hfinC : IsFinite (((sectionIdeal c ε (pt ≫ t)) ^ r).subschemeι ≫ pullback.snd c (pt ≫ t)) := by
    rw [hfacU]; haveI := hfinU; infer_instance
  have hdegC : ∀ q : Spec (CommRingCat.of k),
      (((sectionIdeal c ε (pt ≫ t)) ^ r).subschemeι ≫ pullback.snd c (pt ≫ t)).finrank q = r := by
    intro q; rw [hfacU, Scheme.Hom.finrank_comp_left_of_isIso]; exact hdegU q
  obtain ⟨hfinX, hdegX⟩ := transport_fibreIso c t pt ((sectionIdeal c ε (pt ≫ t)) ^ r) hfinC hdegC

  haveI : IsClosedImmersion (rigSection c t ε) := by
    have : IsClosedImmersion (rigSection c t ε ≫ pullback.snd c t) := by
      rw [rigSection, pullback.lift_snd]; infer_instance
    exact .of_comp (rigSection c t ε) (pullback.snd c t)
  have hsuppε : ∀ z : ↥(pullback (pullback.snd c t) pt),
      (pullback.fst (pullback.snd c t) pt).base z ∈ ((sectionIdeal c ε t) ^ r).support → z ∈ W₁ := by
    intro z hz
    apply hε z
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      rw [pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top] at hz
      exact absurd hz (fun h => h)
    · have hz' : (pullback.fst (pullback.snd c t) pt).base z ∈ ((sectionIdeal c ε t).support : Set ↥(pullback c t)) := by
        rw [Scheme.IdealSheafData.support_pow _ _ hr.ne'] at hz; exact hz
      change _ ∈ ((rigSection c t ε).ker.support : Set ↥(pullback c t)) at hz'
      rwa [Scheme.Hom.support_ker, (rigSection c t ε).isClosedEmbedding.isClosed_range.closure_eq] at hz'
  obtain ⟨hA1, hA2⟩ := transport_line c t pt M₁.toBase i₁ hi₁ W₁ hW₁ ((sectionIdeal c ε t) ^ r) hsuppε _ hε1.symm hfinX hdegX

  have hD1 : (D.pullbackAlong pt rfl).I.comap φ.hom = D.I.comap (pullback.fst (pullback.snd c t) pt) := by
    rw [hpr, Scheme.IdealSheafData.comap_comp]
    rfl
  haveI := (D.pullbackAlong pt rfl).isFinite
  obtain ⟨hfinXD, hdegXD⟩ := transport_fibreIso c t pt (D.pullbackAlong pt rfl).I inferInstance
    (D.pullbackAlong pt rfl).finrank_eq
  obtain ⟨hB1, hB2⟩ := transport_line c t pt M₁.toBase i₁ hi₁ W₁ hW₁ D.I hD _ hD1 hfinXD hdegXD
  exact ⟨hA1, hA2, hB1, hB2⟩

end

end S_AlgebraicGeometry_RelPicard_isFinite_and_finrank_subscheme_comap_sectionIdeal_pow_and_comap_I
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_isFinite_and_finrank_subscheme_comap_sectionIdeal_pow_and_comap_I (solution)
