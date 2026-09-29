-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/662d46a8-3510-5023-a374-339e3c66fe24

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse
import Theorems.Thm_AlgebraicGeometry_exists_rationalPoint_enumeration_of_natCard_pullback_eq
import Theorems.Thm_AlgebraicGeometry_dense_setOf_exists_section_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_curveChange_iso_of_closedCover
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_pullback_curveChange_iso_unit_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_tensor_of_pullback_baseChangeSnd_iso_of_tensor_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_iso_unit_of_forall_pullback_rigSection_iso_unit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"
set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard"

namespace S1C
namespace Ext

variable {K : Type u} [Field K]

noncomputable def ev {A T : Scheme.{u}} (a : A ⟶ Spec (.of K)) {h : T ⟶ Spec (.of K)}
    (t : SchemeHomOver (𝟙 _) h) : A ⟶ pullback a h :=
  pullback.lift (𝟙 A) (a ≫ t.1) (by simp only [Category.id_comp, Category.assoc, t.2, Category.comp_id])

@[scoped simp] theorem ev_fst {A T : Scheme.{u}} (a : A ⟶ Spec (.of K)) {h : T ⟶ Spec (.of K)}
    (t : SchemeHomOver (𝟙 _) h) : ev a t ≫ pullback.fst a h = 𝟙 A := by
  simp only [ev, pullback.lift_fst]

@[scoped simp] theorem ev_snd {A T : Scheme.{u}} (a : A ⟶ Spec (.of K)) {h : T ⟶ Spec (.of K)}
    (t : SchemeHomOver (𝟙 _) h) : ev a t ≫ pullback.snd a h = a ≫ t.1 := by
  simp only [ev, pullback.lift_snd]

theorem ev_congr {A T : Scheme.{u}} (a : A ⟶ Spec (.of K)) {h : T ⟶ Spec (.of K)}
    {t t' : SchemeHomOver (𝟙 _) h} (e : t.1 = t'.1) : ev a t = ev a t' := by
  obtain ⟨t, ht⟩ := t; obtain ⟨t', ht'⟩ := t'; cases e; rfl

theorem exists_ev_of_isAlgEquivZero {A : Scheme.{u}} {a : A ⟶ Spec (.of K)} {L : A.Modules}
    (hL : IsAlgEquivZero a L) :
    ∃ (T : Scheme.{u}) (h : T ⟶ Spec (.of K)) (_ : LocallyOfFiniteType h) (_ : GeometricallyIntegral h)
      (M : (pullback a h).Modules) (_ : Scheme.Modules.IsInvertible M) (t₀ t₁ : SchemeHomOver (𝟙 _) h),
      Nonempty ((Scheme.Modules.pullback (ev a t₀)).obj M ≅ SheafOfModules.unit A.ringCatSheaf) ∧
      Nonempty ((Scheme.Modules.pullback (ev a t₁)).obj M ≅ L) := by
  obtain ⟨T, h, hft, hgi, M, hM, t₀, t₁, ⟨e₀⟩, ⟨e₁⟩⟩ := hL

  let σ : A ⟶ pullback a (𝟙 (Spec (.of K))) := pullback.lift (𝟙 A) a (by simp)
  have hσ : ∀ t : SchemeHomOver (𝟙 _) h, σ ≫ baseChangeSnd a t = ev a t := by
    intro t
    apply pullback.hom_ext <;>
      simp only [σ, ev, baseChangeSnd, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
  have hσfst : σ ≫ pullback.fst a (𝟙 _) = 𝟙 A := by simp only [σ, pullback.lift_fst]
  refine ⟨T, h, hft, hgi, M, hM, t₀, t₁, ⟨?_⟩, ⟨?_⟩⟩
  · exact (Scheme.Modules.pullbackCongr (hσ t₀).symm).app M ≪≫
      ((Scheme.Modules.pullbackComp σ (baseChangeSnd a t₀)).app M).symm ≪≫
      (Scheme.Modules.pullback σ).mapIso e₀ ≪≫ Scheme.Modules.pullbackUnitIso σ
  · exact (Scheme.Modules.pullbackCongr (hσ t₁).symm).app M ≪≫
      ((Scheme.Modules.pullbackComp σ (baseChangeSnd a t₁)).app M).symm ≪≫
      (Scheme.Modules.pullback σ).mapIso e₁ ≪≫
      (Scheme.Modules.pullbackComp _ _).app L ≪≫ (Scheme.Modules.pullbackCongr hσfst).app L ≪≫
      (Scheme.Modules.pullbackId A).app L

theorem isIntegral_of_geometricallyIntegral {T : Scheme.{u}} (h : T ⟶ Spec (.of K))
    [hgi : GeometricallyIntegral h] : IsIntegral T :=
  hgi.geometrically_isIntegral (𝟙 _) (𝟙 T) h IsPullback.of_id_fst

theorem exists_section_mem [IsAlgClosed K] {T : Scheme.{u}} (h : T ⟶ Spec (.of K)) [LocallyOfFiniteType h]
    (V : T.Opens) (hV : (V : Set T).Nonempty) :
    ∃ w : Spec (.of K) ⟶ T, w ≫ h = 𝟙 _ ∧ w.base (IsLocalRing.closedPoint K) ∈ V := by
  obtain ⟨x, hxV, s, hs, hsx⟩ :=
    (AlgebraicGeometry.dense_setOf_exists_section_of_isAlgClosed h).inter_open_nonempty (V : Set T) V.isOpen hV
  refine ⟨s, hs, ?_⟩
  rw [← hsx] at hxV
  exact hxV

theorem range_subset_range_ι {T : Scheme.{u}} (t : Spec (.of K) ⟶ T) (V : T.Opens)
    (ht : t.base (IsLocalRing.closedPoint K) ∈ V) : Set.range t.base ⊆ Set.range V.ι.base := by
  rintro _ ⟨p, rfl⟩
  obtain rfl : p = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  rw [← Scheme.Hom.coe_opensRange, Scheme.Opens.opensRange_ι]
  exact ht

theorem exists_opens_forall_trivial {T : Scheme.{u}} {ι : Type} [Finite ι] (N : ι → T.Modules)
    (hN : ∀ j, Scheme.Modules.IsInvertible (N j)) (q : T) :
    ∃ V : T.Opens, q ∈ V ∧ ∀ j, Nonempty ((Scheme.Modules.pullback V.ι).obj (N j) ≅
      SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf) := by
  classical

  have restr : ∀ {U V : T.Opens} (_ : V ≤ U) (j : ι),
      Nonempty ((Scheme.Modules.pullback U.ι).obj (N j) ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) →
      Nonempty ((Scheme.Modules.pullback V.ι).obj (N j) ≅ SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf) := by
    rintro U V e j ⟨i⟩
    exact ⟨(Scheme.Modules.pullbackCongr (T.homOfLE_ι e).symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp (T.homOfLE e) U.ι).app _).symm ≪≫
      (Scheme.Modules.pullback (T.homOfLE e)).mapIso i ≪≫ Scheme.Modules.pullbackUnitIso _⟩
  haveI := Fintype.ofFinite ι
  suffices H : ∀ S : Finset ι, ∃ V : T.Opens, q ∈ V ∧ ∀ j ∈ S, Nonempty ((Scheme.Modules.pullback V.ι).obj (N j) ≅
      SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf) by
    obtain ⟨V, hq, hV⟩ := H Finset.univ
    exact ⟨V, hq, fun j => hV j (Finset.mem_univ j)⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨⊤, trivial, fun j hj => by simp at hj⟩
  | insert j S hjS ih =>
    obtain ⟨V, hqV, hV⟩ := ih
    obtain ⟨U, hqU, ⟨eU⟩⟩ := (hN j).exists_trivialization q
    refine ⟨U ⊓ V, ⟨hqU, hqV⟩, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact restr inf_le_left _ ⟨eU⟩
    · exact restr inf_le_right _ (hV i hi)

end S1C.Ext
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.S1C P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.S1C.Ext"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.S1C"

namespace S1C
namespace Ext
variable {K : Type u} [Field K]
variable {k : Type u} [Field k] (κ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))

def overκ {V : Scheme.{u}} (hV : V ⟶ Spec (.of K)) (v : Spec (.of K) ⟶ V) (hv : v ≫ hV = 𝟙 _) :
    SchemeHomOver κ (hV ≫ κ) :=
  ⟨v, by rw [← Category.assoc, hv, Category.id_comp]⟩

noncomputable def fib {X V : Scheme.{u}} (x : X ⟶ Spec (.of k)) (hV : V ⟶ Spec (.of K))
    (F : (pullback x (hV ≫ κ)).Modules) (v : Spec (.of K) ⟶ V) (hv : v ≫ hV = 𝟙 _) : (pullback x κ).Modules :=
  (Scheme.Modules.pullback (baseChangeSnd x (overκ κ hV v hv))).obj F

end S1C.Ext
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.S1C P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.S1C.Ext"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.S1C P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.S1C.Ext"

namespace S1C
namespace Ext

noncomputable def pullbackTensorIsoUnit {A B : Scheme.{u}} (f : B ⟶ A) {L P : A.Modules} (e : L ⊗ P ≅ 𝟙_ A.Modules) :
    (Scheme.Modules.pullback f).obj L ⊗ (Scheme.Modules.pullback f).obj P ≅ 𝟙_ B.Modules :=
  (Scheme.Modules.pullbackTensorObjIso f L P).symm ≪≫ (Scheme.Modules.pullback f).mapIso e ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso f

theorem ev_mk_congr {K : Type u} [Field K] {A T : Scheme.{u}} (a : A ⟶ Spec (.of K)) {h : T ⟶ Spec (.of K)}
    {u u' : Spec (.of K) ⟶ T} (hu : u ≫ h = 𝟙 _) (hu' : u' ≫ h = 𝟙 _) (e : u = u') :
    ev a ⟨u, hu⟩ = ev a ⟨u', hu'⟩ := by
  cases e; rfl

end S1C.Ext
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.S1C P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.S1C.Ext"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.S1C P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.S1C.Ext"

namespace S1C
namespace Ext

theorem geometricallyIntegral_opens_ι_comp {K : Type u} [Field K] {T : Scheme.{u}} (h : T ⟶ Spec (.of K))
    [hgi : GeometricallyIntegral h] (V : T.Opens) (hV : (V : Set T).Nonempty) : GeometricallyIntegral (V.ι ≫ h) := by
  constructor
  intro K' _ y Z fst snd hP

  haveI : IsIntegral (pullback h y) :=
    hgi.geometrically_isIntegral y (pullback.fst h y) (pullback.snd h y) (IsPullback.of_hasPullback h y)

  let e : Z ≅ pullback V.ι (pullback.fst h y) := hP.isoPullback ≪≫ (pullbackRightPullbackFstIso h y V.ι).symm
  haveI : Nonempty ↥(pullback V.ι (pullback.fst h y)) := by
    obtain ⟨v, hv⟩ := hV
    obtain ⟨p, hp⟩ := (pullback.fst h y).surjective v
    have hp' : p ∈ Set.range (pullback.snd V.ι (pullback.fst h y)) := by
      rw [Scheme.Pullback.range_snd, Set.mem_preimage, hp, Scheme.Opens.range_ι]
      exact hv
    obtain ⟨q, -⟩ := hp'
    exact ⟨q⟩
  haveI : IsIntegral (pullback V.ι (pullback.fst h y)) :=
    isIntegral_of_isOpenImmersion (pullback.snd V.ι (pullback.fst h y))
  exact IsIntegral.of_isIso e.inv
end S1C.Ext
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.S1C P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.S1C.Ext"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.S1C P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.S1C.Ext"

namespace S1C
namespace Ext

section GluedFamily

variable {k : Type u} [Field k] {K : Type u} [Field K] (κ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))

noncomputable def cmp {C T : Scheme.{u}} (c : C ⟶ Spec (.of k)) (h : T ⟶ Spec (.of K)) (V : T.Opens) :
    pullback c ((V.ι ≫ h) ≫ κ) ⟶ pullback (pullback.snd c κ) h :=
  pullback.lift (pullback.lift (pullback.fst c _) (pullback.snd c _ ≫ V.ι ≫ h)
      (by rw [pullback.condition]; simp only [Category.assoc]))
    (pullback.snd c _ ≫ V.ι) (by rw [pullback.lift_snd]; simp only [Category.assoc])

@[reassoc (attr := simp)]
lemma cmp_fst_fst {C T : Scheme.{u}} (c : C ⟶ Spec (.of k)) (h : T ⟶ Spec (.of K)) (V : T.Opens) :
    cmp κ c h V ≫ pullback.fst _ _ ≫ pullback.fst c κ = pullback.fst c _ := by
  simp only [cmp, pullback.lift_fst_assoc, pullback.lift_fst]

@[reassoc (attr := simp)]
lemma cmp_fst_snd {C T : Scheme.{u}} (c : C ⟶ Spec (.of k)) (h : T ⟶ Spec (.of K)) (V : T.Opens) :
    cmp κ c h V ≫ pullback.fst _ _ ≫ pullback.snd c κ = pullback.snd c _ ≫ V.ι ≫ h := by
  simp only [cmp, pullback.lift_fst_assoc, pullback.lift_snd]

@[reassoc (attr := simp)]
lemma cmp_snd {C T : Scheme.{u}} (c : C ⟶ Spec (.of k)) (h : T ⟶ Spec (.of K)) (V : T.Opens) :
    cmp κ c h V ≫ pullback.snd _ _ = pullback.snd c _ ≫ V.ι := by
  simp only [cmp, pullback.lift_snd]

lemma rigSection_cmp {C T : Scheme.{u}} (c : C ⟶ Spec (.of k)) (h : T ⟶ Spec (.of K)) (V : T.Opens)
    (p : SchemeHomOver (𝟙 (Spec (.of k))) c) :
    rigSection c ((V.ι ≫ h) ≫ κ) p ≫ cmp κ c h V =
      V.ι ≫ rigSection (pullback.snd c κ) h
        ⟨pullback.lift (κ ≫ p.1) (𝟙 _) (by simp only [Category.assoc, p.2, Category.comp_id, Category.id_comp]),
          by simp only [pullback.lift_snd]⟩ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc, cmp_fst_fst, rigSection, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [Category.assoc, cmp_fst_snd, rigSection, pullback.lift_snd_assoc, Category.id_comp,
        pullback.lift_fst_assoc, pullback.lift_snd, Category.comp_id]
  · simp only [Category.assoc, cmp_snd, rigSection, pullback.lift_snd_assoc, Category.id_comp, pullback.lift_snd,
      Category.comp_id]

lemma baseChangeSnd_cmp {C T : Scheme.{u}} (c : C ⟶ Spec (.of k)) (h : T ⟶ Spec (.of K)) (V : T.Opens)
    (v : Spec (.of K) ⟶ (V : Scheme.{u})) (hv : v ≫ (V.ι ≫ h) = 𝟙 _) :
    baseChangeSnd c (overκ κ (V.ι ≫ h) v hv) ≫ cmp κ c h V =
      ev (pullback.snd c κ) ⟨v ≫ V.ι, by simpa using hv⟩ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc, cmp_fst_fst, baseChangeSnd, pullback.lift_fst, Category.comp_id, ev,
        pullback.lift_fst_assoc, Category.id_comp]
    · have hv' : v ≫ V.ι ≫ h = 𝟙 _ := by simpa using hv
      simp only [Category.assoc, cmp_fst_snd, baseChangeSnd, pullback.lift_snd_assoc, ev, pullback.lift_fst_assoc,
        Category.id_comp, overκ]
      rw [hv', Category.comp_id]
  · simp only [Category.assoc, cmp_snd, baseChangeSnd, pullback.lift_snd_assoc, ev, pullback.lift_snd, overκ]

end GluedFamily
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.S1C P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.S1C.Ext"

end S1C.Ext
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.S1C P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.S1C.Ext"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.S1C P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.S1C.Ext"

open S1C.Ext

theorem S1C.Ext.exists_gluedFamily
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (K : Type u) [Field K] [IsAlgClosed K] (κ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (p₁ : Fin s → SchemeHomOver (𝟙 (Spec (.of k))) c₁) (p₂ : Fin s → SchemeHomOver (𝟙 (Spec (.of k))) c₂)
    (hinj : Function.Injective fun j => (p₁ j).1.base (IsLocalRing.closedPoint k))
    (hnode : ∀ j, (p₁ j).1 ≫ i₁.1 = (p₂ j).1 ≫ i₂.1)
    (hinter : ∀ (q₁ : C₁) (q₂ : C₂), i₁.1.base q₁ = i₂.1.base q₂ →
      ∃ j, q₁ = (p₁ j).1.base (IsLocalRing.closedPoint k) ∧ q₂ = (p₂ j).1.base (IsLocalRing.closedPoint k))
    {T : Scheme.{u}} (h : T ⟶ Spec (.of K)) (M : (pullback (pullback.snd c₁ κ) h).Modules)
    (hM : Scheme.Modules.IsInvertible M) (V : T.Opens)
    (hV : ∀ j, Nonempty ((Scheme.Modules.pullback (V.ι ≫ rigSection (pullback.snd c₁ κ) h
        ⟨pullback.lift (κ ≫ (p₁ j).1) (𝟙 _) (by simp only [Category.assoc, (p₁ j).2, Category.comp_id, Category.id_comp]),
          by simp only [pullback.lift_snd]⟩)).obj M ≅ SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf)) :
    ∃ (M' : (pullback x ((V.ι ≫ h) ≫ κ)).Modules), Scheme.Modules.IsInvertible M' ∧
      ∀ (v : Spec (.of K) ⟶ (V : Scheme.{u})) (hv : v ≫ (V.ι ≫ h) = 𝟙 _),
        Nonempty ((Scheme.Modules.pullback (curveChange i₁.1 i₁.2 κ)).obj (fib κ x (V.ι ≫ h) M' v hv) ≅
          (Scheme.Modules.pullback (ev (pullback.snd c₁ κ) ⟨v ≫ V.ι, by simpa using hv⟩)).obj M) ∧
        Nonempty ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 κ)).obj (fib κ x (V.ι ≫ h) M' v hv) ≅
          SheafOfModules.unit (pullback c₂ κ).ringCatSheaf) := by
  classical

  set t : (V : Scheme.{u}) ⟶ Spec (.of k) := (V.ι ≫ h) ≫ κ with ht
  let g := S1C.Ext.cmp κ c₁ h V

  let L₁ : (pullback c₁ t).Modules := (Scheme.Modules.pullback g).obj M
  have hL₁ : Scheme.Modules.IsInvertible L₁ := hM.pullback _
  let L₂ : (pullback c₂ t).Modules := SheafOfModules.unit (pullback c₂ t).ringCatSheaf
  have hL₂ : Scheme.Modules.IsInvertible L₂ := Scheme.Modules.isInvertible_unit _

  let z : pullback i₁.1 i₂.1 ⟶ Spec (.of k) := pullback.fst i₁.1 i₂.1 ≫ c₁
  let j₁ : SchemeHomOver z c₁ := ⟨pullback.fst i₁.1 i₂.1, rfl⟩
  have hz₂ : pullback.snd i₁.1 i₂.1 ≫ c₂ = z := by
    show pullback.snd i₁.1 i₂.1 ≫ c₂ = pullback.fst i₁.1 i₂.1 ≫ c₁
    calc pullback.snd i₁.1 i₂.1 ≫ c₂ = pullback.snd i₁.1 i₂.1 ≫ i₂.1 ≫ x := by rw [i₂.2]
      _ = (pullback.snd i₁.1 i₂.1 ≫ i₂.1) ≫ x := (Category.assoc _ _ _).symm
      _ = (pullback.fst i₁.1 i₂.1 ≫ i₁.1) ≫ x := by rw [pullback.condition]
      _ = pullback.fst i₁.1 i₂.1 ≫ c₁ := by rw [Category.assoc, i₁.2]
  let j₂ : SchemeHomOver z c₂ := ⟨pullback.snd i₁.1 i₂.1, hz₂⟩
  have hZ : IsPullback j₁.1 j₂.1 i₁.1 i₂.1 := IsPullback.of_hasPullback i₁.1 i₂.1
  have hj : j₁.1 ≫ i₁.1 = j₂.1 ≫ i₂.1 := pullback.condition
  have hsq : curveChange j₁.1 j₁.2 t ≫ curveChange i₁.1 i₁.2 t = curveChange j₂.1 j₂.2 t ≫ curveChange i₂.1 i₂.2 t := by
    apply pullback.hom_ext
    · simp only [curveChange, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hj]
    · simp only [curveChange, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]

  let ζ : Fin s → SchemeHomOver (𝟙 (Spec (.of k))) z := fun j =>
    ⟨pullback.lift (p₁ j).1 (p₂ j).1 (hnode j), by
      simp only [z, pullback.lift_fst_assoc, (p₁ j).2]⟩
  have hcov : ∀ w : ↥(pullback i₁.1 i₂.1), ∃ j, (ζ j).1.base (IsLocalRing.closedPoint k) = w := by
    intro w
    obtain ⟨j, hq₁, hq₂⟩ := hinter ((pullback.fst i₁.1 i₂.1).base w) ((pullback.snd i₁.1 i₂.1).base w)
      (congrArg (fun f => f.base w) (pullback.condition (f := i₁.1) (g := i₂.1)))
    refine ⟨j, (pullback.snd i₁.1 i₂.1).isClosedEmbedding.injective ?_⟩
    rw [hq₂]
    exact congrArg (fun f => f.base (IsLocalRing.closedPoint k)) (pullback.lift_snd (p₁ j).1 (p₂ j).1 (hnode j))
  haveI : Finite ↥(pullback i₁.1 i₂.1) := Nat.finite_of_card_ne_zero (by rw [hs]; exact hs0.ne')
  haveI : IsReduced (pullback i₁.1 i₂.1) := hcr
  haveI : IsSeparated z := inferInstance

  let F : (pullback z t).Modules := (Scheme.Modules.pullback (curveChange j₁.1 j₁.2 t)).obj L₁
  have htriv : ∀ j, Nonempty ((Scheme.Modules.pullback (rigSection z t (ζ j))).obj F ≅
      SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf) := by
    intro j
    obtain ⟨e⟩ := hV j
    have hε : (ζ j).1 ≫ j₁.1 = (p₁ j).1 := by simp only [ζ, j₁, pullback.lift_fst]
    have hcomp : rigSection z t (ζ j) ≫ curveChange j₁.1 j₁.2 t ≫ g =
        V.ι ≫ rigSection (pullback.snd c₁ κ) h ⟨pullback.lift (κ ≫ (p₁ j).1) (𝟙 _)
          (by simp only [Category.assoc, (p₁ j).2, Category.comp_id, Category.id_comp]),
          by simp only [pullback.lift_snd]⟩ := by
      rw [← Category.assoc, rigSection_curveChange j₁.1 j₁.2 hε t]
      exact S1C.Ext.rigSection_cmp κ c₁ h V (p₁ j)
    exact ⟨(Scheme.Modules.pullbackComp _ _).app L₁ ≪≫ (Scheme.Modules.pullbackComp _ _).app M ≪≫
      (Scheme.Modules.pullbackCongr hcomp).app M ≪≫ e⟩
  obtain ⟨eF⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_iso_unit_of_forall_pullback_rigSection_iso_unit
    z t ζ hcov F htriv
  let φ : (Scheme.Modules.pullback (curveChange j₁.1 j₁.2 t)).obj L₁ ≅
      (Scheme.Modules.pullback (curveChange j₂.1 j₂.2 t)).obj L₂ :=
    eF ≪≫ (Scheme.Modules.pullbackUnitIso (curveChange j₂.1 j₂.2 t)).symm

  obtain ⟨M', hM', α₁, α₂, -⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_isInvertible_pullback_curveChange_iso_of_closedCover x hXred c₁ c₂ z i₁ i₂
      hjs j₁ j₂ hZ t hsq L₁ hL₁ L₂ hL₂ φ
  refine ⟨M', hM', fun v hv => ⟨⟨?_⟩, ⟨?_⟩⟩⟩
  ·
    have hev : baseChangeSnd c₁ (overκ κ (V.ι ≫ h) v hv) ≫ g = ev (pullback.snd c₁ κ) ⟨v ≫ V.ι, by simpa using hv⟩ :=
      S1C.Ext.baseChangeSnd_cmp κ c₁ h V v hv
    exact (Scheme.Modules.pullbackComp _ _).app M' ≪≫
      (Scheme.Modules.pullbackCongr (curveChange_baseChangeSnd i₁.1 i₁.2 (overκ κ (V.ι ≫ h) v hv))).app M' ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M').symm ≪≫
      (Scheme.Modules.pullback _).mapIso α₁ ≪≫
      (Scheme.Modules.pullbackComp _ _).app M ≪≫ (Scheme.Modules.pullbackCongr hev).app M
  ·
    exact (Scheme.Modules.pullbackComp _ _).app M' ≪≫
      (Scheme.Modules.pullbackCongr (curveChange_baseChangeSnd i₂.1 i₂.2 (overκ κ (V.ι ≫ h) v hv))).app M' ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M').symm ≪≫
      (Scheme.Modules.pullback _).mapIso α₂ ≪≫ Scheme.Modules.pullbackUnitIso _

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (K : Type u) [Field K] [IsAlgClosed K] (κ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (L₁ : (pullback c₁ κ).Modules) (hL₁ : Scheme.Modules.IsInvertible L₁)
    (h₁ : IsAlgEquivZero (pullback.snd c₁ κ) L₁) :
    ∃ L' : (pullback x κ).Modules, Scheme.Modules.IsInvertible L' ∧ IsAlgEquivZero (pullback.snd x κ) L' ∧
      Nonempty ((Scheme.Modules.pullback (curveChange i₁.1 i₁.2 κ)).obj L' ≅ L₁) ∧
      Nonempty ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 κ)).obj L' ≅
        SheafOfModules.unit (pullback c₂ κ).ringCatSheaf) := by

  haveI : LocallyOfFiniteType c₁ := by
    haveI := SmoothOfRelativeDimension.smooth 1 c₁; infer_instance
  haveI : LocallyOfFiniteType c₂ := by
    haveI := SmoothOfRelativeDimension.smooth 1 c₂; infer_instance
  obtain ⟨p₁, p₂, hinj, hnode, hinter⟩ :=
    AlgebraicGeometry.exists_rationalPoint_enumeration_of_natCard_pullback_eq k x i₁ i₂ s hs hs0

  obtain ⟨T, h, hft, hgi, M, hM, t₀, t₁, ⟨e₀⟩, ⟨e₁⟩⟩ := exists_ev_of_isAlgEquivZero h₁
  haveI := hft
  haveI := hgi
  haveI := isIntegral_of_geometricallyIntegral h

  let n : Fin s → (T ⟶ pullback (pullback.snd c₁ κ) h) := fun j => rigSection (pullback.snd c₁ κ) h
    ⟨pullback.lift (κ ≫ (p₁ j).1) (𝟙 _) (by simp only [Category.assoc, (p₁ j).2, Category.comp_id, Category.id_comp]),
      by simp only [pullback.lift_snd]⟩
  obtain ⟨V', ht₁V', hV'⟩ := exists_opens_forall_trivial (fun j => (Scheme.Modules.pullback (n j)).obj M)
    (fun j => hM.pullback _) (t₁.1.base (IsLocalRing.closedPoint K))
  obtain ⟨V'', ht₀V'', hV''⟩ := exists_opens_forall_trivial (fun j => (Scheme.Modules.pullback (n j)).obj M)
    (fun j => hM.pullback _) (t₀.1.base (IsLocalRing.closedPoint K))
  have hV'c : ∀ j, Nonempty ((Scheme.Modules.pullback (V'.ι ≫ n j)).obj M ≅
      SheafOfModules.unit (V' : Scheme.{u}).ringCatSheaf) := fun j =>
    ⟨((Scheme.Modules.pullbackComp V'.ι (n j)).app M).symm ≪≫ (hV' j).some⟩
  have hV''c : ∀ j, Nonempty ((Scheme.Modules.pullback (V''.ι ≫ n j)).obj M ≅
      SheafOfModules.unit (V'' : Scheme.{u}).ringCatSheaf) := fun j =>
    ⟨((Scheme.Modules.pullbackComp V''.ι (n j)).app M).symm ≪≫ (hV'' j).some⟩

  obtain ⟨w, hw, hwV', hwV''⟩ : ∃ w : Spec (.of K) ⟶ T, w ≫ h = 𝟙 _ ∧
      w.base (IsLocalRing.closedPoint K) ∈ V' ∧ w.base (IsLocalRing.closedPoint K) ∈ V'' := by
    obtain ⟨w, hw, hwV⟩ := exists_section_mem h (V' ⊓ V'')
      (nonempty_preirreducible_inter V'.isOpen V''.isOpen ⟨_, ht₁V'⟩ ⟨_, ht₀V''⟩)
    exact ⟨w, hw, (TopologicalSpace.Opens.mem_inf.mp hwV).1, (TopologicalSpace.Opens.mem_inf.mp hwV).2⟩

  obtain ⟨t₁', ht₁'⟩ : ∃ t₁' : Spec (.of K) ⟶ (V' : Scheme.{u}), t₁' ≫ V'.ι = t₁.1 :=
    ⟨_, IsOpenImmersion.lift_fac V'.ι t₁.1 (range_subset_range_ι _ _ ht₁V')⟩
  obtain ⟨w', hw'⟩ : ∃ w' : Spec (.of K) ⟶ (V' : Scheme.{u}), w' ≫ V'.ι = w :=
    ⟨_, IsOpenImmersion.lift_fac V'.ι w (range_subset_range_ι _ _ hwV')⟩
  obtain ⟨t₀'', ht₀''⟩ : ∃ t₀'' : Spec (.of K) ⟶ (V'' : Scheme.{u}), t₀'' ≫ V''.ι = t₀.1 :=
    ⟨_, IsOpenImmersion.lift_fac V''.ι t₀.1 (range_subset_range_ι _ _ ht₀V'')⟩
  obtain ⟨w'', hw''⟩ : ∃ w'' : Spec (.of K) ⟶ (V'' : Scheme.{u}), w'' ≫ V''.ι = w :=
    ⟨_, IsOpenImmersion.lift_fac V''.ι w (range_subset_range_ι _ _ hwV'')⟩
  have ht₁'h : t₁' ≫ (V'.ι ≫ h) = 𝟙 _ := by rw [← Category.assoc, ht₁', t₁.2]
  have hw'h : w' ≫ (V'.ι ≫ h) = 𝟙 _ := by rw [← Category.assoc, hw', hw]
  have ht₀''h : t₀'' ≫ (V''.ι ≫ h) = 𝟙 _ := by rw [← Category.assoc, ht₀'', t₀.2]
  have hw''h : w'' ≫ (V''.ι ≫ h) = 𝟙 _ := by rw [← Category.assoc, hw'', hw]

  obtain ⟨M', hM', hfib'⟩ := S1C.Ext.exists_gluedFamily x hXred c₁ c₂ i₁ i₂ hjs hcr s hs hs0 K κ
    p₁ p₂ hinj hnode hinter h M hM V' hV'c
  obtain ⟨M'', hM'', hfib''⟩ := S1C.Ext.exists_gluedFamily x hXred c₁ c₂ i₁ i₂ hjs hcr s hs hs0 K κ
    p₁ p₂ hinj hnode hinter h M hM V'' hV''c

  obtain ⟨⟨eAw₁⟩, ⟨eAw₂⟩⟩ := hfib' w' hw'h
  obtain ⟨⟨eBt₁⟩, ⟨eBt₂⟩⟩ := hfib' t₁' ht₁'h
  obtain ⟨⟨eCt₁⟩, ⟨eCt₂⟩⟩ := hfib'' t₀'' ht₀''h
  obtain ⟨⟨eDw₁⟩, ⟨eDw₂⟩⟩ := hfib'' w'' hw''h
  have hAw : Scheme.Modules.IsInvertible (fib κ x (V'.ι ≫ h) M' w' hw'h) := hM'.pullback _
  have hBt : Scheme.Modules.IsInvertible (fib κ x (V'.ι ≫ h) M' t₁' ht₁'h) := hM'.pullback _
  have hCt : Scheme.Modules.IsInvertible (fib κ x (V''.ι ≫ h) M'' t₀'' ht₀''h) := hM''.pullback _
  have hDw : Scheme.Modules.IsInvertible (fib κ x (V''.ι ≫ h) M'' w'' hw''h) := hM''.pullback _
  obtain ⟨PA, hPA, ⟨ePA⟩⟩ := hAw.exists_tensor_inverse
  obtain ⟨PC, hPC, ⟨ePC⟩⟩ := hCt.exists_tensor_inverse
  obtain ⟨PD, hPD, ⟨ePD⟩⟩ := hDw.exists_tensor_inverse

  haveI : GeometricallyIntegral (V'.ι ≫ h) := geometricallyIntegral_opens_ι_comp h V' ⟨_, ht₁V'⟩
  haveI : GeometricallyIntegral (V''.ι ≫ h) := geometricallyIntegral_opens_ι_comp h V'' ⟨_, ht₀V''⟩
  have hBA : IsAlgEquivZero (pullback.snd x κ) (fib κ x (V'.ι ≫ h) M' t₁' ht₁'h ⊗ PA) :=
    AlgebraicGeometry.RelPicard.isAlgEquivZero_tensor_of_pullback_baseChangeSnd_iso_of_tensor_iso_unit κ x (V'.ι ≫ h)
      M' hM' w' t₁' hw'h ht₁'h _ _ PA (Iso.refl _) (Iso.refl _) hPA ePA
  have hDC : IsAlgEquivZero (pullback.snd x κ) (fib κ x (V''.ι ≫ h) M'' w'' hw''h ⊗ PC) :=
    AlgebraicGeometry.RelPicard.isAlgEquivZero_tensor_of_pullback_baseChangeSnd_iso_of_tensor_iso_unit κ x (V''.ι ≫ h)
      M'' hM'' t₀'' w'' ht₀''h hw''h _ _ PC (Iso.refl _) (Iso.refl _) hPC ePC

  have hCt0 : IsAlgEquivZero (pullback.snd x κ) (fib κ x (V''.ι ≫ h) M'' t₀'' ht₀''h) :=
    AlgebraicGeometry.RelPicard.isAlgEquivZero_of_pullback_curveChange_iso_unit_of_twoGluedSmoothCurves
      x hXred c₁ c₂ i₁ i₂ hjs hcr s hs hs0 K κ _ hCt
      ⟨eCt₁ ≪≫ (Scheme.Modules.pullbackCongr (ev_mk_congr _ _ t₀.2 ht₀'')).app M ≪≫ e₀⟩ ⟨eCt₂⟩

  have hDw0 : IsAlgEquivZero (pullback.snd x κ) (fib κ x (V''.ι ≫ h) M'' w'' hw''h) :=
    (hDC.tensor hCt0).of_iso ((α_ _ _ _) ≪≫ whiskerLeftIso _ ((β_ _ _) ≪≫ ePC) ≪≫ (ρ_ _))

  have hAD : IsAlgEquivZero (pullback.snd x κ) (fib κ x (V'.ι ≫ h) M' w' hw'h ⊗ PD) := by
    refine AlgebraicGeometry.RelPicard.isAlgEquivZero_of_pullback_curveChange_iso_unit_of_twoGluedSmoothCurves
      x hXred c₁ c₂ i₁ i₂ hjs hcr s hs hs0 K κ _ (hAw.tensor hPD) ⟨?_⟩ ⟨?_⟩
    · exact Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
        ((eAw₁ ≪≫ (Scheme.Modules.pullbackCongr (ev_mk_congr _ _ _ (by rw [hw', hw'']))).app M ≪≫ eDw₁.symm) ⊗ᵢ
          Iso.refl _) ≪≫ pullbackTensorIsoUnit _ ePD
    · exact Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ ((eAw₂ ≪≫ eDw₂.symm) ⊗ᵢ Iso.refl _) ≪≫
        pullbackTensorIsoUnit _ ePD

  have hBt0 : IsAlgEquivZero (pullback.snd x κ) (fib κ x (V'.ι ≫ h) M' t₁' ht₁'h) :=
    ((hBA.tensor hAD).tensor hDw0).of_iso
      ((α_ _ _ _) ≪≫ whiskerLeftIso _ ((α_ _ _ _) ≪≫ whiskerLeftIso _ ((β_ _ _) ≪≫ ePD) ≪≫ (ρ_ _)) ≪≫
        (α_ _ _ _) ≪≫ whiskerLeftIso _ ((β_ _ _) ≪≫ ePA) ≪≫ (ρ_ _))
  exact ⟨fib κ x (V'.ι ≫ h) M' t₁' ht₁'h, hBt, hBt0,
    ⟨eBt₁ ≪≫ (Scheme.Modules.pullbackCongr (ev_mk_congr _ _ t₁.2 ht₁')).app M ≪≫ e₁⟩, ⟨eBt₂⟩⟩

end S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves (solution)
