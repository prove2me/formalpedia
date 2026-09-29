-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_opens_section_restrictPair_of_twoGluedSmoothCurves
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/e94c9f63-7175-578a-8226-7930743d150e

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_curveChange_iso_of_closedCover
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_iso_unit_of_forall_pullback_rigSection_iso_unit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_opens_section_restrictPair_of_twoGluedSmoothCurves
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard

namespace S1C
namespace LocSec

section Helpers

variable {X₀ X₁ X₂ X₃ : Scheme.{u}}

noncomputable def pb3 (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (L : X₃.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj L)) ≅
      (Scheme.Modules.pullback (f ≫ g ≫ h)).obj L :=
  (Scheme.Modules.pullback f).mapIso ((Scheme.Modules.pullbackComp g h).app L) ≪≫ (Scheme.Modules.pullbackComp f (g ≫ h)).app L

noncomputable def pb2 (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (L : X₂.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj L) ≅ (Scheme.Modules.pullback (f ≫ g)).obj L :=
  (Scheme.Modules.pullbackComp f g).app L

theorem nonempty_iso_unit_of_le {X : Scheme.{u}} {K : X.Modules} {U U' : X.Opens} (hle : U ≤ U')
    (h : Nonempty ((Scheme.Modules.pullback U'.ι).obj K ≅ SheafOfModules.unit (U' : Scheme.{u}).ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback U.ι).obj K ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :=
  ⟨(Scheme.Modules.pullbackCongr (X.homOfLE_ι hle).symm).app K ≪≫ (pb2 (X.homOfLE hle) U'.ι K).symm ≪≫
    (Scheme.Modules.pullback (X.homOfLE hle)).mapIso h.some ≪≫ Scheme.Modules.pullbackUnitIso _⟩

theorem nonempty_rigidify_iso {T P : Scheme.{u}} (σ : T ⟶ P) (q : P ⟶ T) (L : P.Modules)
    (h : Nonempty ((Scheme.Modules.pullback σ).obj L ≅ SheafOfModules.unit T.ringCatSheaf)) :
    Nonempty (Scheme.Modules.rigidify σ q L ≅ L) := by
  obtain ⟨e⟩ := h
  exact ⟨MonoidalCategory.whiskerLeftIso L ((Scheme.Modules.pullback q).mapIso
      (Scheme.Modules.dualMapIso e ≪≫ (MonoidalClosed.unitNatIso.app _).symm) ≪≫
    Scheme.Modules.pullbackUnitIso q) ≪≫ MonoidalCategory.rightUnitor L⟩

end Helpers

theorem exists_rationalPoints
    {k : Type u} [Field k] [IsAlgClosed k] {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType z] [Finite Z] :
    ∃ ζ : Z → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z, ∀ w, (ζ w).1.base (IsLocalRing.closedPoint k) = w := by

  haveI : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace z
  haveI : DiscreteTopology Z := JacobsonSpace.discreteTopology (Set.toFinite _)
  choose ζ hζ using fun w : Z =>
    AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton k z w (isClosed_discrete _)
  exact ⟨fun w => ⟨(ζ w).left, Over.w (ζ w)⟩, hζ⟩

theorem isAlgEquivZero_pullback_curveChange_fibre
    {k : Type u} [Field k] {X C T : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (c : C ⟶ Spec (CommRingCat.of k))
    {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c} (i : SchemeHomOver c x) (t : T ⟶ Spec (CommRingCat.of k))
    (L : (pullback x t).Modules) (P : RigidifiedLineBundle c ε' t)
    (α : (Scheme.Modules.pullback (curveChange i.1 i.2 t)).obj L ≅ P.L) (hP : FibrewiseAlgEquivZero P)
    (K : Type u) [Field K] [IsAlgClosed K] (sK : Spec (CommRingCat.of K) ⟶ T) :
    IsAlgEquivZero (pullback.snd c (sK ≫ t))
      ((Scheme.Modules.pullback (curveChange i.1 i.2 (sK ≫ t))).obj
        ((Scheme.Modules.pullback ((pullbackLeftPullbackSndIso x t sK).inv ≫ pullback.fst (pullback.snd x t) sK)).obj L)) := by

  have hmap : ((pullbackLeftPullbackSndIso c t sK).inv ≫ pullback.fst (pullback.snd c t) sK) ≫ curveChange i.1 i.2 t =
      curveChange i.1 i.2 (sK ≫ t) ≫ (pullbackLeftPullbackSndIso x t sK).inv ≫ pullback.fst (pullback.snd x t) sK := by
    apply pullback.hom_ext
    · have l1 : (((pullbackLeftPullbackSndIso c t sK).inv ≫ pullback.fst (pullback.snd c t) sK) ≫
          curveChange i.1 i.2 t) ≫ pullback.fst x t = pullback.fst c (sK ≫ t) ≫ i.1 := by
        simp only [Category.assoc, curveChange, pullback.lift_fst]
        rw [← Category.assoc, ← Category.assoc, Category.assoc _ (pullback.fst (pullback.snd c t) sK),
          pullbackLeftPullbackSndIso_inv_fst]
      have r1 : (curveChange i.1 i.2 (sK ≫ t) ≫ (pullbackLeftPullbackSndIso x t sK).inv ≫
          pullback.fst (pullback.snd x t) sK) ≫ pullback.fst x t = pullback.fst c (sK ≫ t) ≫ i.1 := by
        simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_fst, curveChange, pullback.lift_fst]
      rw [l1, r1]
    · have hc : (pullbackLeftPullbackSndIso c t sK).inv ≫ pullback.snd (pullback.snd c t) sK = pullback.snd c (sK ≫ t) := by
        rw [Iso.inv_comp_eq]; exact (pullbackLeftPullbackSndIso_hom_snd c t sK).symm
      have hx : (pullbackLeftPullbackSndIso x t sK).inv ≫ pullback.snd (pullback.snd x t) sK = pullback.snd x (sK ≫ t) := by
        rw [Iso.inv_comp_eq]; exact (pullbackLeftPullbackSndIso_hom_snd x t sK).symm
      have l2 : (((pullbackLeftPullbackSndIso c t sK).inv ≫ pullback.fst (pullback.snd c t) sK) ≫
          curveChange i.1 i.2 t) ≫ pullback.snd x t = pullback.snd c (sK ≫ t) ≫ sK := by
        simp only [Category.assoc, curveChange, pullback.lift_snd, Category.comp_id]
        rw [pullback.condition (f := pullback.snd c t) (g := sK), ← Category.assoc, hc]
      have r2 : (curveChange i.1 i.2 (sK ≫ t) ≫ (pullbackLeftPullbackSndIso x t sK).inv ≫
          pullback.fst (pullback.snd x t) sK) ≫ pullback.snd x t = pullback.snd c (sK ≫ t) ≫ sK := by
        simp only [Category.assoc]
        rw [pullback.condition (f := pullback.snd x t) (g := sK), ← Category.assoc (pullbackLeftPullbackSndIso x t sK).inv,
          hx, ← Category.assoc, curveChange_snd]
      rw [l2, r2]

  have h := (hP K sK).pullback (pullbackLeftPullbackSndIso c t sK).inv (by
    rw [Iso.inv_comp_eq]; exact (pullbackLeftPullbackSndIso_hom_snd c t sK).symm)
  refine h.of_iso ?_
  exact pb2 _ _ _ ≪≫ (Scheme.Modules.pullback _).mapIso α.symm ≪≫ pb2 _ _ _ ≪≫
    (Scheme.Modules.pullbackCongr hmap).app L ≪≫ (pb2 _ _ L).symm

end S1C.LocSec

open S1C.LocSec in
theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (ε : SchemeHomOver (𝟙 _) x) (ε₁ : SchemeHomOver (𝟙 _) c₁) (hε : ε₁.1 ≫ i₁.1 = ε.1)
    (ε₂ : SchemeHomOver (𝟙 _) c₂)
    (D : RelativePic0Designation k x) (hD : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (D₁ : RelativePic0Designation k c₁) (hD₁ : RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁)
    (D₂ : RelativePic0Designation k c₂) (hD₂ : RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂)
    (ν₁ : SchemeHomOver D.toBase D₁.toBase) (ν₂ : SchemeHomOver D.toBase D₂.toBase)
    (hν₁ : ν₁ = RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁)
    (hν₂ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
        Nonempty ((hD₂.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L))) :
    ∀ b : ↥(pullback D₁.toBase D₂.toBase), ∃ U : (pullback D₁.toBase D₂.toBase).Opens, b ∈ U ∧
      ∃ σ : (U : Scheme.{u}) ⟶ D.P, σ ≫ pullback.lift ν₁.1 ν₂.1 (ν₁.2.trans ν₂.2.symm) = U.ι := by
  intro b

  let bB : pullback D₁.toBase D₂.toBase ⟶ Spec (CommRingCat.of k) := pullback.fst D₁.toBase D₂.toBase ≫ D₁.toBase
  let pr₁ : SchemeHomOver bB D₁.toBase := ⟨pullback.fst D₁.toBase D₂.toBase, rfl⟩
  let pr₂ : SchemeHomOver bB D₂.toBase := ⟨pullback.snd D₁.toBase D₂.toBase, pullback.condition.symm⟩
  let z : pullback i₁.1 i₂.1 ⟶ Spec (CommRingCat.of k) := pullback.fst i₁.1 i₂.1 ≫ c₁
  let j₁ : SchemeHomOver z c₁ := ⟨pullback.fst i₁.1 i₂.1, rfl⟩
  have hj₂ : pullback.snd i₁.1 i₂.1 ≫ c₂ = z :=
    calc pullback.snd i₁.1 i₂.1 ≫ c₂ = pullback.snd i₁.1 i₂.1 ≫ i₂.1 ≫ x := by rw [i₂.2]
      _ = pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ x := by rw [pullback.condition_assoc]
      _ = pullback.fst i₁.1 i₂.1 ≫ c₁ := by rw [i₁.2]
  let j₂ : SchemeHomOver z c₂ := ⟨pullback.snd i₁.1 i₂.1, hj₂⟩
  haveI : LocallyOfFiniteType z := inferInstance
  haveI : IsSeparated z := inferInstance
  haveI : IsReduced (pullback i₁.1 i₂.1) := hcr
  haveI : Finite ↥(pullback i₁.1 i₂.1) := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fintype ↥(pullback i₁.1 i₂.1) := Fintype.ofFinite _
  obtain ⟨ζ, hζpt⟩ := exists_rationalPoints z

  have hN₁B : ∀ w, Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (rigSection z bB (ζ w))).obj
      ((Scheme.Modules.pullback (curveChange j₁.1 j₁.2 bB)).obj (hD₁.poincare.pullbackAlong pr₁).L)) :=
    fun w => (((hD₁.poincare.pullbackAlong pr₁).isInvertible.pullback _).pullback _)
  have hN₂B : ∀ w, Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (rigSection z bB (ζ w))).obj
      ((Scheme.Modules.pullback (curveChange j₂.1 j₂.2 bB)).obj (hD₂.poincare.pullbackAlong pr₂).L)) :=
    fun w => (((hD₂.poincare.pullbackAlong pr₂).isInvertible.pullback _).pullback _)
  choose U₁ hbU₁ hU₁ using fun w => (hN₁B w).exists_trivialization b
  choose U₂ hbU₂ hU₂ using fun w => (hN₂B w).exists_trivialization b
  let U : (pullback D₁.toBase D₂.toBase).Opens := Finset.univ.inf U₁ ⊓ Finset.univ.inf U₂
  have hbU : b ∈ U := by
    refine ⟨?_, ?_⟩
    · exact Finset.inf_induction (p := fun O : (pullback D₁.toBase D₂.toBase).Opens => b ∈ O) trivial
        (fun O₁ h₁ O₂ h₂ => ⟨h₁, h₂⟩) (fun w _ => hbU₁ w)
    · exact Finset.inf_induction (p := fun O : (pullback D₁.toBase D₂.toBase).Opens => b ∈ O) trivial
        (fun O₁ h₁ O₂ h₂ => ⟨h₁, h₂⟩) (fun w _ => hbU₂ w)
  have hUle₁ : ∀ w, U ≤ U₁ w := fun w => inf_le_left.trans (Finset.inf_le (Finset.mem_univ w))
  have hUle₂ : ∀ w, U ≤ U₂ w := fun w => inf_le_right.trans (Finset.inf_le (Finset.mem_univ w))
  refine ⟨U, hbU, ?_⟩
  let u : (U : Scheme.{u}) ⟶ Spec (CommRingCat.of k) := U.ι ≫ bB
  let a₁ : SchemeHomOver u D₁.toBase := ⟨U.ι ≫ pullback.fst D₁.toBase D₂.toBase, by rw [Category.assoc]⟩
  let a₂ : SchemeHomOver u D₂.toBase := ⟨U.ι ≫ pullback.snd D₁.toBase D₂.toBase, by
    rw [Category.assoc, ← pullback.condition]⟩
  let P₁U := hD₁.poincare.pullbackAlong a₁
  let P₂U := hD₂.poincare.pullbackAlong a₂

  have hmaps₁ : ∀ w, rigSection z u (ζ w) ≫ curveChange j₁.1 j₁.2 u ≫ baseChangeSnd c₁ a₁ =
      (U.ι ≫ rigSection z bB (ζ w)) ≫ curveChange j₁.1 j₁.2 bB ≫ baseChangeSnd c₁ pr₁ := fun w => by
    apply pullback.hom_ext <;> simp only [u, a₁, pr₁, rigSection, curveChange, baseChangeSnd, Category.assoc,
      pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id,
      Category.id_comp]
  have hmaps₂ : ∀ w, rigSection z u (ζ w) ≫ curveChange j₂.1 j₂.2 u ≫ baseChangeSnd c₂ a₂ =
      (U.ι ≫ rigSection z bB (ζ w)) ≫ curveChange j₂.1 j₂.2 bB ≫ baseChangeSnd c₂ pr₂ := fun w => by
    apply pullback.hom_ext <;> simp only [u, a₂, pr₂, rigSection, curveChange, baseChangeSnd, Category.assoc,
      pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id,
      Category.id_comp]
  have key₁ : ∀ w, Nonempty ((Scheme.Modules.pullback (rigSection z u (ζ w))).obj
      ((Scheme.Modules.pullback (curveChange j₁.1 j₁.2 u)).obj P₁U.L) ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) := by
    intro w
    obtain ⟨tr⟩ := nonempty_iso_unit_of_le (hUle₁ w) (hU₁ w)
    refine ⟨pb3 (rigSection z u (ζ w)) (curveChange j₁.1 j₁.2 u) (baseChangeSnd c₁ a₁) hD₁.poincare.L ≪≫
      (Scheme.Modules.pullbackCongr (hmaps₁ w)).app hD₁.poincare.L ≪≫
      (pb3 (U.ι ≫ rigSection z bB (ζ w)) (curveChange j₁.1 j₁.2 bB) (baseChangeSnd c₁ pr₁) hD₁.poincare.L).symm ≪≫
      (pb2 U.ι (rigSection z bB (ζ w)) _).symm ≪≫ tr⟩
  have key₂ : ∀ w, Nonempty ((Scheme.Modules.pullback (rigSection z u (ζ w))).obj
      ((Scheme.Modules.pullback (curveChange j₂.1 j₂.2 u)).obj P₂U.L) ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) := by
    intro w
    obtain ⟨tr⟩ := nonempty_iso_unit_of_le (hUle₂ w) (hU₂ w)
    refine ⟨pb3 (rigSection z u (ζ w)) (curveChange j₂.1 j₂.2 u) (baseChangeSnd c₂ a₂) hD₂.poincare.L ≪≫
      (Scheme.Modules.pullbackCongr (hmaps₂ w)).app hD₂.poincare.L ≪≫
      (pb3 (U.ι ≫ rigSection z bB (ζ w)) (curveChange j₂.1 j₂.2 bB) (baseChangeSnd c₂ pr₂) hD₂.poincare.L).symm ≪≫
      (pb2 U.ι (rigSection z bB (ζ w)) _).symm ≪≫ tr⟩
  have triv₁ := AlgebraicGeometry.Scheme.Modules.nonempty_iso_unit_of_forall_pullback_rigSection_iso_unit z u ζ
    (fun w => ⟨w, hζpt w⟩) _ key₁
  have triv₂ := AlgebraicGeometry.Scheme.Modules.nonempty_iso_unit_of_forall_pullback_rigSection_iso_unit z u ζ
    (fun w => ⟨w, hζpt w⟩) _ key₂
  have hsq : curveChange j₁.1 j₁.2 u ≫ curveChange i₁.1 i₁.2 u = curveChange j₂.1 j₂.2 u ≫ curveChange i₂.1 i₂.2 u := by
    apply pullback.hom_ext
    · simp only [curveChange, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      exact congrArg (pullback.fst z u ≫ ·) pullback.condition
    · simp only [curveChange, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]

  obtain ⟨L, hL, α₁, α₂, -⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_isInvertible_pullback_curveChange_iso_of_closedCover x hXred c₁ c₂ z
      i₁ i₂ hjs j₁ j₂ (IsPullback.of_hasPullback i₁.1 i₂.1) u hsq P₁U.L P₁U.isInvertible P₂U.L P₂U.isInvertible
      (triv₁.some ≪≫ triv₂.some.symm)
  have hrig : Nonempty ((Scheme.Modules.pullback (rigSection x u ε)).obj L ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :=
    ⟨(Scheme.Modules.pullbackCongr (rigSection_curveChange i₁.1 i₁.2 hε u).symm).app L ≪≫
      (pb2 (rigSection c₁ u ε₁) (curveChange i₁.1 i₁.2 u) L).symm ≪≫
      (Scheme.Modules.pullback (rigSection c₁ u ε₁)).mapIso α₁ ≪≫ P₁U.rigidified.some⟩
  let M : RigidifiedLineBundle x ε u := ⟨L, hL, hrig⟩

  have hP₁U : FibrewiseAlgEquivZero P₁U := (algEquivZeroCut c₁ ε₁).pullback_mem _ _ a₁ _ hD₁.poincare_mem
  have hP₂U : FibrewiseAlgEquivZero P₂U := (algEquivZeroCut c₂ ε₂).pullback_mem _ _ a₂ _ hD₂.poincare_mem
  have hM : (algEquivZeroCut x ε).P u M := by
    intro K _ _ sK
    have h₁ := isAlgEquivZero_pullback_curveChange_fibre x c₁ i₁ u L P₁U α₁ hP₁U K sK
    have h₂ := isAlgEquivZero_pullback_curveChange_fibre x c₂ i₂ u L P₂U α₂ hP₂U K sK
    have hK := AlgebraicGeometry.RelPicard.isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves
      x hXred c₁ c₂ i₁ i₂ hjs hcr s hs hs0 K (sK ≫ u) _ (hL.pullback _) h₁ h₂
    have hK' := hK.pullback (pullbackLeftPullbackSndIso x u sK).hom (pullbackLeftPullbackSndIso_hom_snd x u sK)
    refine hK'.of_iso ?_
    exact pb2 _ _ L ≪≫ (Scheme.Modules.pullbackCongr ((pullbackLeftPullbackSndIso x u sK).hom_inv_id_assoc _)).app L

  refine ⟨(hD.classify u M hM).1, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst]
    have e1 : postComp ν₁ (hD.classify u M hM) = a₁ := by
      rw [hν₁, RepresentsRelSubPic.postComp_pullbackHom_classify]
      exact (hD₁.classify_unique u _ _ a₁ ⟨α₁.symm⟩).symm
    exact congrArg Subtype.val e1
  · rw [Category.assoc, pullback.lift_snd]
    have e2 : NeronModelInfra.schemeHomOverComp (hD.classify u M hM) ν₂ = a₂ := by
      refine hD₂.ext_of_iso u _ _ ⟨(hν₂ u (hD.classify u M hM)).some ≪≫
        Scheme.Modules.rigidifyMapIso _ _ ((Scheme.Modules.pullback _).mapIso (hD.classify_spec u M hM).some ≪≫ α₂) ≪≫
        (nonempty_rigidify_iso _ _ _ P₂U.rigidified).some⟩
    exact congrArg Subtype.val e2

end S_AlgebraicGeometry_RelPicard_exists_opens_section_restrictPair_of_twoGluedSmoothCurves
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_opens_section_restrictPair_of_twoGluedSmoothCurves (solution)
