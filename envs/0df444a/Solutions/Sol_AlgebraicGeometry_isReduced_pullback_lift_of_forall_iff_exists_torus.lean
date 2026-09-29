-- Prove2me | solution 1 for AlgebraicGeometry.isReduced_pullback_lift_of_forall_iff_exists_torus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/3f95ff05-a158-5caa-96fc-128f3cd17f8d

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isReduced_pullback_lift_of_forall_iff_exists_torus
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.SplitTorus ModularCurve ModularCurve.DRLevel

universe u

namespace FibTr1ca8f961

set_option backward.isDefEq.respectTransparency false

section Main

variable {κ : Type u} [Field κ] {G B : Scheme.{u}} (sG : G ⟶ Spec (CommRingCat.of κ)) (sB : B ⟶ Spec (CommRingCat.of κ))
  (LG : RelativeGroupLaw κ sG) (LB : RelativeGroupLaw κ sB)
  (abq : Fin 2 → SchemeHomOver sG sB)
  (habq : ∀ (i : Fin 2) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (a b : SchemeHomOver t sG),
    NeronModelInfra.schemeHomOverComp (LG.mul t a b) (abq i) =
      LB.mul t (NeronModelInfra.schemeHomOverComp a (abq i)) (NeronModelInfra.schemeHomOverComp b (abq i)))

noncomputable abbrev q : G ⟶ pullback sB sB := pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)

noncomputable abbrev e : Spec (CommRingCat.of κ) ⟶ B := (LB.one (𝟙 _)).1
noncomputable abbrev eBB : Spec (CommRingCat.of κ) ⟶ pullback sB sB :=
  pullback.lift (e sB LB) (e sB LB) rfl

theorem q_prᵢ (i : Fin 2) : q sG sB abq ≫ (if i = 0 then pullback.fst sB sB else pullback.snd sB sB) = (abq i).1 := by
  fin_cases i <;> simp

theorem one_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) : (LB.one t).1 = t ≫ e sB LB := by
  have := LB.one_natural (𝟙 _) t t (Category.comp_id _)
  exact (congrArg Subtype.val this).symm

include habq in

theorem comp_inv (i : Fin 2) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t sG) :
    NeronModelInfra.schemeHomOverComp (LG.inv t a) (abq i) = LB.inv t (NeronModelInfra.schemeHomOverComp a (abq i)) := by
  letI := LG.pointGroup t
  letI := LB.pointGroup t
  let φ : SchemeHomOver t sG →* SchemeHomOver t sB :=
    MonoidHom.mk' (fun a => NeronModelInfra.schemeHomOverComp a (abq i)) (habq i t)
  exact map_inv φ a

theorem forall_comp_eq_one_iff {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t sG) :
    (∀ i, NeronModelInfra.schemeHomOverComp a (abq i) = LB.one t) ↔ a.1 ≫ q sG sB abq = t ≫ eBB sB LB := by
  constructor
  · intro h
    apply pullback.hom_ext
    · simpa [one_coe sB LB t] using congrArg Subtype.val (h 0)
    · simpa [one_coe sB LB t] using congrArg Subtype.val (h 1)
  · intro h i
    apply Subtype.ext
    rw [one_coe sB LB t]
    fin_cases i
    · have := congrArg (· ≫ pullback.fst sB sB) h
      simpa using this
    · have := congrArg (· ≫ pullback.snd sB sB) h
      simpa using this

end Main

end FibTr1ca8f961

open FibTr1ca8f961 in
theorem solution
    {κ : Type u} [Field κ] [IsAlgClosed κ]
    {G B : Scheme.{u}} (sG : G ⟶ Spec (CommRingCat.of κ)) (sB : B ⟶ Spec (CommRingCat.of κ))
    (LG : RelativeGroupLaw κ sG) (LB : RelativeGroupLaw κ sB) (hsm : Smooth sG) [LocallyOfFiniteType sB]
    (abq : Fin 2 → SchemeHomOver sG sB)

    (habq : ∀ (i : Fin 2) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (a b : SchemeHomOver t sG),
      NeronModelInfra.schemeHomOverComp (LG.mul t a b) (abq i) =
        LB.mul t (NeronModelInfra.schemeHomOverComp a (abq i)) (NeronModelInfra.schemeHomOverComp b (abq i)))

    (hsurj : Surjective (pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)))

    (r : ℕ) (τ : SchemeHomOver (torusStr κ r) sG) (hτ : IsClosedImmersion τ.1)
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t sG),
      (∀ i, NeronModelInfra.schemeHomOverComp a (abq i) = LB.one t) ↔
        ∃ y : SchemeHomOver t (torusStr κ r), NeronModelInfra.schemeHomOverComp y τ = a)

    (b : Spec (CommRingCat.of κ) ⟶ pullback sB sB) (hb : b ≫ pullback.fst sB sB ≫ sB = 𝟙 _) :
    IsReduced (pullback (pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)) b) := by
  classical

  have hsG : q sG sB abq ≫ pullback.fst sB sB ≫ sB = sG := by
    rw [pullback.lift_fst_assoc]; exact (abq 0).2
  haveI : Smooth sG := hsm
  haveI : LocallyOfFiniteType (q sG sB abq ≫ pullback.fst sB sB ≫ sB) := by rw [hsG]; infer_instance
  haveI : LocallyOfFiniteType (q sG sB abq) := locallyOfFiniteType_of_comp (q sG sB abq) (pullback.fst sB sB ≫ sB)
  haveI : Mono τ.1 := by haveI := hτ; infer_instance
  change IsReduced (pullback (q sG sB abq) b)

  have inv_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (t' : T' ⟶ Spec (CommRingCat.of κ))
      (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t sG),
      GoodReductionJacobian.schemeHomOverComp ψ hψ (LG.inv t x) = LG.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
    intro T T' t t' ψ hψ x
    letI := LG.pointGroup t'
    have h : LG.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (LG.inv t x)) (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
        LG.one t' := by
      rw [← LG.mul_natural, LG.inv_mul_cancel, LG.one_natural]
    exact (inv_eq_of_mul_eq_one_left (G := SchemeHomOver t' sG) h).symm

  rcases isEmpty_or_nonempty ↥(pullback (q sG sB abq) b) with hX | hX
  · exact isReduced_of_isOpenImmersion (pullback.snd (q sG sB abq) b)

  haveI : JacobsonSpace ↥(pullback (q sG sB abq) b) := LocallyOfFiniteType.jacobsonSpace (pullback.snd (q sG sB abq) b)
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (X := ↥(pullback (q sG sB abq) b)) Set.univ_nonempty
    isClosed_univ.isLocallyClosed
  let z : Spec (CommRingCat.of κ) ⟶ pullback (q sG sB abq) b := pointOfClosedPoint (pullback.snd (q sG sB abq) b) x hx
  have hz : z ≫ pullback.snd (q sG sB abq) b = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  let g : Spec (CommRingCat.of κ) ⟶ G := z ≫ pullback.fst (q sG sB abq) b
  have hgq : g ≫ q sG sB abq = b := by
    rw [Category.assoc, pullback.condition, reassoc_of% hz]
  have hg : g ≫ sG = 𝟙 _ := by rw [← hsG, reassoc_of% hgq, hb]

  let gT : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)), SchemeHomOver t sG :=
    fun t => ⟨t ≫ g, by rw [Category.assoc, hg, Category.comp_id]⟩
  have gT_nat : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (t' : T' ⟶ Spec (CommRingCat.of κ))
      (ψ : T' ⟶ T) (hψ : ψ ≫ t = t'), GoodReductionJacobian.schemeHomOverComp ψ hψ (gT t) = gT t' := by
    intro T T' t t' ψ hψ
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, gT]
    rw [← Category.assoc, hψ]
  have gT_abq : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (i : Fin 2),
      (NeronModelInfra.schemeHomOverComp (gT t) (abq i)).1 =
        t ≫ b ≫ (if i = 0 then pullback.fst sB sB else pullback.snd sB sB) := by
    intro T t i
    change (t ≫ g) ≫ (abq i).1 = _
    rw [← q_prᵢ sG sB abq i, ← reassoc_of% hgq, Category.assoc]

  let k₁ := pullback.fst (q sG sB abq) (eBB sB LB)
  let k₂ := pullback.snd (q sG sB abq) (eBB sB LB)
  have hk : k₁ ≫ sG = k₂ := by
    have e1 : k₁ ≫ sG = k₁ ≫ q sG sB abq ≫ pullback.fst sB sB ≫ sB := by rw [hsG]
    rw [e1, pullback.condition_assoc, pullback.lift_fst_assoc, (LB.one (𝟙 _)).2, Category.comp_id]
  let aK : SchemeHomOver (k₁ ≫ sG) sG := ⟨k₁, rfl⟩
  have haK : ∀ i, NeronModelInfra.schemeHomOverComp aK (abq i) = LB.one _ :=
    (forall_comp_eq_one_iff sG sB LB abq (k₁ ≫ sG) aK).mpr (pullback.condition.trans (by rw [hk]))

  have hτq : τ.1 ≫ q sG sB abq = torusStr κ r ≫ eBB sB LB :=
    (forall_comp_eq_one_iff sG sB LB abq (torusStr κ r) τ).mp
      ((hker (torusStr κ r) τ).mpr ⟨⟨𝟙 _, Category.id_comp _⟩, Subtype.ext (Category.id_comp _)⟩)
  let s : torusScheme κ r ⟶ pullback (q sG sB abq) (eBB sB LB) := pullback.lift τ.1 (torusStr κ r) hτq
  obtain ⟨y, hy⟩ := (hker (k₁ ≫ sG) aK).mp haK
  have hy1 : y.1 ≫ τ.1 = k₁ := congrArg Subtype.val hy
  have hys : y.1 ≫ s = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hy1, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, y.2, hk, Category.id_comp]
  have hsy : s ≫ y.1 = 𝟙 _ := by
    rw [← cancel_mono τ.1, Category.assoc, hy1, pullback.lift_fst, Category.id_comp]
  haveI : IsIso y.1 := ⟨s, hys, hsy⟩
  haveI : IsReduced (pullback (q sG sB abq) (eBB sB LB)) := isReduced_of_isOpenImmersion y.1

  let x₁ := pullback.fst (q sG sB abq) b
  let x₂ := pullback.snd (q sG sB abq) b
  have hxx : x₁ ≫ sG = x₂ := by
    have e1 : x₁ ≫ sG = x₁ ≫ q sG sB abq ≫ pullback.fst sB sB ≫ sB := by rw [hsG]
    rw [e1, pullback.condition_assoc, hb, Category.comp_id]
  let aX : SchemeHomOver (x₁ ≫ sG) sG := ⟨x₁, rfl⟩
  have haX : ∀ i, NeronModelInfra.schemeHomOverComp aX (abq i) = NeronModelInfra.schemeHomOverComp (gT (x₁ ≫ sG)) (abq i) := by
    intro i
    apply Subtype.ext
    rw [gT_abq]
    change x₁ ≫ (abq i).1 = _
    rw [← q_prᵢ sG sB abq i, pullback.condition_assoc, ← reassoc_of% hxx, Category.assoc]

  let nX : SchemeHomOver (x₁ ≫ sG) sG := LG.mul _ aX (LG.inv _ (gT _))
  have hnX : ∀ i, NeronModelInfra.schemeHomOverComp nX (abq i) = LB.one _ := by
    intro i
    rw [habq, comp_inv sG sB LG LB abq habq, haX, LB.mul_inv_cancel]
  let B' : pullback (q sG sB abq) b ⟶ pullback (q sG sB abq) (eBB sB LB) :=
    pullback.lift nX.1 (x₁ ≫ sG) ((forall_comp_eq_one_iff sG sB LB abq _ nX).mp hnX)
  have hB'k : B' ≫ k₁ = nX.1 := pullback.lift_fst _ _ _
  have hB' : B' ≫ (k₁ ≫ sG) = x₁ ≫ sG := by rw [← Category.assoc, hB'k]; exact nX.2

  let mK : SchemeHomOver (k₁ ≫ sG) sG := LG.mul _ aK (gT _)
  have hmK : mK.1 ≫ q sG sB abq = (k₁ ≫ sG) ≫ b := by
    apply pullback.hom_ext
    · have h0 := congrArg Subtype.val (habq 0 _ aK (gT _))
      rw [haK 0, LB.one_mul] at h0
      change (mK.1 ≫ (abq 0).1) = _ at h0
      rw [Category.assoc, pullback.lift_fst, h0, gT_abq, Category.assoc]
      simp
    · have h1 := congrArg Subtype.val (habq 1 _ aK (gT _))
      rw [haK 1, LB.one_mul] at h1
      change (mK.1 ≫ (abq 1).1) = _ at h1
      rw [Category.assoc, pullback.lift_snd, h1, gT_abq, Category.assoc]
      simp
  let F : pullback (q sG sB abq) (eBB sB LB) ⟶ pullback (q sG sB abq) b := pullback.lift mK.1 (k₁ ≫ sG) hmK
  have hFx : F ≫ x₁ = mK.1 := pullback.lift_fst _ _ _
  have hF : F ≫ (x₁ ≫ sG) = k₁ ≫ sG := by rw [← Category.assoc, hFx]; exact mK.2

  have hBF : B' ≫ F = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hFx, Category.id_comp]
      have hnat := LG.mul_natural _ _ B' hB' aK (gT _)
      have e1 : GoodReductionJacobian.schemeHomOverComp B' hB' aK = nX := Subtype.ext hB'k
      rw [e1, gT_nat] at hnat
      have e2 : LG.mul _ nX (gT (x₁ ≫ sG)) = aX := by
        rw [LG.mul_assoc, LG.inv_mul_cancel, LG.mul_one]
      rw [e2] at hnat
      exact congrArg Subtype.val hnat
    · rw [Category.assoc, pullback.lift_snd, hB', hxx, Category.id_comp]

  have hFB : F ≫ B' = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hB'k, Category.id_comp]
      have hnat := LG.mul_natural _ _ F hF aX (LG.inv _ (gT _))
      have e1 : GoodReductionJacobian.schemeHomOverComp F hF aX = mK := Subtype.ext hFx
      rw [e1, inv_natural, gT_nat] at hnat
      have e2 : LG.mul _ mK (LG.inv _ (gT (k₁ ≫ sG))) = aK := by
        rw [LG.mul_assoc, LG.mul_inv_cancel, LG.mul_one]
      rw [e2] at hnat
      exact congrArg Subtype.val hnat
    · rw [Category.assoc, pullback.lift_snd, hF, hk, Category.id_comp]
  haveI : IsIso B' := ⟨F, hBF, hFB⟩
  exact isReduced_of_isOpenImmersion B'

end S_AlgebraicGeometry_isReduced_pullback_lift_of_forall_iff_exists_torus
end P2MW
export P2MW.S_AlgebraicGeometry_isReduced_pullback_lift_of_forall_iff_exists_torus (solution)
