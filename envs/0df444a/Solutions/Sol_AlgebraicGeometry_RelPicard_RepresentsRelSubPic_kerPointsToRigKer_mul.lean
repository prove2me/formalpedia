-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.kerPointsToRigKer_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/496ef18d-2514-5a96-86ea-1240b97332c5

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_RigKerDualNumber
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPointsToRigKer_mul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

private theorem fibrewiseAlgEquivZero_of_pullbackAlong_iso_unit_aux
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {T T₀ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₀ : T₀ ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t₀ t)
    (hψ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      ∃ s₀ : Spec (CommRingCat.of k) ⟶ T₀, s₀ ≫ ψ.1 = s)
    (M : RigidifiedLineBundle c ε t)
    (hM : Nonempty ((M.pullbackAlong ψ).L ≅ (RigidifiedLineBundle.unit (c := c) (ε := ε) t₀).L)) :
    FibrewiseAlgEquivZero M := by
  intro k _ _ s
  obtain ⟨s₀, hs₀⟩ := hψ k s
  subst hs₀

  let P := Limits.pullback (pullback.snd c t) (s₀ ≫ ψ.1)
  have hcomm : (pullback.fst (pullback.snd c t) (s₀ ≫ ψ.1) ≫ pullback.fst c t) ≫ c =
      (pullback.snd (pullback.snd c t) (s₀ ≫ ψ.1) ≫ s₀) ≫ t₀ := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
      Category.assoc, ψ.2, Category.assoc]
  let a : P ⟶ Limits.pullback c t₀ :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst c t) (pullback.snd _ _ ≫ s₀) hcomm
  let e' : P ⟶ Limits.pullback (pullback.snd c t₀) s₀ :=
    pullback.lift a (pullback.snd _ _) (by simp only [a, pullback.lift_snd])
  have he' : e' ≫ fibreAt c t₀ s₀ = fibreAt c t (s₀ ≫ ψ.1) := by
    simp only [e', fibreAt, pullback.lift_snd]
  have hfst' : e' ≫ pullback.fst (pullback.snd c t₀) s₀ ≫ baseChangeSnd c ψ =
      pullback.fst (pullback.snd c t) (s₀ ≫ ψ.1) := by
    apply pullback.hom_ext
    · simp only [e', a, baseChangeSnd, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Category.comp_id]
    · simp only [e', a, baseChangeSnd, Category.assoc, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc]
      rw [pullback.condition]

  have h₀ : IsAlgEquivZero (fibreAt c t₀ s₀)
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t₀) s₀)).obj (M.pullbackAlong ψ).L) :=
    (fibrewiseAlgEquivZero_unit (c := c) (ε := ε) t₀ k s₀).of_iso
      ((Scheme.Modules.pullback _).mapIso hM.some.symm)

  refine IsAlgEquivZero.of_iso ?_ (h₀.pullback e' he')
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (by simpa only [Category.assoc] using hfst')).app M.L

private theorem ker_restrict_iff_and_exists_unique_and_mul_aux
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {D : RelativePic0Designation R c} (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {T T₀ : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (ψ : SchemeHomOver t₀ t)
    (hψ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      ∃ s₀ : Spec (CommRingCat.of k) ⟶ T₀, s₀ ≫ ψ.1 = s) :
    letI L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h
    (∀ x : SchemeHomOver t D.toBase,
      GoodReductionJacobian.schemeHomOverComp ψ.1 ψ.2 x = L.one t₀ ↔
        Nonempty (((h.poincare.pullbackAlong x).pullbackAlong ψ).L ≅
          (RigidifiedLineBundle.unit (c := c) (ε := ε) t₀).L)) ∧
    (∀ M : RigidifiedLineBundle c ε t,
      Nonempty ((M.pullbackAlong ψ).L ≅ (RigidifiedLineBundle.unit (c := c) (ε := ε) t₀).L) →
        ∃! x : SchemeHomOver t D.toBase, Nonempty ((h.poincare.pullbackAlong x).L ≅ M.L)) ∧
    (∀ x y : SchemeHomOver t D.toBase,
      Nonempty ((h.poincare.pullbackAlong (L.mul t x y)).L ≅
        ((h.poincare.pullbackAlong x).tensor (h.poincare.pullbackAlong y)).L)) := by
  letI := RepresentsRelSubPic.grpObj (P := algEquivZeroGroupCut c ε) h
  refine ⟨fun x => ?_, fun M hM => ?_, fun x y => ?_⟩
  ·
    letI := (algEquivZeroGroupCut c ε).commGroupObj (Opposite.op (Over.mk t₀))
    have h1 := congrArg Subtype.val
      (RepresentsRelSubPic.homEquiv_one (P := algEquivZeroGroupCut c ε) h (Over.mk t₀))
    have one_iso : Nonempty ((h.poincare.pullbackAlong
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one t₀)).L ≅
          (RigidifiedLineBundle.unit (c := c) (ε := ε) t₀).L) :=
      Quotient.exact h1
    have comp_iso : ((h.poincare.pullbackAlong x).pullbackAlong ψ).L ≅
        (h.poincare.pullbackAlong (GoodReductionJacobian.schemeHomOverComp ψ.1 ψ.2 x)).L :=
      h.poincare.pullbackAlongPullbackAlongIso x ψ
    constructor
    · intro hx
      rw [← hx] at one_iso
      exact ⟨comp_iso ≪≫ one_iso.some⟩
    · rintro ⟨e⟩
      exact h.ext_of_iso t₀ _ _ ⟨comp_iso.symm ≪≫ e ≪≫ one_iso.some.symm⟩
  ·
    exact h.univ t M (fibrewiseAlgEquivZero_of_pullbackAlong_iso_unit_aux ψ hψ M hM)
  ·
    letI := (algEquivZeroGroupCut c ε).commGroupObj (Opposite.op (Over.mk t))
    have hm := congrArg Subtype.val
      (RepresentsRelSubPic.homEquiv_mul (P := algEquivZeroGroupCut c ε) h (Over.mk t)
        (schemeHomOverToOverHom x) (schemeHomOverToOverHom y))
    exact Quotient.exact hm

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (A : Type u) [CommRing A] [Algebra R A] :
    letI L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h
    ∀ (x y : { x : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)) D.toBase //
        dualNumberReduction R A ≫ x.1 = (L.one (Scheme.TwoAffineOpenCover.specMap R A)).1 })
      (hxy : dualNumberReduction R A ≫ (L.mul _ x.1 y.1).1 = (L.one (Scheme.TwoAffineOpenCover.specMap R A)).1),
      h.kerPointsToRigKer A ⟨L.mul _ x.1 y.1, hxy⟩ =
        RigKerDualNumber.mul c ε A (h.kerPointsToRigKer A x) (h.kerPointsToRigKer A y) := by
  intro x y hxy
  obtain ⟨-, -, hiii⟩ := ker_restrict_iff_and_exists_unique_and_mul_aux h (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)) (Scheme.TwoAffineOpenCover.specMap R A)
    (dualNumberReductionOver R A) (dualNumberReduction_catches_geometric_points R A)
  exact Quotient.sound (hiii x.1 y.1)

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPointsToRigKer_mul
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPointsToRigKer_mul (solution)
