-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_pullbackAlong_mul_iso_tensor_ofInvertible_norm_pullback_poincare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a4ca83a7-67bf-5ea3-9a59-4774783c8df6

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_rigidify_pullback_tensor_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_rigidify
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_flat_mul_fst_snd
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullbackAlong_mul_iso_tensor_ofInvertible_norm_pullback_poincare

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

p2m_open "AlgebraicGeometry.Scheme.Modules"

namespace ModularCurve
namespace PrimBody

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {R : Type} [CommRing R] {C C' : Scheme.{0}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}

theorem isFinite_curveChange' (π : C' ⟶ C) (hπ : π ≫ c = c') [IsFinite π] {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    IsFinite (curveChange π hπ t) :=
  MorphismProperty.pullbackMap (P := @IsFinite) ‹IsFinite π› (inferInstance : IsFinite (𝟙 T)) hπ.symm
    (Category.id_comp t).symm

theorem surjective_curveChange' (π : C' ⟶ C) (hπ : π ≫ c = c') [Surjective π] {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Surjective (curveChange π hπ t) :=
  MorphismProperty.pullbackMap (P := @Surjective) ‹Surjective π› (inferInstance : Surjective (𝟙 T)) hπ.symm
    (Category.id_comp t).symm

theorem isPullback_curveChange_baseChangeSnd (π : C' ⟶ C) (hπ : π ≫ c = c')
    {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) :
    IsPullback (baseChangeSnd c' ψ) (curveChange π hπ t') (curveChange π hπ t) (baseChangeSnd c ψ) := by

  have sqC : ∀ {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of R)),
      IsPullback (curveChange π hπ s) (pullback.fst c' s) (pullback.fst c s) π := by
    intro S s
    have big : IsPullback (curveChange π hπ s ≫ pullback.snd c s) (pullback.fst c' s) s (π ≫ c) := by
      rw [curveChange_snd, hπ]
      exact (IsPullback.of_hasPullback c' s).flip
    have hcomm : curveChange π hπ s ≫ pullback.fst c s = pullback.fst c' s ≫ π := by
      simp only [curveChange, pullback.lift_fst]
    exact IsPullback.of_right big hcomm (IsPullback.of_hasPullback c s).flip

  have h1 : baseChangeSnd c' ψ ≫ pullback.fst c' t = pullback.fst c' t' := by
    simp only [baseChangeSnd, pullback.map]; rw [pullback.lift_fst, Category.comp_id]
  have h2 : baseChangeSnd c ψ ≫ pullback.fst c t = pullback.fst c t' := by
    simp only [baseChangeSnd, pullback.map]; rw [pullback.lift_fst, Category.comp_id]
  have big : IsPullback (baseChangeSnd c' ψ ≫ pullback.fst c' t) (curveChange π hπ t') π
      (baseChangeSnd c ψ ≫ pullback.fst c t) := by
    rw [h1, h2]; exact (sqC t').flip
  exact (IsPullback.of_right big (curveChange_baseChangeSnd π hπ ψ).symm (sqC t).flip)

theorem flat_baseChangeSnd {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) [Flat ψ.1] : Flat (baseChangeSnd c ψ) :=
  MorphismProperty.pullbackMap (P := @Flat) (inferInstance : Flat (𝟙 C)) ‹Flat ψ.1› (by simp) (by simpa using ψ.2.symm)

def shuffle {V : Type 1} [Category.{0} V] [MonoidalCategory V] [SymmetricCategory V] (A B X Y : V) :
    (A ⊗ B) ⊗ (X ⊗ Y) ≅ (A ⊗ X) ⊗ (B ⊗ Y) :=
  (α_ A B (X ⊗ Y)) ≪≫ (Iso.refl A ⊗ᵢ ((α_ B X Y).symm ≪≫ (β_ B X ⊗ᵢ Iso.refl Y) ≪≫ α_ X B Y)) ≪≫ (α_ A X (B ⊗ Y)).symm

theorem nonempty_rigidify_tensor_iso {T P : Scheme.{0}} (σ : T ⟶ P) (q : P ⟶ T) {A B : P.Modules}
    (hA : Scheme.Modules.IsInvertible A) (hB : Scheme.Modules.IsInvertible B) :
    Nonempty (Scheme.Modules.rigidify σ q (A ⊗ B) ≅ Scheme.Modules.rigidify σ q A ⊗ Scheme.Modules.rigidify σ q B) := by
  rw [Scheme.Modules.rigidify_def, Scheme.Modules.rigidify_def, Scheme.Modules.rigidify_def]
  obtain ⟨edual⟩ := (hA.pullback σ).dual_tensor (hB.pullback σ)
  refine ⟨(Iso.refl _ ⊗ᵢ ((Scheme.Modules.pullback q).mapIso
      (Scheme.Modules.dualMapIso (Scheme.Modules.pullbackTensorObjIso σ A B) ≪≫ edual) ≪≫
      Scheme.Modules.pullbackTensorObjIso q _ _)) ≪≫ shuffle _ _ _ _⟩

end ModularCurve.PrimBody

open ModularCurve.PrimBody in

theorem solution

    (R : Type) [CommRing R]
    {C C' : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R)) (c' : C' ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

    (π₁ π₂ : SchemeHomOver c' c) [IsFinite π₂.1] [Surjective π₂.1]

    (D : RelativePic0Designation R c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

    [IsIntegral ↑(pullback c' D.toBase)] [IsIntegral ↑(pullback c D.toBase)]
    (hnorm : ∀ U : (pullback c D.toBase).Opens, IsAffineOpen U →
      IsIntegrallyClosed Γ(pullback c D.toBase, U))

    [Flat D.toBase] [LocallyOfFiniteType D.toBase]
    [IsIntegral ↑(pullback c' (pullback.fst D.toBase D.toBase ≫ D.toBase))]
    [IsIntegral ↑(pullback c (pullback.fst D.toBase D.toBase ≫ D.toBase))]
    (hnorm₂ : ∀ U : (pullback c (pullback.fst D.toBase D.toBase ≫ D.toBase)).Opens, IsAffineOpen U →
      IsIntegrallyClosed Γ(pullback c (pullback.fst D.toBase D.toBase ≫ D.toBase), U))

    (Nm : ∀ ⦃X Y : Scheme.{0}⦄, (X ⟶ Y) → X.Modules → Y.Modules)
    (hNm :
      ∀ ⦃X Y : Scheme.{0}⦄ (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral X] [IsIntegral Y],
        (∀ U : Y.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y, U)) →

        (∀ L : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible (Nm π L)) ∧

        (∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Nonempty (L ≅ L') →
          Nonempty (Nm π L ≅ Nm π L')) ∧

        (∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
          Nonempty (Nm π (L ⊗ L') ≅ Nm π L ⊗ Nm π L')) ∧

        Nonempty (Nm π (𝟙_ X.Modules) ≅ 𝟙_ Y.Modules) ∧

        (∀ ⦃X' Y' : Scheme.{0}⦄ (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X), IsPullback g' π' π g →
          ∀ [Flat g] [IsIntegral X'] [IsIntegral Y'],
          (∀ U : Y'.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y', U)) →
          ∀ L : X.Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback g).obj (Nm π L) ≅
              Nm π' ((Scheme.Modules.pullback g').obj L))) ∧

        (∀ (V : Y.Opens) (d : ℕ), Flat (π ∣_ V) → LocallyOfFinitePresentation (π ∣_ V) →
          (∀ y : V, (π ∣_ V).finrank y = d) →
          ∀ L : X.Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback V.ι).obj (Nm π L) ≅
              Scheme.Modules.normModule (π ∣_ V) d ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L))))
    (hinv : Scheme.Modules.IsInvertible
      (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)))
    {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase) :
    Nonempty (((RigidifiedLineBundle.ofInvertible (ε := ε) (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) hinv).pullbackAlong
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s x y)).L ≅
      (((RigidifiedLineBundle.ofInvertible (ε := ε) (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) hinv).pullbackAlong x).tensor
        ((RigidifiedLineBundle.ofInvertible (ε := ε) (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) hinv).pullbackAlong y)).L) := by
  let M := (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L))
  let M' := RigidifiedLineBundle.ofInvertible (ε := ε) M hinv
  let t₂ : pullback D.toBase D.toBase ⟶ Spec (CommRingCat.of R) := pullback.fst D.toBase D.toBase ≫ D.toBase
  let pr₁D : SchemeHomOver t₂ D.toBase := ⟨pullback.fst D.toBase D.toBase, rfl⟩
  let pr₂D : SchemeHomOver t₂ D.toBase := ⟨pullback.snd D.toBase D.toBase, pullback.condition.symm⟩
  let G := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
  let mulD : SchemeHomOver t₂ D.toBase := G.mul t₂ pr₁D pr₂D

  have univ : Nonempty ((M'.pullbackAlong mulD).L ≅ ((M'.pullbackAlong pr₁D).tensor (M'.pullbackAlong pr₂D)).L) := by
    haveI := ModularCurve.PrimBody.isFinite_curveChange' π₂.1 π₂.2 D.toBase
    haveI := ModularCurve.PrimBody.surjective_curveChange' π₂.1 π₂.2 D.toBase
    haveI := ModularCurve.PrimBody.isFinite_curveChange' π₂.1 π₂.2 t₂
    haveI := ModularCurve.PrimBody.surjective_curveChange' π₂.1 π₂.2 t₂
    obtain ⟨h0, ha, hb, -, hd, -⟩ := hNm (curveChange π₂.1 π₂.2 D.toBase) hnorm
    obtain ⟨h0₂, ha₂, hb₂, -, -, -⟩ := hNm (curveChange π₂.1 π₂.2 t₂) hnorm₂

    let P : (pullback c D.toBase).Modules := hD.poincare.L
    let L₁ : (pullback c' D.toBase).Modules := (Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj P
    have hP : Scheme.Modules.IsInvertible P := hD.poincare.isInvertible
    have hL₁ : Scheme.Modules.IsInvertible L₁ := hP.pullback _

    have U1 : ∀ (g : SchemeHomOver t₂ D.toBase) [Flat g.1],
        Nonempty ((Scheme.Modules.pullback (baseChangeSnd c g)).obj M ≅
          Nm (curveChange π₂.1 π₂.2 t₂)
            ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 t₂)).obj ((Scheme.Modules.pullback (baseChangeSnd c g)).obj P))) := by
      intro g _
      haveI : Flat (baseChangeSnd c g) := ModularCurve.PrimBody.flat_baseChangeSnd g
      obtain ⟨e1⟩ := hd (baseChangeSnd c g) (curveChange π₂.1 π₂.2 t₂) (baseChangeSnd c' g)
        (ModularCurve.PrimBody.isPullback_curveChange_baseChangeSnd π₂.1 π₂.2 g) hnorm₂ L₁ hL₁

      have e2 : (Scheme.Modules.pullback (baseChangeSnd c' g)).obj L₁ ≅
          (Scheme.Modules.pullback (curveChange π₁.1 π₁.2 t₂)).obj ((Scheme.Modules.pullback (baseChangeSnd c g)).obj P) :=
        (Scheme.Modules.pullbackComp _ _).app P ≪≫
          (Scheme.Modules.pullbackCongr (curveChange_baseChangeSnd π₁.1 π₁.2 g).symm).app P ≪≫
          ((Scheme.Modules.pullbackComp _ _).app P).symm
      exact ⟨e1 ≪≫ (ha₂ _ _ (hL₁.pullback _) ⟨e2⟩).some⟩

    letI := RepresentsRelSubPic.grpObj (P := algEquivZeroGroupCut c ε) hD
    letI := (algEquivZeroGroupCut c ε).commGroupObj (Opposite.op (Over.mk t₂))
    have U2 : Nonempty ((Scheme.Modules.pullback (baseChangeSnd c mulD)).obj P ≅
        (Scheme.Modules.pullback (baseChangeSnd c pr₁D)).obj P ⊗ (Scheme.Modules.pullback (baseChangeSnd c pr₂D)).obj P) :=
      Quotient.exact (congrArg Subtype.val
        (RepresentsRelSubPic.homEquiv_mul (P := algEquivZeroGroupCut c ε) hD (Over.mk t₂)
          (schemeHomOverToOverHom pr₁D) (schemeHomOverToOverHom pr₂D)))

    haveI : Flat mulD.1 :=
      AlgebraicGeometry.RelPicard.RepresentsRelSubPic.flat_mul_fst_snd (P := algEquivZeroGroupCut c ε) hD
    haveI : Flat pr₁D.1 := by show Flat (pullback.fst D.toBase D.toBase); infer_instance
    haveI : Flat pr₂D.1 := by show Flat (pullback.snd D.toBase D.toBase); infer_instance
    let Q : SchemeHomOver t₂ D.toBase → (pullback c' t₂).Modules := fun g =>
      (Scheme.Modules.pullback (curveChange π₁.1 π₁.2 t₂)).obj ((Scheme.Modules.pullback (baseChangeSnd c g)).obj P)
    have hQ : ∀ g, Scheme.Modules.IsInvertible (Q g) := fun g => (hP.pullback _).pullback _
    have core : Nonempty ((Scheme.Modules.pullback (baseChangeSnd c mulD)).obj M ≅
        (Scheme.Modules.pullback (baseChangeSnd c pr₁D)).obj M ⊗ (Scheme.Modules.pullback (baseChangeSnd c pr₂D)).obj M) := by
      obtain ⟨em⟩ := U1 mulD
      obtain ⟨e1⟩ := U1 pr₁D
      obtain ⟨e2⟩ := U1 pr₂D

      have eQ : Q mulD ≅ Q pr₁D ⊗ Q pr₂D :=
        (Scheme.Modules.pullback (curveChange π₁.1 π₁.2 t₂)).mapIso U2.some ≪≫
          Scheme.Modules.pullbackTensorObjIso _ _ _
      obtain ⟨ea⟩ := ha₂ _ _ (hQ mulD) ⟨eQ⟩
      obtain ⟨ebb⟩ := hb₂ _ _ (hQ pr₁D) (hQ pr₂D)
      exact ⟨em ≪≫ ea ≪≫ ebb ≪≫ (e1.symm ⊗ᵢ e2.symm)⟩

    have F : ∀ g : SchemeHomOver t₂ D.toBase, Nonempty ((M'.pullbackAlong g).L ≅
        Scheme.Modules.rigidify (rigSection c t₂ ε) (pullback.snd c t₂) ((Scheme.Modules.pullback (baseChangeSnd c g)).obj M)) :=
      fun g => Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso g.1 (baseChangeSnd c g)
        (rigSection_baseChangeSnd c ε g) (by simp only [baseChangeSnd, pullback.map]; exact pullback.lift_snd _ _ _) hinv
    obtain ⟨ec⟩ := core
    obtain ⟨ert⟩ := ModularCurve.PrimBody.nonempty_rigidify_tensor_iso (rigSection c t₂ ε) (pullback.snd c t₂)
      (hinv.pullback (baseChangeSnd c pr₁D)) (hinv.pullback (baseChangeSnd c pr₂D))
    exact ⟨(F mulD).some ≪≫ Scheme.Modules.rigidifyMapIso _ _ ec ≪≫ ert ≪≫ ((F pr₁D).some.symm ⊗ᵢ (F pr₂D).some.symm)⟩

  let pair : SchemeHomOver s t₂ :=
    ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm), by
      show pullback.lift x.1 y.1 _ ≫ (pullback.fst D.toBase D.toBase ≫ D.toBase) = s
      rw [pullback.lift_fst_assoc, x.2]⟩
  have hx : postComp pr₁D pair = x := Subtype.ext (pullback.lift_fst _ _ _)
  have hy : postComp pr₂D pair = y := Subtype.ext (pullback.lift_snd _ _ _)
  have hmul : postComp mulD pair = G.mul s x y := by
    have nat := G.mul_natural t₂ s pair.1 pair.2 pr₁D pr₂D

    have e0 : ∀ a : SchemeHomOver t₂ D.toBase,
        GoodReductionJacobian.schemeHomOverComp pair.1 pair.2 a = postComp a pair := fun a => Subtype.ext rfl
    rw [e0, e0, e0, hx, hy] at nat
    exact nat

  have ecomp : ∀ a : SchemeHomOver t₂ D.toBase,
      (M'.pullbackAlong (postComp a pair)).L ≅ ((M'.pullbackAlong a).pullbackAlong pair).L := fun a =>
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c a pair).symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp (baseChangeSnd c pair) (baseChangeSnd c a)).app _).symm
  have eL : (M'.pullbackAlong (G.mul s x y)).L ≅ ((M'.pullbackAlong mulD).pullbackAlong pair).L :=
    (Scheme.Modules.pullbackCongr (show baseChangeSnd c (G.mul s x y) = baseChangeSnd c (postComp mulD pair)
      by rw [hmul])).app _ ≪≫ ecomp mulD
  have eX : ((M'.pullbackAlong pr₁D).pullbackAlong pair).L ≅ (M'.pullbackAlong x).L :=
    (ecomp pr₁D).symm ≪≫ (Scheme.Modules.pullbackCongr (show baseChangeSnd c (postComp pr₁D pair) =
      baseChangeSnd c x by rw [hx])).app _
  have eY : ((M'.pullbackAlong pr₂D).pullbackAlong pair).L ≅ (M'.pullbackAlong y).L :=
    (ecomp pr₂D).symm ≪≫ (Scheme.Modules.pullbackCongr (show baseChangeSnd c (postComp pr₂D pair) =
      baseChangeSnd c y by rw [hy])).app _
  exact ⟨eL ≪≫ (Scheme.Modules.pullback (baseChangeSnd c pair)).mapIso univ.some ≪≫
    (RigidifiedLineBundle.nonempty_tensor_pullbackAlong_iso pair _ _).some ≪≫ (eX ⊗ᵢ eY)⟩

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullbackAlong_mul_iso_tensor_ofInvertible_norm_pullback_poincare
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullbackAlong_mul_iso_tensor_ofInvertible_norm_pullback_poincare (solution)
