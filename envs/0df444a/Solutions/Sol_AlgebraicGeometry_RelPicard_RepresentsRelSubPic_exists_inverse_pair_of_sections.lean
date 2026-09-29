-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_inverse_pair_of_sections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/e2ee5e1a-fb82-5dcb-95d6-31362ee9af5a

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_hom_of_transform
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_inverse_pair_of_sections

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard"

universe u

noncomputable section

namespace Sub2c

section Monoidal

variable {𝒞 : Type*} [Category 𝒞] [MonoidalCategory 𝒞] [SymmetricCategory 𝒞]

def inverseIso {X X' Q Q' : 𝒞} (eX : X ≅ X') (hQ : X ⊗ Q ≅ 𝟙_ 𝒞) (hQ' : X' ⊗ Q' ≅ 𝟙_ 𝒞) : Q ≅ Q' :=
  (ρ_ Q).symm ≪≫ whiskerLeftIso Q hQ'.symm ≪≫ (α_ Q X' Q').symm ≪≫
    whiskerRightIso ((β_ Q X') ≪≫ whiskerRightIso eX.symm Q ≪≫ hQ) Q' ≪≫ λ_ Q'

def inverseOfIso {X Y Q : 𝒞} (eX : X ≅ Y) (hQ : X ⊗ Q ≅ 𝟙_ 𝒞) : Y ⊗ Q ≅ 𝟙_ 𝒞 :=
  whiskerRightIso eX.symm Q ≪≫ hQ

end Monoidal

section Modules

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

theorem rigSection_snd {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    rigSection c t ε ≫ pullback.snd c t = 𝟙 T := by
  simp only [rigSection, pullback.lift_snd]

def sectionPullbackIso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (Q : T.Modules) :
    (Scheme.Modules.pullback (rigSection c t ε)).obj ((Scheme.Modules.pullback (pullback.snd c t)).obj Q) ≅ Q :=
  (Scheme.Modules.pullbackComp _ _).app Q ≪≫
    (Scheme.Modules.pullbackCongr (rigSection_snd t ε)).app Q ≪≫
    (Scheme.Modules.pullbackId _).app Q

theorem baseChangeSnd_snd {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) : baseChangeSnd c ψ ≫ pullback.snd c t = pullback.snd c t' ≫ ψ.1 := by
  simp only [baseChangeSnd, pullback.lift_snd]

def baseChangePullbackIso {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (Q : T.Modules) :
    (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj ((Scheme.Modules.pullback (pullback.snd c t)).obj Q) ≅
      (Scheme.Modules.pullback (pullback.snd c t')).obj ((Scheme.Modules.pullback ψ.1).obj Q) :=
  (Scheme.Modules.pullbackComp _ _).app Q ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_snd ψ)).app Q ≪≫
    ((Scheme.Modules.pullbackComp _ _).app Q).symm

end Modules

theorem nonempty_iso_unit_of_field {k : Type u} [Field k] (Q : (Spec (CommRingCat.of k)).Modules)
    (hQ : Scheme.Modules.IsInvertible Q) : Nonempty (Q ≅ 𝟙_ (Spec (CommRingCat.of k)).Modules) := by
  obtain ⟨U, hx, ⟨eU⟩⟩ := hQ.1 default
  have hU : U = ⊤ := by
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    rw [Subsingleton.elim y default]
    exact hx
  subst hU
  let X := Spec (CommRingCat.of k)
  let i : (⊤ : X.Opens).toScheme ≅ X := X.topIso
  have hi : i.inv ≫ (⊤ : X.Opens).ι = 𝟙 X := by
    rw [← Scheme.topIso_hom]; exact i.inv_hom_id
  exact ⟨((Scheme.Modules.pullbackId _).app Q).symm ≪≫
    (Scheme.Modules.pullbackCongr hi.symm).app Q ≪≫
    ((Scheme.Modules.pullbackComp _ _).app Q).symm ≪≫
    (Scheme.Modules.pullback i.inv).mapIso eU ≪≫
    Scheme.Modules.pullbackUnitIso i.inv⟩

section Twist

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  (ε₁ ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

noncomputable def qinv {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε₁ t) : T.Modules :=
  (M.isInvertible.pullback (rigSection c t ε₂)).exists_tensor_inverse.choose

theorem qinv_isInvertible {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε₁ t) :
    Scheme.Modules.IsInvertible (qinv ε₁ ε₂ M) :=
  (M.isInvertible.pullback (rigSection c t ε₂)).exists_tensor_inverse.choose_spec.1

noncomputable def qinvIso {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε₁ t) :
    (Scheme.Modules.pullback (rigSection c t ε₂)).obj M.L ⊗ qinv ε₁ ε₂ M ≅ 𝟙_ _ :=
  (M.isInvertible.pullback (rigSection c t ε₂)).exists_tensor_inverse.choose_spec.2.some

noncomputable def twist {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε₁ t) :
    RigidifiedLineBundle c ε₂ t where
  L := M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj (qinv ε₁ ε₂ M)
  isInvertible := M.isInvertible.tensor ((qinv_isInvertible ε₁ ε₂ M).pullback _)
  rigidified := ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    whiskerLeftIso _ (sectionPullbackIso t ε₂ _) ≪≫ qinvIso ε₁ ε₂ M⟩

theorem twist_L {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε₁ t) :
    (twist ε₁ ε₂ M).L = M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj (qinv ε₁ ε₂ M) := rfl

def twistIsoOfInverse {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε₁ t)
    (Q : T.Modules) (hQ : (Scheme.Modules.pullback (rigSection c t ε₂)).obj M.L ⊗ Q ≅ 𝟙_ _) :
    (twist ε₁ ε₂ M).L ≅ M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj Q :=
  whiskerLeftIso M.L ((Scheme.Modules.pullback _).mapIso (inverseIso (Iso.refl _) (qinvIso ε₁ ε₂ M) hQ))

theorem twist_congr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c ε₁ t)
    (e : Nonempty (M.L ≅ M'.L)) : Nonempty ((twist ε₁ ε₂ M).L ≅ (twist ε₁ ε₂ M').L) :=
  ⟨e.some ⊗ᵢ (Scheme.Modules.pullback _).mapIso
    (inverseIso ((Scheme.Modules.pullback _).mapIso e.some) (qinvIso ε₁ ε₂ M) (qinvIso ε₁ ε₂ M'))⟩

theorem twist_natural {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε₁ t) :
    Nonempty (((twist ε₁ ε₂ M).pullbackAlong ψ).L ≅ (twist ε₁ ε₂ (M.pullbackAlong ψ)).L) := by

  have hX : (Scheme.Modules.pullback (rigSection c t' ε₂)).obj (M.pullbackAlong ψ).L ≅
      (Scheme.Modules.pullback ψ.1).obj ((Scheme.Modules.pullback (rigSection c t ε₂)).obj M.L) :=
    (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
      (Scheme.Modules.pullbackCongr (rigSection_baseChangeSnd c ε₂ ψ)).app M.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M.L).symm
  have hQ : (Scheme.Modules.pullback ψ.1).obj ((Scheme.Modules.pullback (rigSection c t ε₂)).obj M.L) ⊗
      (Scheme.Modules.pullback ψ.1).obj (qinv ε₁ ε₂ M) ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫
      (Scheme.Modules.pullback ψ.1).mapIso (qinvIso ε₁ ε₂ M) ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _
  have hq : (Scheme.Modules.pullback ψ.1).obj (qinv ε₁ ε₂ M) ≅ qinv ε₁ ε₂ (M.pullbackAlong ψ) :=
    inverseIso hX.symm hQ (qinvIso ε₁ ε₂ (M.pullbackAlong ψ))
  exact ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    whiskerLeftIso _ (baseChangePullbackIso ψ _ ≪≫ (Scheme.Modules.pullback _).mapIso hq)⟩

theorem twist_cut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε₁ t)
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (twist ε₁ ε₂ M) := by
  intro k _ _ s

  let φ := pullback.fst (pullback.snd c t) s
  have hφ : φ ≫ pullback.snd c t = fibreAt c t s ≫ s := pullback.condition
  obtain ⟨e0⟩ := nonempty_iso_unit_of_field _ ((qinv_isInvertible ε₁ ε₂ M).pullback s)
  have e1 : (Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback (pullback.snd c t)).obj (qinv ε₁ ε₂ M)) ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr hφ).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
      (Scheme.Modules.pullback (fibreAt c t s)).mapIso e0 ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso _
  have e2 : (Scheme.Modules.pullback φ).obj (twist ε₁ ε₂ M).L ≅ (Scheme.Modules.pullback φ).obj M.L :=
    Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ whiskerLeftIso _ e1 ≪≫ ρ_ _
  exact (hM k s).of_iso e2.symm

end Twist

section Rep

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  (ε₁ ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
  {D₁ D₂ : RelativePic0Designation R c}
  (h₁ : RepresentsRelSubPic c ε₁ (algEquivZeroCut c ε₁) D₁)
  (h₂ : RepresentsRelSubPic c ε₂ (algEquivZeroCut c ε₂) D₂)

theorem classify_congr {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {P : SubPicCondition c ε}
    {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c ε t) (hM : P.P t M) (hM' : P.P t M') (i : Nonempty (M.L ≅ M'.L)) :
    h.classify t M hM = h.classify t M' hM' :=
  h.classify_unique t M' hM' _ ⟨(h.classify_spec t M hM).some ≪≫ i.some⟩

theorem exists_theta :
    ∃ θ : SchemeHomOver D₁.toBase D₂.toBase,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε₁ t)
        (hM : FibrewiseAlgEquivZero M),
        postComp θ (h₁.classify t M hM) = h₂.classify t (twist ε₁ ε₂ M) (twist_cut ε₁ ε₂ t M hM) := by
  obtain ⟨θ, hθ, -⟩ := AlgebraicGeometry.RelPicard.RepresentsRelSubPic.existsUnique_hom_of_transform h₂ h₁
    (fun t M => twist ε₁ ε₂ M)
    (fun t M M' e => twist_congr ε₁ ε₂ t M M' e)
    (fun ψ M => twist_natural ε₁ ε₂ ψ M)
    (fun t M hM => twist_cut ε₁ ε₂ t M hM)
  exact ⟨θ, fun t M hM => hθ t M hM⟩

end Rep

section Comp

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  (ε₁ ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

theorem twist_twist {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε₁ t) :
    Nonempty ((twist ε₂ ε₁ (twist ε₁ ε₂ M)).L ≅ M.L) := by

  let q₁ := qinv ε₁ ε₂ M
  let q₂ := qinv ε₂ ε₁ (twist ε₁ ε₂ M)
  have hX : (Scheme.Modules.pullback (rigSection c t ε₁)).obj (twist ε₁ ε₂ M).L ≅ q₁ :=
    Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (M.rigidified.some ⊗ᵢ sectionPullbackIso t ε₁ q₁) ≪≫ λ_ q₁
  have h12 : q₁ ⊗ q₂ ≅ 𝟙_ _ := inverseOfIso hX (qinvIso ε₂ ε₁ (twist ε₁ ε₂ M))
  exact ⟨α_ _ _ _ ≪≫
    whiskerLeftIso M.L ((Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso h12 ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _) ≪≫
    ρ_ M.L⟩

end Comp

section Assembly

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

theorem comp_eq_id (ε₁ ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {D₁ D₂ : RelativePic0Designation R c}
    (h₁ : RepresentsRelSubPic c ε₁ (algEquivZeroCut c ε₁) D₁)
    (h₂ : RepresentsRelSubPic c ε₂ (algEquivZeroCut c ε₂) D₂)
    (θ : SchemeHomOver D₁.toBase D₂.toBase)
    (hθ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε₁ t)
        (hM : FibrewiseAlgEquivZero M),
        postComp θ (h₁.classify t M hM) = h₂.classify t (twist ε₁ ε₂ M) (twist_cut ε₁ ε₂ t M hM))
    (θ' : SchemeHomOver D₂.toBase D₁.toBase)
    (hθ' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε₂ t)
        (hM : FibrewiseAlgEquivZero M),
        postComp θ' (h₂.classify t M hM) = h₁.classify t (twist ε₂ ε₁ M) (twist_cut ε₂ ε₁ t M hM)) :
    θ.1 ≫ θ'.1 = 𝟙 D₁.P := by

  have hid : h₁.classify D₁.toBase h₁.poincare h₁.poincare_mem = ⟨𝟙 _, Category.id_comp _⟩ :=
    (h₁.classify_unique D₁.toBase _ _ _ ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_id c D₁.toBase)).app _ ≪≫
      (Scheme.Modules.pullbackId _).app _⟩).symm
  have key : postComp (postComp θ' θ) (h₁.classify D₁.toBase h₁.poincare h₁.poincare_mem)
      = h₁.classify D₁.toBase h₁.poincare h₁.poincare_mem := by
    have step : postComp (postComp θ' θ) (h₁.classify D₁.toBase h₁.poincare h₁.poincare_mem)
        = postComp θ' (postComp θ (h₁.classify D₁.toBase h₁.poincare h₁.poincare_mem)) :=
      Subtype.ext (Category.assoc _ _ _).symm
    rw [step, hθ, hθ']
    exact classify_congr h₁ _ _ _ _ _ (twist_twist ε₁ ε₂ h₁.poincare)
  rw [hid] at key
  have := congrArg Subtype.val key
  simpa only [postComp, Category.id_comp] using this

end Assembly

end Sub2c

end

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (ε ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {D D' : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c ε' (algEquivZeroCut c ε') D') :
    ∃ (θ : SchemeHomOver D.toBase D'.toBase) (θ' : SchemeHomOver D'.toBase D.toBase),
      θ.1 ≫ θ'.1 = 𝟙 D.P ∧ θ'.1 ≫ θ.1 = 𝟙 D'.P ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
        (N : RigidifiedLineBundle c ε' t) (hN : FibrewiseAlgEquivZero N)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (N.L ≅ M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj Q) →
        postComp θ (h.classify t M hM) = h'.classify t N hN := by
  obtain ⟨θ, hθ⟩ := Sub2c.exists_theta ε ε' h h'
  obtain ⟨θ', hθ'⟩ := Sub2c.exists_theta ε' ε h' h
  refine ⟨θ, θ', Sub2c.comp_eq_id ε ε' h h' θ hθ θ' hθ', Sub2c.comp_eq_id ε' ε h' h θ' hθ' θ hθ, ?_⟩
  intro T t M hM N hN Q hQ hNM
  rw [hθ t M hM]
  apply Sub2c.classify_congr

  have hQinv : (Scheme.Modules.pullback (rigSection c t ε')).obj M.L ⊗ Q ≅ 𝟙_ _ :=
    (whiskerLeftIso _ (Sub2c.sectionPullbackIso t ε' Q)).symm ≪≫
      (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso hNM.some.symm ≪≫ N.rigidified.some
  exact ⟨Sub2c.twistIsoOfInverse ε ε' M Q hQinv ≪≫ hNM.some.symm⟩

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_inverse_pair_of_sections
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_inverse_pair_of_sections (solution)
