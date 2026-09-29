-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.baseChangeSnd_comp_restrictHom_eq_of_baseChangeSnd_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/5538776b-ad45-50bb-8472-ea51f6e010af

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_baseChangeSnd_comp_restrictHom_eq_of_baseChangeSnd_comp
set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian CategoryTheory.MonoidalCategory"

noncomputable section

namespace TwistNatAux

variable {R : Type u} [CommRing R] {κ : Type u} [CommRing κ] [Algebra R κ]

local notation "𝔰" => specMap R κ

section Basic

@[reassoc] theorem rigSection_fst'' {C T : Scheme.{u}} (cc : C ⟶ Spec (CommRingCat.of κ)) (t : T ⟶ Spec (CommRingCat.of κ))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) cc) : rigSection cc t e ≫ pullback.fst cc t = t ≫ e.1 :=
  pullback.lift_fst _ _ _

@[reassoc] theorem rigSection_snd'' {C T : Scheme.{u}} (cc : C ⟶ Spec (CommRingCat.of κ)) (t : T ⟶ Spec (CommRingCat.of κ))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) cc) : rigSection cc t e ≫ pullback.snd cc t = 𝟙 T :=
  pullback.lift_snd _ _ _

@[reassoc] theorem baseChangeSnd_fst'' {S : Type u} [CommRing S] {C T T' : Scheme.{u}} (cc : C ⟶ Spec (CommRingCat.of S))
    {t : T ⟶ Spec (CommRingCat.of S)} {t' : T' ⟶ Spec (CommRingCat.of S)}
    (ψ : SchemeHomOver t' t) : baseChangeSnd cc ψ ≫ pullback.fst cc t = pullback.fst cc t' :=
  BaseChange.baseChangeSnd_fst' _ cc ψ

@[reassoc] theorem baseChangeSnd_snd'' {S : Type u} [CommRing S] {C T T' : Scheme.{u}} (cc : C ⟶ Spec (CommRingCat.of S))
    {t : T ⟶ Spec (CommRingCat.of S)} {t' : T' ⟶ Spec (CommRingCat.of S)}
    (ψ : SchemeHomOver t' t) : baseChangeSnd cc ψ ≫ pullback.snd cc t = pullback.snd cc t' ≫ ψ.1 :=
  BaseChange.baseChangeSnd_snd' _ cc ψ

@[reassoc] theorem sectionBaseChange_fst'' {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    (sectionBaseChange κ e).1 ≫ pullback.fst c 𝔰 = 𝔰 ≫ e.1 :=
  sectionBaseChange_coe_fst κ e

@[reassoc] theorem sectionBaseChange_snd'' {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    (sectionBaseChange κ e).1 ≫ pullback.snd c 𝔰 = 𝟙 _ :=
  sectionBaseChange_coe_snd κ e

@[reassoc] theorem curveChange_fst'' {S : Type u} [CommRing S] {C C' T : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of S)}
    {c' : C' ⟶ Spec (CommRingCat.of S)} (f : C' ⟶ C) (hf : f ≫ c = c')
    (t : T ⟶ Spec (CommRingCat.of S)) : curveChange f hf t ≫ pullback.fst c t = pullback.fst c' t ≫ f := by
  unfold curveChange; rw [pullback.lift_fst]

@[reassoc] theorem curveChange_snd'' {S : Type u} [CommRing S] {C C' T : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of S)}
    {c' : C' ⟶ Spec (CommRingCat.of S)} (f : C' ⟶ C) (hf : f ≫ c = c')
    (t : T ⟶ Spec (CommRingCat.of S)) : curveChange f hf t ≫ pullback.snd c t = pullback.snd c' t :=
  curveChange_snd f hf t

end Basic

section Points

variable {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R)) (τ : SchemeHomOver (specMap R κ) (specMap R κ))

def flatPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (b : T ⟶ pullback y 𝔰)
    (hb : b ≫ pullback.snd y 𝔰 = t ≫ τ.1) : SchemeHomOver t (pullback.snd y 𝔰) :=
  ⟨pullback.lift (b ≫ pullback.fst y 𝔰) t (by
      rw [Category.assoc, pullback.condition, reassoc_of% hb, τ.2]),
    pullback.lift_snd _ _ _⟩

@[reassoc] theorem flatPt_coe_fst {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (b : T ⟶ pullback y 𝔰)
    (hb : b ≫ pullback.snd y 𝔰 = t ≫ τ.1) : (flatPt y τ t b hb).1 ≫ pullback.fst y 𝔰 = b ≫ pullback.fst y 𝔰 :=
  pullback.lift_fst _ _ _

@[reassoc] theorem flatPt_coe_snd {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (b : T ⟶ pullback y 𝔰)
    (hb : b ≫ pullback.snd y 𝔰 = t ≫ τ.1) : (flatPt y τ t b hb).1 ≫ pullback.snd y 𝔰 = t :=
  pullback.lift_snd _ _ _

theorem flatPt_comp_baseChangeSnd {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (b : T ⟶ pullback y 𝔰)
    (hb : b ≫ pullback.snd y 𝔰 = t ≫ τ.1) : (flatPt y τ t b hb).1 ≫ baseChangeSnd y τ = b := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangeSnd_fst'', flatPt_coe_fst]
  · simp only [Category.assoc, baseChangeSnd_snd'', flatPt_coe_snd_assoc, hb]

def twistPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of κ)} (a : SchemeHomOver t (pullback.snd y 𝔰)) :
    SchemeHomOver (t ≫ τ.1) (pullback.snd y 𝔰) :=
  ⟨a.1 ≫ baseChangeSnd y τ, by rw [Category.assoc, baseChangeSnd_snd'', reassoc_of% a.2]⟩

@[scoped simp] theorem twistPt_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of κ)} (a : SchemeHomOver t (pullback.snd y 𝔰)) :
    (twistPt y τ a).1 = a.1 ≫ baseChangeSnd y τ := rfl

@[reassoc] theorem twistPt_coe_fst {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of κ)}
    (a : SchemeHomOver t (pullback.snd y 𝔰)) :
    (twistPt y τ a).1 ≫ pullback.fst y 𝔰 = a.1 ≫ pullback.fst y 𝔰 := by
  rw [twistPt_coe, Category.assoc, baseChangeSnd_fst'']

end Points

section Pi

variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (τ : SchemeHomOver (specMap R κ) (specMap R κ))
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ))

def piHom : pullback (baseChange R c κ) (t ≫ τ.1) ⟶ pullback (baseChange R c κ) t :=
  pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst c 𝔰) (pullback.snd _ _ ≫ t) (by
      simp only [Category.assoc, pullback.condition, pullback.condition_assoc, reassoc_of% τ.2, τ.2]))
    (pullback.snd _ _) (by rw [pullback.lift_snd])

def piInv : pullback (baseChange R c κ) t ⟶ pullback (baseChange R c κ) (t ≫ τ.1) :=
  pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst c 𝔰) (pullback.snd _ _ ≫ t ≫ τ.1) (by
      simp only [Category.assoc, pullback.condition, pullback.condition_assoc, reassoc_of% τ.2, τ.2]))
    (pullback.snd _ _) (by rw [pullback.lift_snd])

@[reassoc (attr := simp)] theorem piHom_snd : piHom c τ t ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
@[reassoc (attr := simp)] theorem piInv_snd : piInv c τ t ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
@[reassoc (attr := simp)] theorem piHom_fst_fst :
    piHom c τ t ≫ pullback.fst _ _ ≫ pullback.fst c 𝔰 = pullback.fst _ _ ≫ pullback.fst c 𝔰 := by
  rw [piHom, pullback.lift_fst_assoc, pullback.lift_fst]
@[reassoc (attr := simp)] theorem piInv_fst_fst :
    piInv c τ t ≫ pullback.fst _ _ ≫ pullback.fst c 𝔰 = pullback.fst _ _ ≫ pullback.fst c 𝔰 := by
  rw [piInv, pullback.lift_fst_assoc, pullback.lift_fst]
@[reassoc (attr := simp)] theorem piHom_fst_snd :
    piHom c τ t ≫ pullback.fst _ _ ≫ pullback.snd c 𝔰 = pullback.snd _ _ ≫ t := by
  rw [piHom, pullback.lift_fst_assoc, pullback.lift_snd]
@[reassoc (attr := simp)] theorem piInv_fst_snd :
    piInv c τ t ≫ pullback.fst _ _ ≫ pullback.snd c 𝔰 = pullback.snd _ _ ≫ t ≫ τ.1 := by
  rw [piInv, pullback.lift_fst_assoc, pullback.lift_snd]

def piIso : pullback (baseChange R c κ) (t ≫ τ.1) ≅ pullback (baseChange R c κ) t where
  hom := piHom c τ t
  inv := piInv c τ t
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, Category.id_comp, piInv_fst_fst, piHom_fst_fst]
      · simp only [Category.assoc, Category.id_comp, piInv_fst_snd, piHom_snd_assoc]
        exact pullback.condition.symm
    · simp only [Category.assoc, piInv_snd, piHom_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, Category.id_comp, piHom_fst_fst, piInv_fst_fst]
      · simp only [Category.assoc, Category.id_comp, piHom_fst_snd, piInv_snd_assoc]
        exact pullback.condition.symm
    · simp only [Category.assoc, piHom_snd, piInv_snd, Category.id_comp]

@[scoped simp] theorem piIso_hom : (piIso c τ t).hom = piHom c τ t := rfl
@[scoped simp] theorem piIso_inv : (piIso c τ t).inv = piInv c τ t := rfl

theorem rigSection_piHom (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    rigSection (baseChange R c κ) (t ≫ τ.1) (sectionBaseChange κ e) ≫ piHom c τ t =
      rigSection (baseChange R c κ) t (sectionBaseChange κ e) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc, piHom_fst_fst, rigSection_fst''_assoc, sectionBaseChange_fst'', reassoc_of% τ.2]
    · simp only [Category.assoc, piHom_fst_snd, rigSection_snd''_assoc, rigSection_fst''_assoc,
        sectionBaseChange_snd'', Category.comp_id]
  · simp only [Category.assoc, piHom_snd, rigSection_snd'']

end Pi

section Transport

def objIso {P Q S : Scheme.{u}} (A : P ⟶ Q) (B : Q ⟶ S) (C : P ⟶ S) (h : A ≫ B = C) (L : S.Modules) :
    (Scheme.Modules.pullback A).obj ((Scheme.Modules.pullback B).obj L) ≅ (Scheme.Modules.pullback C).obj L :=
  (Scheme.Modules.pullbackComp A B).app L ≪≫ (Scheme.Modules.pullbackCongr h).app L

def invHomIso {P Q : Scheme.{u}} (e : P ≅ Q) (N : Q.Modules) :
    (Scheme.Modules.pullback e.inv).obj ((Scheme.Modules.pullback e.hom).obj N) ≅ N :=
  objIso e.inv e.hom (𝟙 Q) e.inv_hom_id N ≪≫ (Scheme.Modules.pullbackId Q).app N

def squareIso {P Q P' Q' : Scheme.{u}} (A : P ⟶ Q) (B : Q ⟶ Q') (A' : P ⟶ P') (B' : P' ⟶ Q') (h : A ≫ B = A' ≫ B')
    (L : Q'.Modules) :
    (Scheme.Modules.pullback A).obj ((Scheme.Modules.pullback B).obj L) ≅
      (Scheme.Modules.pullback A').obj ((Scheme.Modules.pullback B').obj L) :=
  objIso A B _ h L ≪≫ (objIso A' B' _ rfl L).symm

def rigidifyTransport {P₁ P₂ T : Scheme.{u}} (e : P₁ ≅ P₂) (σ₁ : T ⟶ P₁) (σ₂ : T ⟶ P₂) (hσ : σ₁ ≫ e.hom = σ₂)
    (q₁ : P₁ ⟶ T) (q₂ : P₂ ⟶ T) (hq : e.hom ≫ q₂ = q₁) (N : P₂.Modules) :
    (Scheme.Modules.pullback e.inv).obj (Scheme.Modules.rigidify σ₁ q₁ ((Scheme.Modules.pullback e.hom).obj N)) ≅
      Scheme.Modules.rigidify σ₂ q₂ N :=
  Scheme.Modules.pullbackTensorObjIso e.inv _ _ ≪≫
    (invHomIso e N ⊗ᵢ
      (objIso e.inv q₁ q₂ (by rw [← hq, Iso.inv_hom_id_assoc]) _ ≪≫
        (Scheme.Modules.pullback q₂).mapIso (Scheme.Modules.dualMapIso (objIso σ₁ e.hom σ₂ hσ N))))

end Transport

section Poincare

variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)} {e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {G : RelativePic0Designation R c} (hGR : RepresentsRelSubPic c e (algEquivZeroCut c e) G)
  (hG : RepresentsRelSubPic (baseChange R c κ) (sectionBaseChange κ e)
    (algEquivZeroCut (baseChange R c κ) (sectionBaseChange κ e)) (G.baseChange κ))
  (hPG : Nonempty (hG.poincare.L ≅ (BaseChange.ofR c e κ
    (hGR.poincare.pullbackAlong ⟨pullback.fst G.toBase (specMap R κ), pullback.condition⟩)).L))
  (τ : SchemeHomOver (specMap R κ) (specMap R κ))

def qMap {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of κ)} (p : SchemeHomOver t (G.baseChange κ).toBase) :
    pullback (baseChange R c κ) t ⟶ pullback c G.toBase :=
  baseChangeSnd (baseChange R c κ) p ≫ (BaseChange.κ c κ (G.baseChange κ).toBase).hom ≫
    baseChangeSnd c (⟨pullback.fst G.toBase (specMap R κ), pullback.condition⟩ :
      SchemeHomOver ((G.baseChange κ).toBase ≫ specMap R κ) G.toBase)

theorem qMap_fst {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of κ)} (p : SchemeHomOver t (G.baseChange κ).toBase) :
    qMap p ≫ pullback.fst c G.toBase = pullback.fst _ _ ≫ pullback.fst c 𝔰 := by
  simp only [qMap, Category.assoc, baseChangeSnd_fst'', BaseChange.κ_hom_fst, baseChangeSnd_fst''_assoc]

theorem qMap_snd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of κ)} (p : SchemeHomOver t (G.baseChange κ).toBase) :
    qMap p ≫ pullback.snd c G.toBase = pullback.snd _ _ ≫ p.1 ≫ pullback.fst G.toBase 𝔰 := by
  simp only [qMap, Category.assoc, baseChangeSnd_snd'', reassoc_of% (BaseChange.κ_hom_snd c κ (G.baseChange κ).toBase),
    baseChangeSnd_snd''_assoc]

include hPG in

theorem nonempty_poincare_pullbackAlong_iso {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of κ)}
    (p : SchemeHomOver t (G.baseChange κ).toBase) :
    Nonempty ((hG.poincare.pullbackAlong p).L ≅ (Scheme.Modules.pullback (qMap p)).obj hGR.poincare.L) := by
  obtain ⟨eP⟩ := hPG
  exact ⟨(Scheme.Modules.pullback _).mapIso eP ≪≫ objIso _ _ _ rfl _ ≪≫ objIso _ _ _ rfl _⟩

include hPG in

theorem nonempty_poincare_pullbackAlong_iso_of_fst_eq {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of κ)}
    (p : SchemeHomOver (t ≫ τ.1) (G.baseChange κ).toBase) (q : SchemeHomOver t (G.baseChange κ).toBase)
    (hpq : p.1 ≫ pullback.fst G.toBase 𝔰 = q.1 ≫ pullback.fst G.toBase 𝔰) :
    Nonempty ((hG.poincare.pullbackAlong p).L ≅
      (Scheme.Modules.pullback (piHom c τ t)).obj (hG.poincare.pullbackAlong q).L) := by
  have hQ : piHom c τ t ≫ qMap q = qMap p := by
    apply pullback.hom_ext
    · rw [Category.assoc, qMap_fst, qMap_fst, piHom_fst_fst]
    · rw [Category.assoc, qMap_snd, qMap_snd, piHom_snd_assoc, hpq]
  obtain ⟨e₁⟩ := nonempty_poincare_pullbackAlong_iso hGR hG hPG p
  obtain ⟨e₂⟩ := nonempty_poincare_pullbackAlong_iso hGR hG hPG q
  exact ⟨e₁ ≪≫ (objIso _ _ _ hQ _).symm ≪≫ (Scheme.Modules.pullback _).mapIso e₂.symm⟩

end Poincare

section Curves

variable {𝔛 𝔛₀ : Scheme.{u}} {x : 𝔛 ⟶ Spec (CommRingCat.of R)} {x₀ : 𝔛₀ ⟶ Spec (CommRingCat.of R)}
  (f : pullback x₀ (specMap R κ) ⟶ pullback x (specMap R κ)) (hf : f ≫ baseChange R x κ = baseChange R x₀ κ)
  (τ : SchemeHomOver (specMap R κ) (specMap R κ))
  (hcomm : baseChangeSnd x₀ τ ≫ f = f ≫ baseChangeSnd x τ)

theorem piHom_fst_baseChangeSnd {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of κ)) :
    piHom c τ t ≫ pullback.fst _ _ ≫ baseChangeSnd c τ = pullback.fst _ _ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangeSnd_fst'', piHom_fst_fst]
  · simp only [Category.assoc, baseChangeSnd_snd'', piHom_fst_snd_assoc]
    exact pullback.condition.symm

include hcomm in

theorem baseChangeSnd_f_fst : baseChangeSnd x₀ τ ≫ f ≫ pullback.fst x 𝔰 = f ≫ pullback.fst x 𝔰 := by
  rw [reassoc_of% hcomm, baseChangeSnd_fst'']

include hcomm in

theorem curveChange_piHom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) :
    curveChange f hf (t ≫ τ.1) ≫ piHom x τ t = piHom x₀ τ t ≫ curveChange f hf t := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, piHom_fst_fst, curveChange_fst''_assoc,
        curveChange_fst''_assoc, ← piHom_fst_baseChangeSnd τ x₀ t, Category.assoc, Category.assoc,
        baseChangeSnd_f_fst f τ hcomm]
    · have h₁ : pullback.fst (baseChange R x κ) t ≫ pullback.snd x 𝔰 = pullback.snd _ _ ≫ t := pullback.condition
      rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, piHom_fst_snd, curveChange_snd''_assoc,
        h₁, curveChange_snd''_assoc, piHom_snd_assoc]
  · rw [Category.assoc, Category.assoc, piHom_snd, curveChange_snd'', curveChange_snd'', piHom_snd]

include hcomm in

theorem nonempty_curveChange_piHom_iso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ))
    (M : (pullback (baseChange R x κ) t).Modules) :
    Nonempty ((Scheme.Modules.pullback (curveChange f hf (t ≫ τ.1))).obj ((Scheme.Modules.pullback (piHom x τ t)).obj M) ≅
      (Scheme.Modules.pullback (piHom x₀ τ t)).obj ((Scheme.Modules.pullback (curveChange f hf t)).obj M)) :=
  ⟨squareIso _ _ _ _ (curveChange_piHom f hf τ hcomm t) M⟩

end Curves

section Core

variable {𝔛 𝔛₀ : Scheme.{u}} {x : 𝔛 ⟶ Spec (CommRingCat.of R)} {x₀ : 𝔛₀ ⟶ Spec (CommRingCat.of R)}
  {εR : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) x} {ε₀R : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) x₀}
  {D_R : RelativePic0Designation R x} {D₀ : RelativePic0Designation R x₀}
  (hD_R : RepresentsRelSubPic x εR (algEquivZeroCut x εR) D_R)
  (hD₀ : RepresentsRelSubPic x₀ ε₀R (algEquivZeroCut x₀ ε₀R) D₀)
  (hD : RepresentsRelSubPic (baseChange R x κ) (sectionBaseChange κ εR)
    (algEquivZeroCut (baseChange R x κ) (sectionBaseChange κ εR)) (D_R.baseChange κ))
  (hPD : Nonempty (hD.poincare.L ≅ (BaseChange.ofR x εR κ
    (hD_R.poincare.pullbackAlong ⟨pullback.fst D_R.toBase (specMap R κ), pullback.condition⟩)).L))
  (hD' : RepresentsRelSubPic (baseChange R x₀ κ) (sectionBaseChange κ ε₀R)
    (algEquivZeroCut (baseChange R x₀ κ) (sectionBaseChange κ ε₀R)) (D₀.baseChange κ))
  (hPD' : Nonempty (hD'.poincare.L ≅ (BaseChange.ofR x₀ ε₀R κ
    (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap R κ), pullback.condition⟩)).L))
  (f : pullback x₀ (specMap R κ) ⟶ pullback x (specMap R κ)) (hf : f ≫ baseChange R x κ = baseChange R x₀ κ)
  (τ : SchemeHomOver (specMap R κ) (specMap R κ))
  (hcomm : baseChangeSnd x₀ τ ≫ f = f ≫ baseChangeSnd x τ)
  (ν : SchemeHomOver (D_R.baseChange κ).toBase (D₀.baseChange κ).toBase)
  (hν : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t (D_R.baseChange κ).toBase),
    Nonempty ((hD'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν)).L ≅
      Scheme.Modules.rigidify (rigSection (baseChange R x₀ κ) t (sectionBaseChange κ ε₀R))
        (pullback.snd (baseChange R x₀ κ) t)
        ((Scheme.Modules.pullback (curveChange f hf t)).obj (hD.poincare.pullbackAlong a).L)))

theorem twist_comp_snd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of κ)} (a : SchemeHomOver t (D_R.baseChange κ).toBase) :
    ((twistPt D_R.toBase τ a).1 ≫ ν.1) ≫ pullback.snd D₀.toBase 𝔰 = t ≫ τ.1 := by
  rw [Category.assoc]
  exact (congrArg (fun k => (twistPt D_R.toBase τ a).1 ≫ k) ν.2).trans (twistPt D_R.toBase τ a).2

include hD_R hD₀ hPD hPD' hcomm hν in

theorem flatPt_twist_eq {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of κ)} (a : SchemeHomOver t (D_R.baseChange κ).toBase) :
    flatPt D₀.toBase τ t ((twistPt D_R.toBase τ a).1 ≫ ν.1) (twist_comp_snd τ ν a) =
      NeronModelInfra.schemeHomOverComp a ν := by
  apply hD'.ext_of_iso t

  let b : SchemeHomOver (t ≫ τ.1) (D₀.baseChange κ).toBase :=
    NeronModelInfra.schemeHomOverComp (twistPt D_R.toBase τ a) ν

  obtain ⟨e₁⟩ := nonempty_poincare_pullbackAlong_iso_of_fst_eq hD₀ hD' hPD' τ b
    (flatPt D₀.toBase τ t ((twistPt D_R.toBase τ a).1 ≫ ν.1) (twist_comp_snd τ ν a))
    (by rw [flatPt_coe_fst]; rfl)

  obtain ⟨e₂⟩ := hν (t ≫ τ.1) (twistPt D_R.toBase τ a)

  obtain ⟨e₃⟩ := nonempty_poincare_pullbackAlong_iso_of_fst_eq hD_R hD hPD τ (twistPt D_R.toBase τ a) a
    (twistPt_coe_fst D_R.toBase τ a)

  obtain ⟨e₄⟩ := nonempty_curveChange_piHom_iso f hf τ hcomm t (hD.poincare.pullbackAlong a).L

  obtain ⟨e₅⟩ := hν t a
  refine ⟨(invHomIso (piIso x₀ τ t) _).symm ≪≫ (Scheme.Modules.pullback (piInv x₀ τ t)).mapIso e₁.symm ≪≫
    (Scheme.Modules.pullback (piInv x₀ τ t)).mapIso e₂ ≪≫
    (Scheme.Modules.pullback (piInv x₀ τ t)).mapIso
      (Scheme.Modules.rigidifyMapIso _ _ ((Scheme.Modules.pullback _).mapIso e₃ ≪≫ e₄)) ≪≫
    rigidifyTransport (piIso x₀ τ t) _ _ (rigSection_piHom x₀ τ t ε₀R) _ _ (piHom_snd x₀ τ t) _ ≪≫ e₅.symm⟩

include hD_R hD₀ hPD hPD' hcomm hν in

theorem comm_of_characterisation :
    baseChangeSnd D_R.toBase τ ≫ ν.1 = ν.1 ≫ baseChangeSnd D₀.toBase τ := by
  have key := flatPt_twist_eq hD_R hD₀ hD hPD hD' hPD' f hf τ hcomm ν hν
    (⟨𝟙 _, Category.id_comp _⟩ : SchemeHomOver (D_R.baseChange κ).toBase (D_R.baseChange κ).toBase)
  have e := flatPt_comp_baseChangeSnd D₀.toBase τ _ _ (twist_comp_snd τ ν
    (⟨𝟙 _, Category.id_comp _⟩ : SchemeHomOver (D_R.baseChange κ).toBase (D_R.baseChange κ).toBase))
  rw [key] at e
  change (𝟙 _ ≫ ν.1) ≫ baseChangeSnd D₀.toBase τ = (𝟙 _ ≫ baseChangeSnd D_R.toBase τ) ≫ ν.1 at e
  simpa only [Category.id_comp, Category.assoc] using e.symm

end Core

section Clause1

variable {𝔛 𝔛₀ : Scheme.{u}} {x : 𝔛 ⟶ Spec (CommRingCat.of R)} {x₀ : 𝔛₀ ⟶ Spec (CommRingCat.of R)}
  {εR : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) x} {ε₀R : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) x₀}
  {D_R : RelativePic0Designation R x} {D₀ : RelativePic0Designation R x₀}
  (hD : RepresentsRelSubPic (baseChange R x κ) (sectionBaseChange κ εR)
    (algEquivZeroCut (baseChange R x κ) (sectionBaseChange κ εR)) (D_R.baseChange κ))
  (hD' : RepresentsRelSubPic (baseChange R x₀ κ) (sectionBaseChange κ ε₀R)
    (algEquivZeroCut (baseChange R x₀ κ) (sectionBaseChange κ ε₀R)) (D₀.baseChange κ))
  (f : pullback x₀ (specMap R κ) ⟶ pullback x (specMap R κ)) (hf : f ≫ baseChange R x κ = baseChange R x₀ κ)
  (hε : (sectionBaseChange κ ε₀R).1 ≫ f = (sectionBaseChange κ εR).1)

theorem characterisation_pullbackHom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ))
    (a : SchemeHomOver t (D_R.baseChange κ).toBase) :
    Nonempty ((hD'.poincare.pullbackAlong
        (NeronModelInfra.schemeHomOverComp a (RepresentsRelSubPic.pullbackHom f hf hε hD hD'))).L ≅
      Scheme.Modules.rigidify (rigSection (baseChange R x₀ κ) t (sectionBaseChange κ ε₀R))
        (pullback.snd (baseChange R x₀ κ) t)
        ((Scheme.Modules.pullback (curveChange f hf t)).obj (hD.poincare.pullbackAlong a).L)) := by
  have hmem : (algEquivZeroCut (baseChange R x κ) (sectionBaseChange κ εR)).P t (hD.poincare.pullbackAlong a) :=
    (algEquivZeroCut _ _).pullback_mem _ _ a _ hD.poincare_mem
  have ha : a = hD.classify t (hD.poincare.pullbackAlong a) hmem := hD.classify_unique t _ hmem a ⟨Iso.refl _⟩
  have hc : NeronModelInfra.schemeHomOverComp a (RepresentsRelSubPic.pullbackHom f hf hε hD hD') =
      postComp (RepresentsRelSubPic.pullbackHom f hf hε hD hD') a := rfl
  have h₂ := RepresentsRelSubPic.postComp_pullbackHom_classify f hf hε hD hD' t (hD.poincare.pullbackAlong a) hmem
  rw [← ha] at h₂
  obtain ⟨e₁⟩ := hD'.classify_spec t ((hD.poincare.pullbackAlong a).pullbackCurve f hf hε)
    (FibrewiseAlgEquivZero.pullbackCurve f hf hε hmem)
  obtain ⟨e₂⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified
    ((hD.poincare.pullbackAlong a).pullbackCurve f hf hε)
  rw [hc, h₂]
  exact ⟨e₁ ≪≫ e₂.symm⟩

end Clause1

end TwistNatAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_baseChangeSnd_comp_restrictHom_eq_of_baseChangeSnd_comp.TwistNatAux"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_baseChangeSnd_comp_restrictHom_eq_of_baseChangeSnd_comp.TwistNatAux"

open TwistNatAux in
theorem solution
    {R : Type u} [CommRing R] (κ : Type u) [CommRing κ] [Algebra R κ]
    {𝔛 𝔛₀ : Scheme.{u}} {x : 𝔛 ⟶ Spec (CommRingCat.of R)} {x₀ : 𝔛₀ ⟶ Spec (CommRingCat.of R)}
    {εR : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) x} {ε₀R : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) x₀}
    {D_R : RelativePic0Designation R x} {D₀ : RelativePic0Designation R x₀}
    (hD_R : RepresentsRelSubPic x εR (algEquivZeroCut x εR) D_R)
    (hD₀ : RepresentsRelSubPic x₀ ε₀R (algEquivZeroCut x₀ ε₀R) D₀)
    (hD : RepresentsRelSubPic (baseChange R x κ) (sectionBaseChange κ εR)
      (algEquivZeroCut (baseChange R x κ) (sectionBaseChange κ εR)) (D_R.baseChange κ))
    (hPD : Nonempty (hD.poincare.L ≅ (BaseChange.ofR x εR κ
      (hD_R.poincare.pullbackAlong ⟨pullback.fst D_R.toBase (specMap R κ), pullback.condition⟩)).L))
    (hD' : RepresentsRelSubPic (baseChange R x₀ κ) (sectionBaseChange κ ε₀R)
      (algEquivZeroCut (baseChange R x₀ κ) (sectionBaseChange κ ε₀R)) (D₀.baseChange κ))
    (hPD' : Nonempty (hD'.poincare.L ≅ (BaseChange.ofR x₀ ε₀R κ
      (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap R κ), pullback.condition⟩)).L))
    (f : pullback x₀ (specMap R κ) ⟶ pullback x (specMap R κ)) (hf : f ≫ baseChange R x κ = baseChange R x₀ κ)
    (τ : SchemeHomOver (specMap R κ) (specMap R κ))
    (hcomm : baseChangeSnd x₀ τ ≫ f = f ≫ baseChangeSnd x τ) :
    (∀ hε : (sectionBaseChange κ ε₀R).1 ≫ f = (sectionBaseChange κ εR).1,
      baseChangeSnd D_R.toBase τ ≫ (RepresentsRelSubPic.pullbackHom f hf hε hD hD').1 =
        (RepresentsRelSubPic.pullbackHom f hf hε hD hD').1 ≫ baseChangeSnd D₀.toBase τ) ∧
    (∀ ν : SchemeHomOver (D_R.baseChange κ).toBase (D₀.baseChange κ).toBase,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t (D_R.baseChange κ).toBase),
        Nonempty ((hD'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν)).L ≅
          Scheme.Modules.rigidify (rigSection (baseChange R x₀ κ) t (sectionBaseChange κ ε₀R))
            (pullback.snd (baseChange R x₀ κ) t)
            ((Scheme.Modules.pullback (curveChange f hf t)).obj (hD.poincare.pullbackAlong a).L))) →
      baseChangeSnd D_R.toBase τ ≫ ν.1 = ν.1 ≫ baseChangeSnd D₀.toBase τ) := by
  refine ⟨fun hε => ?_, fun ν hν => ?_⟩
  · exact comm_of_characterisation hD_R hD₀ hD hPD hD' hPD' f hf τ hcomm _
      (fun t a => characterisation_pullbackHom (κ := κ) hD hD' f hf hε t a)
  · exact comm_of_characterisation hD_R hD₀ hD hPD hD' hPD' f hf τ hcomm ν (fun t a => hν t a)

end S_AlgebraicGeometry_RelPicard_baseChangeSnd_comp_restrictHom_eq_of_baseChangeSnd_comp
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_baseChangeSnd_comp_restrictHom_eq_of_baseChangeSnd_comp (solution)
