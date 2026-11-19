-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleFramePresentations
-- name    : AlgebraicGeometry_EtaleFramePresentations
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-18T23:54:17.779832+00:00
-- url     : https://prove2.me/theorems/c2d39f0d-f838-44f3-b9e5-94b967405b95
-- title:
--   Frames of modules on the small étale site
-- statement:
--   Local frames are isomorphisms from the structure sheaf to the pullback of a module. Restriction uses the canonical isomorphism for composite pullback. A presentation identifies these frames with sections of a units torsor wherever a frame exists. Tensoring frames uses the canonical tensor comparison for pullback.
-- source:
--   Stacks Project, Section 59.24, https://stacks.math.columbia.edu/tag/03P8.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_SmallEtaleUnits
import Definitions.Def_AlgebraicGeometry_AbelianSheafTorsors
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2

section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PhilipponFrameUnits
universe u

/-- The trivial line bundle on a scheme. -/
abbrev trivial (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- A compatible family of sections on all opens is determined by its
section on the whole scheme. -/
def globalSections (X : Scheme.{u}) (M : X.Modules) :
    SheafOfModules.sections M ≃ Γ(M, ⊤) where
  toFun s := s.val (op ⊤)
  invFun s := M.val.sectionsMk
    (fun U => M.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op s)
    (by
      intro U V f
      rw [← M.val.map_comp_apply]
      congr 2)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact PresheafOfModules.sections_property s (homOfLE (le_top : U.unop ≤ ⊤)).op
  right_inv s := by
    change M.val.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op s = s
    rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (op ⊤) from Subsingleton.elim _ _]
    change M.val.map (𝟙 _) s = s
    simp

/-- Endomorphisms of the actual tensor unit are multiplication by global
sections of the structure sheaf. -/
def unitEnd (X : Scheme.{u}) : End (trivial X) ≃* Γ(X, ⊤) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let e : End (trivial X) ≃ Γ(X, ⊤) :=
    (SheafOfModules.unitHomEquiv O).trans (globalSections X O)
  refine { toEquiv := e, map_mul' := ?_ }
  intro f g
  let f' : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf := f
  let g' : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf := g
  let F : Γ(X, ⊤) →ₗ[Γ(X, ⊤)] Γ(X, ⊤) := (f'.val.app (op (⊤ : X.Opens))).hom
  let G : Γ(X, ⊤) →ₗ[Γ(X, ⊤)] Γ(X, ⊤) := (g'.val.app (op (⊤ : X.Opens))).hom
  change F (G (1 : Γ(X, ⊤))) = F 1 * G 1
  have h := F.map_smul (G (1 : Γ(X, ⊤))) (1 : Γ(X, ⊤))
  change F (G 1 * 1) = G 1 * F 1 at h
  simpa only [mul_one] using h.trans (mul_comm (G 1) (F 1))

/-- Scalar units are exactly automorphisms of the tensor unit. -/
def unitAut (X : Scheme.{u}) : Aut (trivial X) ≃* (Γ(X, ⊤))ˣ :=
  (Aut.unitsEndEquivAut _).symm.trans (Units.mapEquiv (unitEnd X))

/-- Taking differences from a fixed frame gives a bijection with the
global units on the scheme. -/
def differenceEquiv (X : Scheme.{u}) {M : X.Modules} (q : (trivial X) ≅ M) :
    ((trivial X) ≅ M) ≃ (Γ(X, ⊤))ˣ :=
  (Equiv.mk (fun p => p ≪≫ q.symm) (fun a => a ≪≫ q)
    (by intro p; simp) (by intro a; simp)).trans (unitAut X).toEquiv

/-- The scalars measuring two successive changes of frame multiply to
the scalar for the composite change of frame. -/
theorem difference_mul (X : Scheme.{u}) {M : X.Modules} (p q r : (trivial X) ≅ M) :
    differenceEquiv X q p * differenceEquiv X r q = differenceEquiv X r p := by
  change unitAut X (p ≪≫ q.symm) * unitAut X (q ≪≫ r.symm) = unitAut X (p ≪≫ r.symm)
  rw [mul_comm, ← map_mul]
  congr 1
  apply Aut.ext
  change (p.hom ≫ q.inv) ≫ (q.hom ≫ r.inv) = p.hom ≫ r.inv
  simp

end PhilipponFrameUnits
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite PhilipponFrameUnits

namespace PhilipponFramePullback
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical comparison of the pulled-back tensor unit with the
tensor unit on the domain. -/
abbrev unitIso : (Scheme.Modules.pullback f).obj (trivial Y) ≅ trivial X :=
  Scheme.Modules.pullbackUnitIso f

theorem pullback_scalar_square (a : End (trivial Y)) :
    (Scheme.Modules.pullback f).map a ≫ (unitIso f).hom =
      (unitIso f).hom ≫ (PhilipponFrameUnits.unitEnd X).symm
        (f.appTop (PhilipponFrameUnits.unitEnd Y a)) := by
  let b := (PhilipponFrameUnits.unitEnd X).symm (f.appTop (PhilipponFrameUnits.unitEnd Y a))
  let OX : X.Modules := trivial X
  let OY : Y.Modules := trivial Y
  let N := (Scheme.Modules.pushforward f).obj OX
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let m : OY ⟶ N := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have he : adj.homEquiv OY OX (unitIso f).hom = m :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  change (Scheme.Modules.pullback f).map a ≫ (unitIso f).hom = (unitIso f).hom ≫ b
  apply (adj.homEquiv OY OX).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, he]
  let eval : (OY ⟶ N) ≃ Γ(N, ⊤) := (SheafOfModules.unitHomEquiv N).trans
    (PhilipponFrameUnits.globalSections Y N)
  apply eval.injective
  let b' : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf := b
  change f.appTop (PhilipponFrameUnits.unitEnd Y a) =
    b'.val.app (op (⊤ : X.Opens)) (f.appTop (1 : Γ(Y, ⊤)))
  rw [map_one]
  exact ((PhilipponFrameUnits.unitEnd X).apply_symm_apply _).symm

/-- Pulling back an automorphism of the trivial line bundle restricts the
unit that represents it. -/
theorem unitAut_pullback (a : Aut (trivial Y)) :
    PhilipponFrameUnits.unitAut X ((unitIso f).symm ≪≫
      (Scheme.Modules.pullback f).mapIso a ≪≫ unitIso f) =
      Units.map f.appTop.hom.toMonoidHom (PhilipponFrameUnits.unitAut Y a) := by
  apply Units.ext
  change PhilipponFrameUnits.unitEnd X
    ((unitIso f).inv ≫ (Scheme.Modules.pullback f).map a.hom ≫ (unitIso f).hom) =
    f.appTop (PhilipponFrameUnits.unitEnd Y a.hom)
  have h := pullback_scalar_square f (End.of a.hom)
  rw [h, Iso.inv_hom_id_assoc, MulEquiv.apply_symm_apply]

def pullFrame {M : Y.Modules} (p : trivial Y ≅ M) :
    trivial X ≅ (Scheme.Modules.pullback f).obj M :=
  (unitIso f).symm ≪≫ (Scheme.Modules.pullback f).mapIso p

theorem difference_pullback {M : Y.Modules} (p q : trivial Y ≅ M) :
    PhilipponFrameUnits.differenceEquiv X (pullFrame f q) (pullFrame f p) =
      Units.map f.appTop.hom.toMonoidHom (PhilipponFrameUnits.differenceEquiv Y q p) := by
  change PhilipponFrameUnits.unitAut X (pullFrame f p ≪≫ (pullFrame f q).symm) =
    Units.map f.appTop.hom.toMonoidHom (PhilipponFrameUnits.unitAut Y (p ≪≫ q.symm))
  rw [← unitAut_pullback f (p ≪≫ q.symm)]
  congr 1
  apply Aut.ext
  simp [pullFrame]

theorem difference_postcompose {M N : X.Modules} (p q : trivial X ≅ M) (e : M ≅ N) :
    PhilipponFrameUnits.differenceEquiv X (q ≪≫ e) (p ≪≫ e) =
      PhilipponFrameUnits.differenceEquiv X q p := by
  change PhilipponFrameUnits.unitAut X ((p ≪≫ e) ≪≫ (q ≪≫ e).symm) =
    PhilipponFrameUnits.unitAut X (p ≪≫ q.symm)
  congr 1
  apply Aut.ext
  simp

end PhilipponFramePullback
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponFrameUnits PhilipponFramePullback

namespace PhilipponEtaleFrameSections
universe u
variable {X : Scheme.{u}} (M : X.Modules)

/-- A local frame of a module on a small étale object over the scheme. -/
def Frame (U : X.Etale) := trivial U.left ≅ (Scheme.Modules.pullback U.hom).obj M

/-- Restriction pulls back the frame and uses the comparison between
iterated pullback and pullback along the composite. -/
def restrict {U V : X.Etale} (f : V ⟶ U) (p : Frame M U) : Frame M V :=
  pullFrame f.left p ≪≫
    (Scheme.Modules.pullbackComp f.left U.hom).app M ≪≫
    (Scheme.Modules.pullbackCongr (MorphismProperty.Over.w f)).app M

/-- The change of local frame is a section of the published units sheaf. -/
def diff (U : X.Etale) (p q : Frame M U) :
    (PhilipponKummerSequence.units X).obj.obj (op U) :=
  Additive.ofMul (differenceEquiv U.left q p)

theorem diff_add (U : X.Etale) (p q r : Frame M U) :
    diff M U p q + diff M U q r = diff M U p r :=
  congrArg Additive.ofMul (difference_mul U.left p q r)

theorem diff_restrict {U V : X.Etale} (f : V ⟶ U) (p q : Frame M U) :
    (PhilipponKummerSequence.units X).obj.map f.op (diff M U p q) =
      diff M V (restrict M f p) (restrict M f q) := by
  let e := (Scheme.Modules.pullbackComp f.left U.hom).app M ≪≫
    (Scheme.Modules.pullbackCongr (MorphismProperty.Over.w f)).app M
  change Additive.ofMul (Units.map f.left.appTop.hom.toMonoidHom (differenceEquiv U.left q p)) =
    Additive.ofMul (differenceEquiv V.left (pullFrame f.left q ≪≫ e) (pullFrame f.left p ≪≫ e))
  apply congrArg Additive.ofMul
  rw [difference_postcompose, difference_pullback]

theorem diff_bijective (U : X.Etale) (q : Frame M U) : Function.Bijective (fun p => diff M U p q) :=
  (Additive.ofMul.bijective.comp (differenceEquiv U.left q).bijective)

end PhilipponEtaleFrameSections
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponFramePullback PhilipponFrameUnits

namespace PhilipponFrameUnitCoherence
universe u v w t

private theorem homEquiv_precompose_conjugate
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{t} D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (m : L₂ ⟶ L₁) {A : C} {B : D} (k : L₁.obj A ⟶ B) :
    adj₂.homEquiv A B (m.app A ≫ k) =
      adj₁.homEquiv A B k ≫ (conjugateEquiv adj₁ adj₂ m).app B := by
  rw [adj₂.homEquiv_unit, adj₁.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv adj₁ adj₂ m, Category.assoc,
    ← (conjugateEquiv adj₁ adj₂ m).naturality k, Category.assoc]

variable {X Y Z : Scheme.{u}}

private abbrev adj {A B : Scheme.{u}} (f : A ⟶ B) := Scheme.Modules.pullbackPushforwardAdjunction f

private abbrev toDirectImage {A B : Scheme.{u}} (f : A ⟶ B) :
    trivial B ⟶ (Scheme.Modules.pushforward f).obj (trivial A) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

private theorem adj_unit {A B : Scheme.{u}} (f : A ⟶ B) :
    (adj f).homEquiv (trivial B) (trivial A) (unitIso f).hom = toDirectImage f :=
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

@[simp]
theorem unitIso_id (X : Scheme.{u}) :
    unitIso (𝟙 X) = (Scheme.Modules.pullbackId X).app (trivial X) := by
  apply Iso.ext
  apply ((adj (𝟙 X)).homEquiv (trivial X) (trivial X)).injective
  rw [adj_unit]
  have h := homEquiv_precompose_conjugate (Adjunction.id (C := X.Modules)) (adj (𝟙 X))
    (Scheme.Modules.pullbackId X).hom (A := trivial X) (B := trivial X) (𝟙 (trivial X))
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  change ((adj (𝟙 X)).homEquiv _ _)
    ((Scheme.Modules.pullbackId X).hom.app (trivial X) ≫ 𝟙 (trivial X)) =
    𝟙 (trivial X) ≫ (Scheme.Modules.pushforwardId X).inv.app (trivial X) at h
  calc
    toDirectImage (𝟙 X) = (Scheme.Modules.pushforwardId X).inv.app (trivial X) := by
      apply Scheme.Modules.hom_ext
      intro U
      rfl
    _ = 𝟙 (trivial X) ≫ (Scheme.Modules.pushforwardId X).inv.app (trivial X) :=
      (Category.id_comp _).symm
    _ = _ := h.symm
    _ = _ := congrArg ((adj (𝟙 X)).homEquiv (trivial X) (trivial X)) (Category.comp_id _)

/-- Unit comparisons commute with composition of scheme pullbacks. -/
theorem unitIso_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    unitIso (f ≫ g) = ((Scheme.Modules.pullbackComp f g).app (trivial Z)).symm ≪≫
      (Scheme.Modules.pullback f).mapIso (unitIso g) ≪≫ unitIso f := by
  apply Iso.ext
  apply ((adj (f ≫ g)).homEquiv (trivial Z) (trivial X)).injective
  rw [adj_unit]
  let m := (Scheme.Modules.pullbackComp f g).inv
  let k := (Scheme.Modules.pullback f).map (unitIso g).hom ≫ (unitIso f).hom
  change toDirectImage (f ≫ g) = (adj (f ≫ g)).homEquiv _ _ (m.app _ ≫ k)
  rw [homEquiv_precompose_conjugate ((adj g).comp (adj f)) (adj (f ≫ g)),
    Scheme.Modules.conjugateEquiv_pullbackComp_inv]
  change toDirectImage (f ≫ g) = ((adj g).comp (adj f)).homEquiv _ _
    ((Scheme.Modules.pullback f).map (unitIso g).hom ≫ (unitIso f).hom) ≫
    (Scheme.Modules.pushforwardComp f g).hom.app (trivial X)
  rw [Adjunction.comp_homEquiv]
  change toDirectImage (f ≫ g) = (adj g).homEquiv _ _
    ((adj f).homEquiv _ _ ((Scheme.Modules.pullback f).map (unitIso g).hom ≫ (unitIso f).hom)) ≫ _
  rw [(adj f).homEquiv_naturality_left, adj_unit,
    (adj g).homEquiv_naturality_right, adj_unit]
  apply Scheme.Modules.hom_ext
  intro U
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app]
  rfl

end PhilipponFrameUnitCoherence
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory
open PhilipponFrameUnits PhilipponFramePullback PhilipponFrameUnitCoherence

namespace PhilipponFrameRestrictionCoherence
universe u
variable {S U V W : Scheme.{u}} (M : S.Modules)

def alongComposite (f : V ⟶ U) (i : U ⟶ S)
    (q : trivial U ≅ (Scheme.Modules.pullback i).obj M) :
    trivial V ≅ (Scheme.Modules.pullback (f ≫ i)).obj M :=
  pullFrame f q ≪≫ (Scheme.Modules.pullbackComp f i).app M

private theorem comparison_assoc (g : W ⟶ V) (f : V ⟶ U) (i : U ⟶ S) :
    ((Scheme.Modules.pullbackComp g f).app ((Scheme.Modules.pullback i).obj M)).hom ≫
      ((Scheme.Modules.pullbackComp (g ≫ f) i).app M).hom ≫
      ((Scheme.Modules.pullbackCongr (Category.assoc g f i)).app M).hom =
    (Scheme.Modules.pullback g).map (((Scheme.Modules.pullbackComp f i).app M).hom) ≫
      ((Scheme.Modules.pullbackComp g (f ≫ i)).app M).hom := by
  let a := (Scheme.Modules.pullbackComp g (f ≫ i)).app M
  let b := (Scheme.Modules.pullback g).mapIso ((Scheme.Modules.pullbackComp f i).app M)
  let c := (Scheme.Modules.pullbackComp g f).app ((Scheme.Modules.pullback i).obj M) ≪≫
    (Scheme.Modules.pullbackComp (g ≫ f) i).app M
  let e := (Scheme.Modules.pullbackCongr (Category.assoc g f i)).app M
  have he := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity g f i) M
  change a.inv ≫ b.inv ≫ 𝟙 _ ≫ c.hom = e.inv at he
  rw [Category.id_comp] at he
  have h := congrArg (fun k => k ≫ e.hom) he
  change (a.inv ≫ b.inv ≫ c.hom) ≫ e.hom = e.inv ≫ e.hom at h
  simp only [Category.assoc, Iso.inv_hom_id] at h
  have hc : c.hom ≫ e.hom = b.hom ≫ a.hom := by
    apply (cancel_epi (a.inv ≫ b.inv)).mp
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id] using h
  simpa only [c, e, a, b, Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using hc

theorem alongComposite_assoc (g : W ⟶ V) (f : V ⟶ U) (i : U ⟶ S)
    (q : trivial U ≅ (Scheme.Modules.pullback i).obj M) :
    alongComposite M g (f ≫ i) (alongComposite M f i q) =
      alongComposite M (g ≫ f) i q ≪≫
        (Scheme.Modules.pullbackCongr (Category.assoc g f i)).app M := by
  apply Iso.ext
  have hn := (Scheme.Modules.pullbackComp g f).hom.naturality q.hom
  change (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback f).map q.hom) ≫
      ((Scheme.Modules.pullbackComp g f).app ((Scheme.Modules.pullback i).obj M)).hom =
    ((Scheme.Modules.pullbackComp g f).app (trivial U)).hom ≫
      (Scheme.Modules.pullback (g ≫ f)).map q.hom at hn
  simp only [alongComposite, pullFrame, unitIso_comp g f, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp,
    Category.assoc]
  rw [← reassoc_of% hn, comparison_assoc]

theorem alongComposite_id (i : U ⟶ S)
    (q : trivial U ≅ (Scheme.Modules.pullback i).obj M) :
    alongComposite M (𝟙 U) i q ≪≫
      (Scheme.Modules.pullbackCongr (Category.id_comp i)).app M = q := by
  apply Iso.ext
  let I := (Scheme.Modules.pullbackId U).app ((Scheme.Modules.pullback i).obj M)
  let C := (Scheme.Modules.pullbackComp (𝟙 U) i).app M
  let E := (Scheme.Modules.pullbackCongr (Category.id_comp i)).app M
  have he := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality i) M
  change C.inv ≫ I.hom ≫ 𝟙 _ = E.hom at he
  rw [Category.comp_id] at he
  have hn := (Scheme.Modules.pullbackId U).inv.naturality q.hom
  change q.hom ≫ I.inv = ((Scheme.Modules.pullbackId U).app (trivial U)).inv ≫
    (Scheme.Modules.pullback (𝟙 U)).map q.hom at hn
  change (unitIso (𝟙 U)).inv ≫ (Scheme.Modules.pullback (𝟙 U)).map q.hom ≫ C.hom ≫ E.hom = q.hom
  rw [unitIso_id, ← reassoc_of% hn, ← he]
  simp [I, C]

end PhilipponFrameRestrictionCoherence
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponFrameUnits PhilipponEtaleFrameSections PhilipponFrameRestrictionCoherence
open PhilipponTorsorPresheafDifference PhilipponTorsorInvariantDescent

namespace PhilipponEtaleFramePresheaf
universe u
variable {X : Scheme.{u}} (M : X.Modules)

private theorem pullbackCongr_app_trans {U : Scheme.{u}} {a b c : U ⟶ X}
    (h : a = b) (k : b = c) :
    (Scheme.Modules.pullbackCongr h).app M ≪≫ (Scheme.Modules.pullbackCongr k).app M =
      (Scheme.Modules.pullbackCongr (h.trans k)).app M := by
  subst b
  subst c
  change Iso.refl ((Scheme.Modules.pullback a).obj M) ≪≫ Iso.refl _ = Iso.refl _
  simp

private theorem alongComposite_congr {U V : Scheme.{u}} {a b : U ⟶ X} (f : V ⟶ U)
    (h : a = b) (q : trivial U ≅ (Scheme.Modules.pullback a).obj M) :
    alongComposite M f b (q ≪≫ (Scheme.Modules.pullbackCongr h).app M) =
      alongComposite M f a q ≪≫ (Scheme.Modules.pullbackCongr (congrArg (f ≫ ·) h)).app M := by
  subst b
  change alongComposite M f a (q ≪≫ Iso.refl _) = alongComposite M f a q ≪≫ Iso.refl _
  simp

theorem restrict_id (U : X.Etale) (p : Frame M U) : restrict M (𝟙 U) p = p := by
  change alongComposite M (𝟙 U.left) U.hom p ≪≫
    (Scheme.Modules.pullbackCongr (Category.id_comp U.hom)).app M = p
  exact alongComposite_id M U.hom p

theorem restrict_comp {U V W : X.Etale} (f : V ⟶ U) (g : W ⟶ V) (p : Frame M U) :
    restrict M g (restrict M f p) = restrict M (g ≫ f) p := by
  change alongComposite M g.left V.hom
    (alongComposite M f.left U.hom p ≪≫
      (Scheme.Modules.pullbackCongr (MorphismProperty.Over.w f)).app M) ≪≫
      (Scheme.Modules.pullbackCongr (MorphismProperty.Over.w g)).app M =
    alongComposite M (g.left ≫ f.left) U.hom p ≪≫
      (Scheme.Modules.pullbackCongr (MorphismProperty.Over.w (g ≫ f))).app M
  rw [alongComposite_congr, alongComposite_assoc]
  simp only [Iso.trans_assoc, pullbackCongr_app_trans]

/-- The presheaf of frames of a module on the small étale site. -/
def presheaf : X.Etaleᵒᵖ ⥤ Type u where
  obj U := Frame M U.unop
  map f := ↾(restrict M f.unop)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro p
    exact restrict_id M U.unop p
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro p
    exact (restrict_comp M f.unop g.unop p).symm

def difference : Difference (PhilipponKummerSequence.units X).obj where
  P := presheaf M
  diff U := diff M U.unop
  diff_add_diff U := diff_add M U.unop
  map_diff f := diff_restrict M f.unop

end PhilipponEtaleFramePresheaf
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponTorsorSectionFibers PhilipponEtaleFramePresheaf PhilipponEtaleFrameSections

namespace PhilipponEtaleFrameTorsor
universe u
variable {X : Scheme.{u}}

/-- A sheaf torsor equipped with its comparison from actual frames. -/
structure Presentation (M : X.Modules) where
  torsor : Torsor (PhilipponKummerSequence.units X)
  frames : presheaf M ⟶ torsor.D.P
  diff_eq (U : X.Etaleᵒᵖ) (p q : Frame M U.unop) :
    torsor.D.diff U (frames.app U p) (frames.app U q) = diff M U.unop p q
  bijective (U : X.Etaleᵒᵖ) : Nonempty (Frame M U.unop) → Function.Bijective (frames.app U)

end PhilipponEtaleFrameTorsor
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open PhilipponFrameUnits

namespace PhilipponTensorFrames
universe u v

def tensorFrame (X : Scheme.{u}) {M N : X.Modules} (p : trivial X ≅ M) (q : trivial X ≅ N) :
    trivial X ≅ M ⊗ N :=
  (λ_ (𝟙_ X.Modules)).symm ≪≫ (p ⊗ᵢ q)


/-- Tensor two frames and transport along the given module isomorphism. -/
def tensorOn {X : Scheme.{u}} {M N L : X.Modules} (e : M ⊗ N ≅ L)
    (U : X.Etale) (p : PhilipponEtaleFrameSections.Frame M U)
    (q : PhilipponEtaleFrameSections.Frame N U) : PhilipponEtaleFrameSections.Frame L U :=
  tensorFrame U.left p q ≪≫ (Functor.Monoidal.μIso (Scheme.Modules.pullback U.hom) M N) ≪≫
    (Scheme.Modules.pullback U.hom).mapIso e

end PhilipponTensorFrames
end
end


