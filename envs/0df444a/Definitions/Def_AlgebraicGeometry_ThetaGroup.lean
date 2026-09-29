-- Prove2me | Definitions.Def_AlgebraicGeometry_ThetaGroup
-- name    : AlgebraicGeometry_ThetaGroup
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/81043e83-54e6-589b-9524-19d8c459db1a
-- title:
--   Theta group of a module under a relative group law
-- statement:
--   The first part supplements Mathlib's co-Grothendieck construction $\int^{\mathrm c} F$ for a pseudofunctor $F$ on $\mathrm{LocallyDiscrete}\,\mathcal S^{\mathrm{op}}$ with values in $\mathbf{Cat}$: `homMk b φ` assembles a morphism $X \to Y$ from a base map $b : X_{\mathrm{base}} \to Y_{\mathrm{base}}$ and a fibre map $φ : X_{\mathrm{fiber}} \to (F b)(Y_{\mathrm{fiber}})$, `mono_homMk` shows it is a monomorphism when $b$ is one and $φ$ is invertible, `sectionMk` exhibits an explicit section when both are isomorphisms, and `isoMk` packages the resulting isomorphism $X \cong Y$, with the expected descriptions of base and fibre components. `Scheme.Modules.fibration` is Mathlib's pullback pseudofunctor $X \mapsto X.\mathrm{Modules}$, $g \mapsto g^{*}$, with right adjoints forgotten.
--
--   The geometric part fixes a field $k$, a scheme $A$ with a morphism $f : A \to \operatorname{Spec} k$, a relative group law $L$ on $f$ and (from `thetaGroup` onwards) a commutativity hypothesis $hc$. For a $k$-point $x$ of $A$ (a section of $f$) the translation $T_x = L(\mathrm{id}, x) : A \to A$ satisfies $T_{1} = \mathrm{id}_A$ and $T_{xy} = T_x$ followed by $T_y$; written additively on the group $L.\mathrm{AlgPoints}\,hc\,k$ of $k$-points this gives $T_0 = \mathrm{id}$, $T_{P+Q} = T_P \circ T_Q$ and the isomorphism `translationIso P : A ≅ A` with inverse $T_{-P}$. With `modulePair M` the object $(A, M)$ of $\int^{\mathrm c}$, the theta group `thetaGroup f L hc M` is the subgroup of $\operatorname{Aut}(A,M) \times (L.\mathrm{AlgPoints}\,hc\,k)^{\times}$ of pairs $(g, z)$ whose base component is $T_z$; thus $g$ amounts to an isomorphism $T_z^{*}M \cong M$. `pt` is the projection to the point group; `liftOfIso z φ` produces the element with point $z$ from an isomorphism $T_z^{*}M \cong M$. For $g$ over $0$, `unitReading` reads the fibre component as an endomorphism of $M$, and `IsScalarElt g c` asserts that $\mathrm{pt}(g) = 1$ and that this endomorphism is multiplication by the image of $c \in k$, i.e. acts on each $\Gamma(M,U)$ by the global constant $c$. Finally `levelLift 𝓛 n P hx`, given $T_P$ followed by $[n]$ equal to $[n]$, yields the element of the theta group of $[n]^{*}𝓛$ with point $P$ built from the transport isomorphism attached to $hx$.
--
--   **Relation to Mathlib.** The co-Grothendieck construction $\int^{\mathrm c}$ and the pullback pseudofunctor `Scheme.Modules.pseudofunctor` are Mathlib's; the constructors and invertibility criteria for morphisms of $\int^{\mathrm c} F$, and the theta group attached to a relative group law, are the project's own.
--
--   **Where it is used.** The theta group is the group-theoretic frame for the level-$n$ pairing on torsion points: an element over a point $P$ is a lift of the translation $T_P$ to the line bundle $[n]^{*}\mathcal L$, and the scalars arising from commutators of such lifts are what the predicates `IsLevelPairingValue` and `IsRiemannForm` record, hence the Riemann form on the $\ell$-adic Tate module used in the Galois-theoretic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ThetaGroup.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

universe v₁ u₁ v₂ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂}}

def homMk {X Y : ∫ᶜ F} (b : X.base ⟶ Y.base) (φ : X.fiber ⟶ (F.map b.op.toLoc).toFunctor.obj Y.fiber) :
    X ⟶ Y := ⟨b, φ⟩

@[simp] theorem homMk_base {X Y : ∫ᶜ F} (b : X.base ⟶ Y.base)
    (φ : X.fiber ⟶ (F.map b.op.toLoc).toFunctor.obj Y.fiber) : (homMk b φ).base = b := rfl
@[simp] theorem homMk_fiber {X Y : ∫ᶜ F} (b : X.base ⟶ Y.base)
    (φ : X.fiber ⟶ (F.map b.op.toLoc).toFunctor.obj Y.fiber) : (homMk b φ).fiber = φ := rfl

theorem mono_homMk {X Y : ∫ᶜ F} (b : X.base ⟶ Y.base) [Mono b]
    (φ : X.fiber ⟶ (F.map b.op.toLoc).toFunctor.obj Y.fiber) [IsIso φ] : Mono (homMk b φ) := by
  refine ⟨fun {W} u v h => ?_⟩
  obtain ⟨ub, uf⟩ := u
  obtain ⟨vb, vf⟩ := v
  have hb : ub = vb := by
    have := congrArg Hom.base h
    simp only [categoryStruct_comp_base, homMk_base] at this
    exact (cancel_mono b).1 this
  subst hb
  have hf := Hom.congr h
  simp only [categoryStruct_comp_fiber, homMk_base, homMk_fiber, eqToHom_refl, Category.comp_id] at hf
  have hb1 : (F.mapComp b.op.toLoc ub.op.toLoc).inv.toNatTrans.app Y.fiber ≫
      (F.mapComp b.op.toLoc ub.op.toLoc).hom.toNatTrans.app Y.fiber = 𝟙 _ := by
    rw [← Cat.Hom₂.comp_app, Iso.inv_hom_id, Cat.Hom₂.id_app]
  have hb2 : (F.mapComp b.op.toLoc ub.op.toLoc).hom.toNatTrans.app Y.fiber ≫
      (F.mapComp b.op.toLoc ub.op.toLoc).inv.toNatTrans.app Y.fiber = 𝟙 _ := by
    rw [← Cat.Hom₂.comp_app, Iso.hom_inv_id, Cat.Hom₂.id_app]
  haveI : IsIso ((F.mapComp b.op.toLoc ub.op.toLoc).inv.toNatTrans.app Y.fiber) := ⟨⟨_, hb1, hb2⟩⟩
  have hf2 : (uf ≫ (F.map ub.op.toLoc).toFunctor.map φ) ≫ (F.mapComp b.op.toLoc ub.op.toLoc).inv.toNatTrans.app Y.fiber =
      (vf ≫ (F.map ub.op.toLoc).toFunctor.map φ) ≫ (F.mapComp b.op.toLoc ub.op.toLoc).inv.toNatTrans.app Y.fiber := by
    simp only [Category.assoc]
    exact hf
  have hf3 := (cancel_mono ((F.map ub.op.toLoc).toFunctor.map φ)).1
    ((cancel_mono ((F.mapComp b.op.toLoc ub.op.toLoc).inv.toNatTrans.app Y.fiber)).1 hf2)
  subst hf3
  rfl

def sectionMk {X Y : ∫ᶜ F} (e : X.base ≅ Y.base) (φ : X.fiber ≅ (F.map e.hom.op.toLoc).toFunctor.obj Y.fiber) :
    Y ⟶ X :=
  homMk e.inv
    ((F.mapId ⟨Opposite.op Y.base⟩).inv.toNatTrans.app Y.fiber ≫
      eqToHom (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, e.inv_hom_id]; rfl) ≫
      (F.mapComp e.hom.op.toLoc e.inv.op.toLoc).hom.toNatTrans.app Y.fiber ≫
      (F.map e.inv.op.toLoc).toFunctor.map φ.inv)

theorem sectionMk_comp {X Y : ∫ᶜ F} (e : X.base ≅ Y.base)
    (φ : X.fiber ≅ (F.map e.hom.op.toLoc).toFunctor.obj Y.fiber) :
    sectionMk e φ ≫ homMk e.hom φ.hom = 𝟙 Y := by
  apply Hom.ext _ _ (by simp [sectionMk, homMk])
  simp only [sectionMk, categoryStruct_comp_fiber, homMk_base, homMk_fiber, categoryStruct_id_fiber, Category.assoc]
  have h2 : (F.map e.inv.op.toLoc).toFunctor.map φ.inv ≫ (F.map e.inv.op.toLoc).toFunctor.map φ.hom = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]
  have h3 : (F.mapComp e.hom.op.toLoc e.inv.op.toLoc).hom.toNatTrans.app Y.fiber ≫
      (F.mapComp e.hom.op.toLoc e.inv.op.toLoc).inv.toNatTrans.app Y.fiber = 𝟙 _ := by
    rw [← Cat.Hom₂.comp_app, Iso.hom_inv_id, Cat.Hom₂.id_app]
  erw [reassoc_of% h2, h3]
  erw [Category.comp_id]
  rfl

instance isIso_homMk {X Y : ∫ᶜ F} (e : X.base ≅ Y.base)
    (φ : X.fiber ≅ (F.map e.hom.op.toLoc).toFunctor.obj Y.fiber) : IsIso (homMk e.hom φ.hom) := by
  haveI : Mono (homMk e.hom φ.hom) := mono_homMk e.hom φ.hom
  haveI : IsSplitEpi (homMk e.hom φ.hom) := IsSplitEpi.mk' ⟨sectionMk e φ, sectionMk_comp e φ⟩
  exact isIso_of_mono_of_isSplitEpi _

def isoMk {X Y : ∫ᶜ F} (e : X.base ≅ Y.base) (φ : X.fiber ≅ (F.map e.hom.op.toLoc).toFunctor.obj Y.fiber) :
    X ≅ Y :=
  asIso (homMk e.hom φ.hom)

@[simp] theorem isoMk_hom {X Y : ∫ᶜ F} (e : X.base ≅ Y.base)
    (φ : X.fiber ≅ (F.map e.hom.op.toLoc).toFunctor.obj Y.fiber) : (isoMk e φ).hom = homMk e.hom φ.hom := rfl

theorem isoMk_hom_base {X Y : ∫ᶜ F} (e : X.base ≅ Y.base)
    (φ : X.fiber ≅ (F.map e.hom.op.toLoc).toFunctor.obj Y.fiber) : (isoMk e φ).hom.base = e.hom := rfl

theorem isoMk_hom_fiber {X Y : ∫ᶜ F} (e : X.base ≅ Y.base)
    (φ : X.fiber ≅ (F.map e.hom.op.toLoc).toFunctor.obj Y.fiber) : (isoMk e φ).hom.fiber = φ.hom := rfl

end CategoryTheory.Pseudofunctor.CoGrothendieck

namespace AlgebraicGeometry

def Scheme.Modules.fibration : Pseudofunctor (LocallyDiscrete (Scheme.{0}ᵒᵖ)) Cat.{0, 1} :=
  (Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁

@[simp] theorem Scheme.Modules.fibration_obj (X : Scheme.{0}) :
    (Scheme.Modules.fibration.obj ⟨Opposite.op X⟩ : Type 1) = X.Modules := rfl

@[simp] theorem Scheme.Modules.fibration_map_toFunctor {X Y : Scheme.{0}} (g : X ⟶ Y) :
    (Scheme.Modules.fibration.map g.op.toLoc).toFunctor = Scheme.Modules.pullback g := rfl

namespace RiemannForm

variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
variable (L : RelativeGroupLaw k f)

theorem constPt_eq_schemeHomOverComp (x : Pt f) :
    constPt f x = schemeHomOverComp f (by rw [specMap_algebraMap_self, Category.comp_id]) x :=
  Subtype.ext rfl

theorem translation_one : translation f L (L.one _) = 𝟙 A := by
  unfold translation
  rw [constPt_eq_schemeHomOverComp, L.one_natural, L.mul_one]

theorem translation_mul (x y : Pt f) :
    translation f L (L.mul _ x y) = translation f L x ≫ translation f L y := by
  have hx := translation_over f L x
  have e1 : translation f L x ≫ translation f L y =
      (schemeHomOverComp (translation f L x) hx (L.mul f RelativeGroupLaw.idPoint (constPt f y))).1 := rfl
  rw [e1, L.mul_natural]
  have e2 : schemeHomOverComp (translation f L x) hx RelativeGroupLaw.idPoint =
      L.mul f RelativeGroupLaw.idPoint (constPt f x) := Subtype.ext (Category.comp_id _)
  have e3 : schemeHomOverComp (translation f L x) hx (constPt f y) = constPt f y :=
    Subtype.ext (show translation f L x ≫ (f ≫ y.1) = f ≫ y.1 by rw [← Category.assoc, hx])
  rw [e2, e3, L.mul_assoc]
  unfold translation
  rw [constPt_eq_schemeHomOverComp f (L.mul _ x y), L.mul_natural, ← constPt_eq_schemeHomOverComp,
    ← constPt_eq_schemeHomOverComp]

variable (hc : L.IsCommutative)

theorem translation_toPoint_zero :
    translation f L (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)) = 𝟙 A :=
  translation_one f L

theorem translation_toPoint_add (P Q : L.AlgPoints hc k) :
    translation f L (RelativeGroupLaw.AlgPoints.toPoint (P + Q)) =
      translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint Q) :=
  translation_mul f L _ _

def translationIso (P : L.AlgPoints hc k) : A ≅ A where
  hom := translation f L (RelativeGroupLaw.AlgPoints.toPoint P)
  inv := translation f L (RelativeGroupLaw.AlgPoints.toPoint (-P))
  hom_inv_id := by rw [← translation_toPoint_add, add_neg_cancel, translation_toPoint_zero]
  inv_hom_id := by rw [← translation_toPoint_add, neg_add_cancel, translation_toPoint_zero]

@[simp] theorem translationIso_hom (P : L.AlgPoints hc k) :
    (translationIso f L hc P).hom = translation f L (RelativeGroupLaw.AlgPoints.toPoint P) := rfl

abbrev modulePair (M : A.Modules) : Pseudofunctor.CoGrothendieck Scheme.Modules.fibration := ⟨A, M⟩

@[simp] theorem modulePair_base (M : A.Modules) : (modulePair (A := A) M).base = A := rfl
@[simp] theorem modulePair_fiber (M : A.Modules) : (modulePair (A := A) M).fiber = M := rfl

def thetaGroup (M : A.Modules) : Subgroup (Aut (modulePair (A := A) M) × Multiplicative (L.AlgPoints hc k)) where
  carrier := {g | g.1.hom.base = translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd g.2))}
  mul_mem' := by
    rintro ⟨a, P⟩ ⟨b, Q⟩ ha hb
    change (b ≪≫ a).hom.base = translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd (P * Q)))
    change a.hom.base = _ at ha
    change b.hom.base = _ at hb
    rw [toAdd_mul, add_comm, translation_toPoint_add, Iso.trans_hom, Pseudofunctor.CoGrothendieck.categoryStruct_comp_base,
      ha, hb]
  one_mem' := by
    change (Iso.refl (modulePair (A := A) M)).hom.base = translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd 1))
    rw [toAdd_one, translation_toPoint_zero]
    rfl
  inv_mem' := by
    rintro ⟨a, P⟩ ha
    change a.hom.base = translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd P)) at ha
    change a.symm.hom.base = translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd P⁻¹))
    have h1 : a.hom.base ≫ a.inv.base = 𝟙 A := by
      rw [← Pseudofunctor.CoGrothendieck.categoryStruct_comp_base, a.hom_inv_id]
      rfl
    rw [ha] at h1
    rw [Iso.symm_hom, toAdd_inv]
    haveI : Epi (translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd P))) :=
      (inferInstance : Epi (translationIso f L hc (Multiplicative.toAdd P)).hom)
    exact (cancel_epi (translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd P)))).1
      (h1.trans (translationIso f L hc (Multiplicative.toAdd P)).hom_inv_id.symm)

namespace thetaGroup

variable (M : A.Modules)

def pt : thetaGroup f L hc M →* Multiplicative (L.AlgPoints hc k) :=
  (MonoidHom.snd _ _).comp (thetaGroup f L hc M).subtype

@[simp] theorem pt_apply (g : thetaGroup f L hc M) : pt f L hc M g = g.1.2 := rfl

theorem base_eq (g : thetaGroup f L hc M) :
    g.1.1.hom.base = translation f L (RelativeGroupLaw.AlgPoints.toPoint (Multiplicative.toAdd g.1.2)) :=
  g.2

theorem base_eq_id_of_pt_eq_one (g : thetaGroup f L hc M) (hg : pt f L hc M g = 1) :
    g.1.1.hom.base = 𝟙 A := by
  rw [base_eq, ← pt_apply, hg, toAdd_one, translation_toPoint_zero]

def liftOfIso (z : L.AlgPoints hc k)
    (φ : (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint z))).obj M ≅ M) :
    thetaGroup f L hc M :=
  ⟨(Pseudofunctor.CoGrothendieck.isoMk (X := modulePair M) (Y := modulePair M) (translationIso f L hc z) φ.symm,
    Multiplicative.ofAdd z), rfl⟩

@[simp] theorem pt_liftOfIso (z : L.AlgPoints hc k)
    (φ : (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint z))).obj M ≅ M) :
    pt f L hc M (liftOfIso f L hc M z φ) = Multiplicative.ofAdd z := rfl

theorem liftOfIso_hom_fiber (z : L.AlgPoints hc k)
    (φ : (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint z))).obj M ≅ M) :
    (liftOfIso f L hc M z φ).1.1.hom.fiber = φ.inv := rfl

def unitReading {g : Aut (modulePair (A := A) M)} (h : g.hom.base = 𝟙 A) : M ⟶ M :=
  g.hom.fiber ≫ (Scheme.Modules.pullbackCongr h).hom.app M ≫ (Scheme.Modules.pullbackId A).hom.app M

def IsScalarElt (g : thetaGroup f L hc M) (c : k) : Prop :=
  ∃ hg : pt f L hc M g = 1, IsConstScalar f (unitReading M (base_eq_id_of_pt_eq_one f L hc M g hg)) c

end thetaGroup

def levelLift (𝓛 : A.Modules) (n : ℕ) (P : L.AlgPoints hc k)
    (hx : translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul n = L.schemeNsmul n) :
    thetaGroup f L hc ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛) :=
  thetaGroup.liftOfIso f L hc _ P (transportIso hx 𝓛)

@[simp] theorem pt_levelLift (𝓛 : A.Modules) (n : ℕ) (P : L.AlgPoints hc k)
    (hx : translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul n = L.schemeNsmul n) :
    thetaGroup.pt f L hc _ (levelLift f L hc 𝓛 n P hx) = Multiplicative.ofAdd P := rfl

end RiemannForm

end AlgebraicGeometry

end


