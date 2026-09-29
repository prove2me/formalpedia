-- Prove2me | Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
-- name    : AlgebraicGeometry_RelSubPicPresheaf
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/ce6ac59b-97ca-5ab2-b9a2-530f5fa0000b
-- title:
--   Relative Picard subpresheaf and its representability bridge
-- statement:
--   Fix a commutative ring $R$, a scheme $C$ with a structure morphism $c \colon C \to \operatorname{Spec} R$ and a section $\varepsilon$ of $c$ (an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c`, i.e. a morphism $\operatorname{Spec} R \to C$ composing with $c$ to the identity). Recall that for $t \colon T \to \operatorname{Spec} R$ a `RigidifiedLineBundle c ε t` is a module $L$ on $C \times_{\operatorname{Spec} R} T$ that is invertible (locally isomorphic to the unit sheaf) together with a trivialisation of its pullback along the section $T \to C\times_{\operatorname{Spec} R} T$ induced by $\varepsilon$, and that `Classes c ε t` is the quotient of these by the relation '$L \cong L'$' — an isomorphism of the underlying modules only, no compatibility with the rigidifications being required.
--
--   Two canonical isomorphisms of underlying modules are recorded: pulling back along $\psi$ then along $\varphi$ gives the same module as pulling back along the composite, and pulling back along the identity returns $L$.
--
--   For a `SubPicCondition P` (a family of predicates $P_t$ on rigidified line bundles, holding for the unit bundle, invariant under isomorphism of underlying modules, and stable under pullback), `SubPicCondition.onClasses` is the induced predicate on `Classes c ε t`, with the expected compatibilities: it evaluates on a representative, and it is preserved by the transition maps `classesMap`. From this, `relSubPicSubfunctor` is the subfunctor of `relPicardPresheaf c ε` on $(\mathrm{Over}\ \operatorname{Spec} R)^{\mathrm{op}}$ cut out pointwise by $P$, and `relSubPicPresheaf` is the associated presheaf of types.
--
--   The remaining declarations form the dictionary between the structure `RepresentsRelSubPic c ε P D` — a Poincaré bundle on $C\times_R D.P$ satisfying $P$, with the property that every $P$-bundle on $C\times_R T$ is its pullback along a unique $T \to D.P$ over $\operatorname{Spec} R$, plus the normalisation that pullback along the zero section of $D$ gives the unit bundle — and Mathlib's `Functor.RepresentableBy`. `pullbackClass` and `classifyClass` give the two directions on classes, `eq_classifyClass` and `mk_pullbackAlong_classifyClass` their mutual inverse properties, `representableBy` assembles the natural bijection $\operatorname{Hom}_{\operatorname{Spec} R}(T, D.P) \cong \operatorname{Pic}^P(T)$ exhibiting `Over.mk D.toBase` as representing `relSubPicPresheaf c ε P`, and `nonempty_of_representableBy` reverses this: any such natural bijection whose value on the zero section is the class of the unit bundle yields an element of `RepresentsRelSubPic c ε P D`, the Poincaré bundle being a representative of the image of $\mathrm{id}_{D.P}$.
--
--   **Relation to Mathlib.** Mathlib has no relative Picard functor or Poincaré bundle; those notions are the project's own, built on Mathlib's `SheafOfModules`/`Scheme.Modules` and scheme-theoretic pullbacks. The subfunctor and representability packaging use Mathlib's `CategoryTheory.Subfunctor` and `Functor.RepresentableBy`.
--
--   **Where it is used.** The presheaf `relSubPicPresheaf` and the bridge to `Functor.RepresentableBy` are the interface through which a designated relative $\mathrm{Pic}^0$-scheme is recognised as representing a rigidified Picard condition, and hence acquires a group structure and points; this feeds the relative Jacobian and good-reduction layer used for the Jacobians of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelSubPicPresheaf.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian Opposite

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

namespace RigidifiedLineBundle

noncomputable def pullbackAlongPullbackAlongIso {T T' T'' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} {t'' : T'' ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) (ψ : SchemeHomOver t' t) (φ : SchemeHomOver t'' t') :
    ((M.pullbackAlong ψ).pullbackAlong φ).L ≅ (M.pullbackAlong (postComp ψ φ)).L :=
  (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c ψ φ)).app M.L

noncomputable def pullbackAlongIdIso {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) :
    (M.pullbackAlong ⟨𝟙 T, Category.id_comp t⟩).L ≅ M.L :=
  (Scheme.Modules.pullbackCongr (baseChangeSnd_id c t)).app M.L ≪≫
    (Scheme.Modules.pullbackId _).app M.L

end RigidifiedLineBundle

namespace SubPicCondition

def onClasses (P : SubPicCondition c ε) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    RigidifiedLineBundle.Classes c ε t → Prop :=
  Quotient.lift (P.P t) fun M M' h => propext ⟨P.congr t M M' h, P.congr t M' M ⟨h.some.symm⟩⟩

@[simp] theorem onClasses_mk (P : SubPicCondition c ε) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) : P.onClasses t (Quotient.mk _ M) ↔ P.P t M := Iff.rfl

theorem onClasses_classesMap (P : SubPicCondition c ε) {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) (x : RigidifiedLineBundle.Classes c ε t)
    (hx : P.onClasses t x) : P.onClasses t' (RigidifiedLineBundle.classesMap ψ x) := by
  induction x using Quotient.ind
  exact P.pullback_mem _ _ ψ _ hx

end SubPicCondition

def relSubPicSubfunctor (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (P : SubPicCondition c ε) : Subfunctor (relPicardPresheaf c ε) where
  obj X := {x | P.onClasses X.unop.hom x}
  map φ := fun x hx => P.onClasses_classesMap ⟨φ.unop.left, Over.w φ.unop⟩ x hx

def relSubPicPresheaf (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (P : SubPicCondition c ε) : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (u + 1) :=
  (relSubPicSubfunctor c ε P).toFunctor

namespace RepresentsRelSubPic

variable {P : SubPicCondition c ε} {D : RelativePic0Designation R c}

def pullbackClass (h : RepresentsRelSubPic c ε P D) (X : Over (Spec (CommRingCat.of R)))
    (g : X ⟶ Over.mk D.toBase) : (relSubPicPresheaf c ε P).obj (op X) :=
  ⟨Quotient.mk _ (h.poincare.pullbackAlong ⟨g.left, Over.w g⟩), P.pullback_mem _ _ _ _ h.poincare_mem⟩

noncomputable def classifyClass (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : RigidifiedLineBundle.Classes c ε t) (hx : P.onClasses t x) :
    SchemeHomOver t D.toBase :=
  h.classify t x.out (by rwa [← Quotient.out_eq x] at hx)

theorem eq_classifyClass (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : RigidifiedLineBundle.Classes c ε t) (hx : P.onClasses t x)
    (g : SchemeHomOver t D.toBase) (hg : Quotient.mk _ (h.poincare.pullbackAlong g) = x) :
    g = h.classifyClass t x hx := by
  refine h.classify_unique t _ _ g ?_
  rw [← Quotient.out_eq x] at hg
  exact Quotient.exact hg

theorem mk_pullbackAlong_classifyClass (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : RigidifiedLineBundle.Classes c ε t) (hx : P.onClasses t x) :
    Quotient.mk _ (h.poincare.pullbackAlong (h.classifyClass t x hx)) = x := by
  conv_rhs => rw [← Quotient.out_eq x]
  exact Quotient.sound (h.classify_spec t _ _)

noncomputable def representableBy (h : RepresentsRelSubPic c ε P D) :
    (relSubPicPresheaf c ε P).RepresentableBy (Over.mk D.toBase) where
  homEquiv {X} :=
    { toFun := fun g => h.pullbackClass X g
      invFun := fun x => Over.homMk (h.classifyClass X.hom x.1 x.2).1 (h.classifyClass X.hom x.1 x.2).2
      left_inv := fun g => Over.OverMorphism.ext (congrArg Subtype.val
        (h.eq_classifyClass X.hom _ _ ⟨g.left, Over.w g⟩ rfl)).symm
      right_inv := fun x => Subtype.ext (h.mk_pullbackAlong_classifyClass X.hom x.1 x.2) }
  homEquiv_comp {X X'} f g := by
    apply Subtype.ext
    apply Quotient.sound
    exact ⟨(h.poincare.pullbackAlongPullbackAlongIso ⟨g.left, Over.w g⟩ ⟨f.left, Over.w f⟩).symm⟩

end RepresentsRelSubPic

@[simp] theorem relSubPicPresheaf_map_coe {P : SubPicCondition c ε} {X X' : (Over (Spec (CommRingCat.of R)))ᵒᵖ}
    (φ : X ⟶ X') (x : (relSubPicPresheaf c ε P).obj X) :
    ((relSubPicPresheaf c ε P).map φ x).1 = RigidifiedLineBundle.classesMap ⟨φ.unop.left, Over.w φ.unop⟩ x.1 :=
  rfl

namespace RepresentsRelSubPic

variable {P : SubPicCondition c ε} {D : RelativePic0Designation R c}

theorem nonempty_of_representableBy (e : (relSubPicPresheaf c ε P).RepresentableBy (Over.mk D.toBase))
    (h0 : (e.homEquiv (Over.homMk D.zeroSection D.zeroSection_toBase :
        Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk D.toBase)).1 =
      relPicardPresheaf.unitClass c ε (Over.mk (𝟙 _))) :
    Nonempty (RepresentsRelSubPic c ε P D) := by

  let u := e.homEquiv (𝟙 (Over.mk D.toBase))
  let Q : RigidifiedLineBundle c ε D.toBase := u.1.out
  have hQ : P.P D.toBase Q := by
    have h2 : P.onClasses D.toBase u.1 := u.2
    rwa [← Quotient.out_eq u.1] at h2

  have key : ∀ (X : Over (Spec (CommRingCat.of R))) (g : X ⟶ Over.mk D.toBase),
      (e.homEquiv g).1 = Quotient.mk _ (Q.pullbackAlong ⟨g.left, Over.w g⟩) := by
    intro X g
    have hc := e.homEquiv_comp g (𝟙 _)
    rw [Category.comp_id] at hc
    rw [hc, relSubPicPresheaf_map_coe]
    change RigidifiedLineBundle.classesMap _ u.1 = _
    conv_lhs => rw [← Quotient.out_eq u.1]
    rfl
  refine ⟨{ poincare := Q, poincare_mem := hQ, univ := ?_, zero := ?_ }⟩
  · intro T t M hM
    let x : (relSubPicPresheaf c ε P).obj (op (Over.mk t)) := ⟨Quotient.mk _ M, hM⟩
    let g : Over.mk t ⟶ Over.mk D.toBase := e.homEquiv.symm x
    have hg : e.homEquiv g = x := e.homEquiv.apply_symm_apply x
    refine ⟨⟨g.left, Over.w g⟩, ?_, fun g'' hg'' => ?_⟩
    · have h1 : (e.homEquiv g).1 = Quotient.mk _ M := congrArg Subtype.val hg
      rw [key] at h1
      exact Quotient.exact h1
    · have h2 : e.homEquiv (Over.homMk g''.1 g''.2 : Over.mk t ⟶ Over.mk D.toBase) = x := by
        apply Subtype.ext
        rw [key]
        exact Quotient.sound hg''
      have h3 : (Over.homMk g''.1 g''.2 : Over.mk t ⟶ Over.mk D.toBase) = g :=
        e.homEquiv.injective (h2.trans hg.symm)
      exact Subtype.ext (congrArg (fun k => k.left) h3)
  · have h1 := h0
    rw [key] at h1
    exact Quotient.exact h1

end RepresentsRelSubPic

end AlgebraicGeometry.RelPicard

end


