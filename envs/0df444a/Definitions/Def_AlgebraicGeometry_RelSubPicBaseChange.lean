-- Prove2me | Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
-- name    : AlgebraicGeometry_RelSubPicBaseChange
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/20abc5bb-0e76-5126-b394-6edecc42ddaa
-- title:
--   Base change for the rigidified relative Picard presheaf
-- statement:
--   Fix a commutative ring $R$, a morphism $c\colon C\to\operatorname{Spec} R$ together with a section $\varepsilon$ of it (an element of `SchemeHomOver (𝟙 (Spec R)) c`, i.e. a morphism $\operatorname{Spec} R\to C$ whose composite with $c$ is the identity), and an $R$-algebra $R'$; write $c' =$ `baseChange R c R'` for $\operatorname{pr}_2\colon C\times_{\operatorname{Spec} R}\operatorname{Spec} R'\to\operatorname{Spec} R'$ and $\varepsilon' =$ `sectionBaseChange R' ε` for the induced section. For an $R'$-scheme $t'\colon T\to\operatorname{Spec} R'$, `κ` is the canonical isomorphism $(C\times_R R')\times_{R'} T\cong C\times_R T$ (the latter formed along $t'$ followed by $\operatorname{Spec}(R'\!\leftarrow\!R)$), obtained from Mathlib's iterated-pullback isomorphism; the accompanying lemmas identify its composites with the two projections, with the rigidifying section `rigSection` and with the transition maps `baseChangeSnd` along a morphism of $R'$-schemes (the latter rephrased over $R$ by `overR`). Transport of modules along `κ` gives mutually inverse operations `toR` and `ofR` between rigidified line bundles for $(c',\varepsilon')$ over $T/R'$ and for $(c,\varepsilon)$ over $T/R$ — a rigidified line bundle being a module on the relevant pullback, locally isomorphic to the unit sheaf, together with a non-empty set of isomorphisms of its restriction along the rigidifying section with the unit sheaf — with specified isomorphisms of underlying modules expressing the two round trips, compatibility with pullback and with the unit bundle. `restrict` transports a `SubPicCondition` for $(c,\varepsilon)$ (a family of predicates on rigidified line bundles closed under the unit, under isomorphism of underlying modules and under pullback) to one for $(c',\varepsilon')$ by testing `toR`; `subPicCondition_ext` is the extensionality principle for such conditions. The fibre comparison maps `fibreMap`, `fibreMap'` over a point $\operatorname{Spec} k\to T$ yield `fibrewiseAlgEquivZero_toR_iff` and hence `restrict_algEquivZeroCut`: the restriction of the cut `algEquivZeroCut` is the corresponding cut for $(c',\varepsilon')$. On classes (rigidified bundles modulo isomorphism of underlying modules) `classesEquiv` is the induced bijection, natural in $T$ and compatible with the defining predicates; this produces `relSubPicPresheafRestrictIso`, an isomorphism of presheaves on $(\mathbf{Over}\ \operatorname{Spec} R')^{\mathrm{op}}$ between `relSubPicPresheaf` for $(c',\varepsilon',\text{restrict }P)$ and the composite of $(\mathbf{Over}\ \operatorname{Spec}(R\to R'))^{\mathrm{op}}$ with `relSubPicPresheaf` for $(c,\varepsilon,P)$, its special case for the algebraic-equivalence cut, and `representableByRestrict`: from `RepresentsRelSubPic` data for that cut over $R'$ with designation $D'$ one obtains that $D'$'s structure morphism represents the restriction to $R'$-schemes of the presheaf over $R$. Two simp lemmas record the underlying class of the components of the comparison isomorphism.
--
--   **Relation to Mathlib.** Mathlib has no relative Picard functor or notion of rigidified line bundle; those are the project's own, built on Mathlib's `Scheme.Modules.pullback`, `SheafOfModules.unit`, `Subfunctor` and `Functor.RepresentableBy`. The comparison isomorphism `κ` is Mathlib's iterated-pullback isomorphism `pullbackLeftPullbackSndIso` specialised to this situation.
--
--   **Where it is used.** This is the functor-level compatibility of the rigidified relative Picard presheaf, and of its algebraic-equivalence-to-zero cut, with extension of the base ring; it is what allows a representing object constructed over $R'$ to be recognised as representing the restriction of the functor defined over $R$, as needed when descending relative Jacobians of curves along a base extension in the treatment of Jacobians of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelSubPicBaseChange.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian Opposite

namespace AlgebraicGeometry.RelPicard.BaseChange

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (R' : Type u) [CommRing R'] [Algebra R R']

noncomputable def κ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    pullback (baseChange R c R') t' ≅ pullback c (t' ≫ specMap R R') :=
  pullbackLeftPullbackSndIso c (specMap R R') t'

theorem κ_hom_snd {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    (κ c R' t').hom ≫ pullback.snd c (t' ≫ specMap R R') = pullback.snd (baseChange R c R') t' :=
  pullbackLeftPullbackSndIso_hom_snd _ _ _

theorem κ_hom_fst {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    (κ c R' t').hom ≫ pullback.fst c (t' ≫ specMap R R') =
      pullback.fst (baseChange R c R') t' ≫ pullback.fst c (specMap R R') :=
  pullbackLeftPullbackSndIso_hom_fst _ _ _

omit [Algebra R R'] in
theorem rigSection_fst' {T : Scheme.{u}} (cc : C ⟶ Spec (CommRingCat.of R')) (t : T ⟶ Spec (CommRingCat.of R'))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) cc) :
    rigSection cc t e ≫ pullback.fst cc t = t ≫ e.1 :=
  pullback.lift_fst _ _ _

omit [Algebra R R'] in
theorem rigSection_snd' {T : Scheme.{u}} (cc : C ⟶ Spec (CommRingCat.of R')) (t : T ⟶ Spec (CommRingCat.of R'))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) cc) :
    rigSection cc t e ≫ pullback.snd cc t = 𝟙 T :=
  pullback.lift_snd _ _ _

omit [Algebra R R'] in
theorem baseChangeSnd_fst' {T T' : Scheme.{u}} (cc : C ⟶ Spec (CommRingCat.of R'))
    {t : T ⟶ Spec (CommRingCat.of R')} {t' : T' ⟶ Spec (CommRingCat.of R')} (ψ : SchemeHomOver t' t) :
    baseChangeSnd cc ψ ≫ pullback.fst cc t = pullback.fst cc t' :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

omit [Algebra R R'] in
theorem baseChangeSnd_snd' {T T' : Scheme.{u}} (cc : C ⟶ Spec (CommRingCat.of R'))
    {t : T ⟶ Spec (CommRingCat.of R')} {t' : T' ⟶ Spec (CommRingCat.of R')} (ψ : SchemeHomOver t' t) :
    baseChangeSnd cc ψ ≫ pullback.snd cc t = pullback.snd cc t' ≫ ψ.1 :=
  pullback.lift_snd _ _ _

theorem rigSection_κ_hom {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    rigSection (baseChange R c R') t' (sectionBaseChange R' ε) ≫ (κ c R' t').hom =
      rigSection c (t' ≫ specMap R R') ε := by
  apply pullback.hom_ext
  · rw [Category.assoc, κ_hom_fst, ← Category.assoc, rigSection_fst', rigSection_fst', Category.assoc,
      sectionBaseChange_coe_fst, Category.assoc]
  · rw [Category.assoc, κ_hom_snd, rigSection_snd', rigSection_snd']

theorem rigSection_κ_inv {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    rigSection c (t' ≫ specMap R R') ε ≫ (κ c R' t').inv =
      rigSection (baseChange R c R') t' (sectionBaseChange R' ε) := by
  rw [← rigSection_κ_hom c ε R' t', Category.assoc, Iso.hom_inv_id, Category.comp_id]

def overR {T T'' : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')} {t'' : T'' ⟶ Spec (CommRingCat.of R')}
    (ψ : SchemeHomOver t'' t') : SchemeHomOver (t'' ≫ specMap R R') (t' ≫ specMap R R') :=
  ⟨ψ.1, by rw [← Category.assoc, ψ.2]⟩

theorem baseChangeSnd_κ_hom {T T'' : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    {t'' : T'' ⟶ Spec (CommRingCat.of R')} (ψ : SchemeHomOver t'' t') :
    baseChangeSnd (baseChange R c R') ψ ≫ (κ c R' t').hom =
      (κ c R' t'').hom ≫ baseChangeSnd c (overR R' ψ) := by
  apply pullback.hom_ext
  · rw [Category.assoc, κ_hom_fst, ← Category.assoc, baseChangeSnd_fst', Category.assoc, baseChangeSnd_fst',
      κ_hom_fst]
  · rw [Category.assoc, κ_hom_snd, baseChangeSnd_snd', Category.assoc, baseChangeSnd_snd', ← Category.assoc,
      κ_hom_snd]
    rfl

noncomputable def toR {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (M : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε) t') :
    RigidifiedLineBundle c ε (t' ≫ specMap R R') where
  L := (Scheme.Modules.pullback (κ c R' t').inv).obj M.L
  isInvertible := M.isInvertible.pullback _
  rigidified :=
    ⟨(Scheme.Modules.pullbackComp (rigSection c (t' ≫ specMap R R') ε) (κ c R' t').inv).app M.L ≪≫
      (Scheme.Modules.pullbackCongr (rigSection_κ_inv c ε R' t')).app M.L ≪≫ M.rigidified.some⟩

noncomputable def ofR {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (M : RigidifiedLineBundle c ε (t' ≫ specMap R R')) :
    RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε) t' where
  L := (Scheme.Modules.pullback (κ c R' t').hom).obj M.L
  isInvertible := M.isInvertible.pullback _
  rigidified :=
    ⟨(Scheme.Modules.pullbackComp (rigSection (baseChange R c R') t' (sectionBaseChange R' ε))
        (κ c R' t').hom).app M.L ≪≫
      (Scheme.Modules.pullbackCongr (rigSection_κ_hom c ε R' t')).app M.L ≪≫ M.rigidified.some⟩

noncomputable def toR_ofR_iso {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (M : RigidifiedLineBundle c ε (t' ≫ specMap R R')) : (toR c ε R' (ofR c ε R' M)).L ≅ M.L :=
  (Scheme.Modules.pullbackComp (κ c R' t').inv (κ c R' t').hom).app M.L ≪≫
    (Scheme.Modules.pullbackCongr ((κ c R' t').inv_hom_id)).app M.L ≪≫
    (Scheme.Modules.pullbackId _).app M.L

noncomputable def ofR_toR_iso {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (M : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε) t') :
    (ofR c ε R' (toR c ε R' M)).L ≅ M.L :=
  (Scheme.Modules.pullbackComp (κ c R' t').hom (κ c R' t').inv).app M.L ≪≫
    (Scheme.Modules.pullbackCongr ((κ c R' t').hom_inv_id)).app M.L ≪≫
    (Scheme.Modules.pullbackId _).app M.L

theorem baseChangeSnd_κ_inv {T T'' : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    {t'' : T'' ⟶ Spec (CommRingCat.of R')} (ψ : SchemeHomOver t'' t') :
    baseChangeSnd c (overR R' ψ) ≫ (κ c R' t').inv = (κ c R' t'').inv ≫ baseChangeSnd (baseChange R c R') ψ := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← baseChangeSnd_κ_hom, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

noncomputable def toR_pullbackAlong_iso {T T'' : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    {t'' : T'' ⟶ Spec (CommRingCat.of R')} (ψ : SchemeHomOver t'' t')
    (M : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε) t') :
    ((toR c ε R' M).pullbackAlong (overR R' ψ)).L ≅ (toR c ε R' (M.pullbackAlong ψ)).L :=
  (Scheme.Modules.pullbackComp (baseChangeSnd c (overR R' ψ)) (κ c R' t').inv).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_κ_inv c R' ψ)).app M.L ≪≫
    ((Scheme.Modules.pullbackComp (κ c R' t'').inv (baseChangeSnd (baseChange R c R') ψ)).app M.L).symm

noncomputable def toR_unit_iso {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    (toR c ε R' (RigidifiedLineBundle.unit t')).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) (t' ≫ specMap R R')).L :=
  Scheme.Modules.pullbackUnitIso (κ c R' t').inv

noncomputable def restrict (P : SubPicCondition c ε) :
    SubPicCondition (baseChange R c R') (sectionBaseChange R' ε) where
  P := fun t' M => P.P (t' ≫ specMap R R') (toR c ε R' M)
  unit_mem := fun t' => P.congr _ _ _ ⟨(toR_unit_iso c ε R' t').symm⟩ (P.unit_mem (t' ≫ specMap R R'))
  congr := fun t' _ _ h hM => P.congr _ _ _ ⟨(Scheme.Modules.pullback (κ c R' t').inv).mapIso h.some⟩ hM
  pullback_mem := fun _ _ ψ M hM =>
    P.congr _ _ _ ⟨toR_pullbackAlong_iso c ε R' ψ M⟩ (P.pullback_mem _ _ (overR R' ψ) _ hM)

@[simp] theorem restrict_P (P : SubPicCondition c ε) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (M : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε) t') :
    (restrict c ε R' P).P t' M ↔ P.P (t' ≫ specMap R R') (toR c ε R' M) := Iff.rfl

omit [Algebra R R'] in
theorem subPicCondition_ext {cc : C ⟶ Spec (CommRingCat.of R')}
    {e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) cc} {P Q : SubPicCondition cc e}
    (h : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (M : RigidifiedLineBundle cc e t), P.P t M ↔ Q.P t M) :
    P = Q := by
  obtain ⟨P1, h1, h2, h3⟩ := P
  obtain ⟨Q1, g1, g2, g3⟩ := Q
  have hPQ : @P1 = @Q1 := by
    funext T t M
    exact propext (h t M)
  subst hPQ
  rfl

section fibres

variable {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) {k : Type u} [Field k]
  (σ : Spec (CommRingCat.of k) ⟶ T)

noncomputable def fibreMap :
    pullback (pullback.snd (baseChange R c R') t') σ ⟶ pullback (pullback.snd c (t' ≫ specMap R R')) σ :=
  pullback.map _ _ _ _ (κ c R' t').hom (𝟙 _) (𝟙 T) (by rw [Category.comp_id, κ_hom_snd])
    (by rw [Category.comp_id, Category.id_comp])

noncomputable def fibreMap' :
    pullback (pullback.snd c (t' ≫ specMap R R')) σ ⟶ pullback (pullback.snd (baseChange R c R') t') σ :=
  pullback.map _ _ _ _ (κ c R' t').inv (𝟙 _) (𝟙 T)
    (by rw [Category.comp_id, ← κ_hom_snd, Iso.inv_hom_id_assoc]) (by rw [Category.comp_id, Category.id_comp])

theorem fibreMap_fibreAt : fibreMap c R' t' σ ≫ fibreAt c (t' ≫ specMap R R') σ = fibreAt (baseChange R c R') t' σ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem fibreMap'_fibreAt :
    fibreMap' c R' t' σ ≫ fibreAt (baseChange R c R') t' σ = fibreAt c (t' ≫ specMap R R') σ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem fibreMap_fst : fibreMap c R' t' σ ≫ pullback.fst (pullback.snd c (t' ≫ specMap R R')) σ =
    pullback.fst (pullback.snd (baseChange R c R') t') σ ≫ (κ c R' t').hom :=
  pullback.lift_fst _ _ _

theorem fibreMap'_fst : fibreMap' c R' t' σ ≫ pullback.fst (pullback.snd (baseChange R c R') t') σ =
    pullback.fst (pullback.snd c (t' ≫ specMap R R')) σ ≫ (κ c R' t').inv :=
  pullback.lift_fst _ _ _

end fibres

theorem fibrewiseAlgEquivZero_toR_iff {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (M : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε) t') :
    FibrewiseAlgEquivZero (toR c ε R' M) ↔ FibrewiseAlgEquivZero M := by
  constructor
  · intro h k _ _ σ
    have h1 := (h k σ).pullback (fibreMap c R' t' σ) (fibreMap_fibreAt c R' t' σ)
    refine h1.of_iso ?_
    exact (Scheme.Modules.pullbackComp (fibreMap c R' t' σ)
        (pullback.fst (pullback.snd c (t' ≫ specMap R R')) σ)).app _ ≪≫
      (Scheme.Modules.pullbackComp (fibreMap c R' t' σ ≫ pullback.fst (pullback.snd c (t' ≫ specMap R R')) σ)
        (κ c R' t').inv).app M.L ≪≫
      (Scheme.Modules.pullbackCongr (by
        rw [fibreMap_fst, Category.assoc, Iso.hom_inv_id, Category.comp_id])).app M.L
  · intro h k _ _ σ
    have h1 := (h k σ).pullback (fibreMap' c R' t' σ) (fibreMap'_fibreAt c R' t' σ)
    refine h1.of_iso ?_
    exact (Scheme.Modules.pullbackComp (fibreMap' c R' t' σ)
        (pullback.fst (pullback.snd (baseChange R c R') t') σ)).app M.L ≪≫
      (Scheme.Modules.pullbackCongr (fibreMap'_fst c R' t' σ)).app M.L ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst (pullback.snd c (t' ≫ specMap R R')) σ)
        (κ c R' t').inv).app M.L).symm

theorem restrict_algEquivZeroCut :
    restrict c ε R' (algEquivZeroCut c ε) = algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε) :=
  subPicCondition_ext R' (fun _ M => fibrewiseAlgEquivZero_toR_iff c ε R' M)

noncomputable def classesEquiv {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    RigidifiedLineBundle.Classes (baseChange R c R') (sectionBaseChange R' ε) t' ≃
      RigidifiedLineBundle.Classes c ε (t' ≫ specMap R R') where
  toFun := Quotient.map (toR c ε R') (fun _ _ h => ⟨(Scheme.Modules.pullback (κ c R' t').inv).mapIso h.some⟩)
  invFun := Quotient.map (ofR c ε R') (fun _ _ h => ⟨(Scheme.Modules.pullback (κ c R' t').hom).mapIso h.some⟩)
  left_inv := fun x => by
    induction x using Quotient.ind
    exact Quotient.sound ⟨ofR_toR_iso c ε R' _⟩
  right_inv := fun x => by
    induction x using Quotient.ind
    exact Quotient.sound ⟨toR_ofR_iso c ε R' _⟩

theorem onClasses_classesEquiv (P : SubPicCondition c ε) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (x : RigidifiedLineBundle.Classes (baseChange R c R') (sectionBaseChange R' ε) t') :
    P.onClasses (t' ≫ specMap R R') (classesEquiv c ε R' t' x) ↔ (restrict c ε R' P).onClasses t' x := by
  induction x using Quotient.ind
  exact Iff.rfl

theorem classesEquiv_classesMap {T T'' : Scheme.{u}}
    {t' : T ⟶ Spec (CommRingCat.of R')} {t'' : T'' ⟶ Spec (CommRingCat.of R')} (ψ : SchemeHomOver t'' t')
    (x : RigidifiedLineBundle.Classes (baseChange R c R') (sectionBaseChange R' ε) t') :
    classesEquiv c ε R' t'' (RigidifiedLineBundle.classesMap ψ x) =
      RigidifiedLineBundle.classesMap (overR R' ψ) (classesEquiv c ε R' t' x) := by
  induction x using Quotient.ind
  exact Quotient.sound ⟨(toR_pullbackAlong_iso c ε R' ψ _).symm⟩

noncomputable def relSubPicPresheafRestrictIso (P : SubPicCondition c ε) :
    relSubPicPresheaf (baseChange R c R') (sectionBaseChange R' ε) (restrict c ε R' P) ≅
      (Over.map (specMap R R')).op ⋙ relSubPicPresheaf c ε P :=
  NatIso.ofComponents
    (fun X => Equiv.toIso
      { toFun := fun x => ⟨classesEquiv c ε R' X.unop.hom x.1, (onClasses_classesEquiv c ε R' P _ x.1).2 x.2⟩
        invFun := fun y => ⟨(classesEquiv c ε R' X.unop.hom).symm y.1, by
          have h := (onClasses_classesEquiv c ε R' P X.unop.hom ((classesEquiv c ε R' X.unop.hom).symm y.1)).1
          rw [Equiv.apply_symm_apply] at h
          exact h y.2⟩
        left_inv := fun x => Subtype.ext ((classesEquiv c ε R' X.unop.hom).symm_apply_apply x.1)
        right_inv := fun y => Subtype.ext ((classesEquiv c ε R' X.unop.hom).apply_symm_apply y.1) })
    (fun {X Y} φ => by
      apply TypeCat.homEquiv.injective
      funext x
      apply Subtype.ext
      exact classesEquiv_classesMap c ε R' ⟨φ.unop.left, Over.w φ.unop⟩ x.1)

noncomputable def relSubPicPresheafAlgEquivZeroCutIso :
    relSubPicPresheaf (baseChange R c R') (sectionBaseChange R' ε)
        (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) ≅
      (Over.map (specMap R R')).op ⋙ relSubPicPresheaf c ε (algEquivZeroCut c ε) :=
  eqToIso (by rw [← restrict_algEquivZeroCut]) ≪≫ relSubPicPresheafRestrictIso c ε R' (algEquivZeroCut c ε)

noncomputable def representableByRestrict {D' : RelativePic0Designation R' (baseChange R c R')}
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) D') :
    ((Over.map (specMap R R')).op ⋙ relSubPicPresheaf c ε (algEquivZeroCut c ε)).RepresentableBy
      (Over.mk D'.toBase) :=
  h'.representableBy.ofIso (relSubPicPresheafAlgEquivZeroCutIso c ε R')

omit [Algebra R R'] in

theorem relSubPicPresheaf_eqToHom_app_coe {cc : C ⟶ Spec (CommRingCat.of R')}
    {e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) cc} {P₁ P₂ : SubPicCondition cc e} (h : P₁ = P₂)
    (X : (Over (Spec (CommRingCat.of R')))ᵒᵖ) (x : (relSubPicPresheaf cc e P₁).obj X) :
    ((eqToHom (congrArg (relSubPicPresheaf cc e) h)).app X x).1 = x.1 := by
  subst h
  rfl

@[simp] theorem relSubPicPresheafRestrictIso_hom_app_coe (P : SubPicCondition c ε)
    (X : (Over (Spec (CommRingCat.of R')))ᵒᵖ)
    (x : (relSubPicPresheaf (baseChange R c R') (sectionBaseChange R' ε) (restrict c ε R' P)).obj X) :
    ((relSubPicPresheafRestrictIso c ε R' P).hom.app X x).1 = classesEquiv c ε R' X.unop.hom x.1 :=
  rfl

@[simp] theorem relSubPicPresheafRestrictIso_inv_app_coe (P : SubPicCondition c ε)
    (X : (Over (Spec (CommRingCat.of R')))ᵒᵖ)
    (y : ((Over.map (specMap R R')).op ⋙ relSubPicPresheaf c ε P).obj X) :
    ((relSubPicPresheafRestrictIso c ε R' P).inv.app X y).1 = (classesEquiv c ε R' X.unop.hom).symm y.1 :=
  rfl

end AlgebraicGeometry.RelPicard.BaseChange


