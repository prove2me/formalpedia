-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nonempty_etale_cohomology_equiv_rightDerived_global_sections
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-20T21:03:29.157327+00:00
-- url     : https://prove2.me/submissions/2ba65898-e0b2-4bb7-b362-37b7bd032f3c

import Definitions.Def_AlgebraicGeometry_SmallEtaleAbelianDirectImage
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) etaleHasSheafify (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) etaleHasExt (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) etaleEnoughInjectives (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

section

open AlgebraicGeometry CategoryTheory Opposite
namespace PhilipponEtaleAcyclicCohomology
universe u
abbrev globalSections (X : Scheme.{u}) :=
  (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op (Scheme.Etale.mk (𝟙 X)))
end PhilipponEtaleAcyclicCohomology

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits HomologicalComplex


namespace PhilipponDerivedAdjunction

universe u v u' v' w w'

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Abelian C] [Abelian D]

private def homotopyAdjunction {L : D ⥤ C} {R : C ⥤ D} [L.Additive] [R.Additive]
    (adj : L ⊣ R) (c : ComplexShape ℕ) :
    L.mapHomotopyCategory c ⊣ R.mapHomotopyCategory c where
  unit := {
    app := (NatTrans.mapHomotopyCategory adj.unit c).app
    naturality := by
      rintro ⟨K⟩ ⟨M⟩ ⟨g : K ⟶ M⟩
      simp only [HomotopyCategory.quot_mk_eq_quotient_map, NatTrans.mapHomotopyCategory_app,
        Functor.id_map, Functor.comp_map, Functor.mapHomotopyCategory_map, ← Functor.map_comp]
      congr 1
      ext n
      exact adj.unit.naturality (g.f n) }
  counit := {
    app := (NatTrans.mapHomotopyCategory adj.counit c).app
    naturality := by
      rintro ⟨K⟩ ⟨M⟩ ⟨g : K ⟶ M⟩
      simp only [HomotopyCategory.quot_mk_eq_quotient_map, NatTrans.mapHomotopyCategory_app,
        Functor.id_map, Functor.comp_map, Functor.mapHomotopyCategory_map, ← Functor.map_comp]
      congr 1
      ext n
      exact adj.counit.naturality (g.f n) }
  left_triangle_components := by
    rintro ⟨K⟩
    simp only [NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map,
      ← Functor.map_comp]
    congr 1
    ext n
    exact adj.left_triangle_components (K.X n)
  right_triangle_components := by
    rintro ⟨K⟩
    simp only [NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map,
      ← Functor.map_comp]
    congr 1
    ext n
    exact adj.right_triangle_components (K.X n)

private def homEquivOfIsos {E : Type*} [Category* E] [Preadditive E]
    {A B A' B' : E} (a : A ≅ A') (b : B ≅ B') : (A ⟶ B) ≃+ (A' ⟶ B') where
  toEquiv := Iso.homCongr a b
  map_add' := by simp [Iso.homCongr, Preadditive.add_comp, Preadditive.comp_add]

variable [HasInjectiveResolutions C]

/-- An injective-preserving left exact functor carries a resolution of an
acyclic object to an injective resolution of its image. -/
def mapInjectiveResolution (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R]
    [R.PreservesInjectiveObjects] {F : C} (I : InjectiveResolution F)
    (h : ∀ q : ℕ, IsZero ((R.rightDerived (q + 1)).obj F)) :
    InjectiveResolution (R.obj F) where
  cocomplex := (R.mapHomologicalComplex _).obj I.cocomplex
  injective n := R.injective_obj_of_injective (I.injective n)
  ι := (singleMapHomologicalComplex R (ComplexShape.up ℕ) 0).inv.app F ≫
    (R.mapHomologicalComplex _).map I.ι
  quasiIso := by
    constructor
    intro n
    cases n with
    | zero =>
      let K := (R.mapHomologicalComplex _).obj I.cocomplex
      let a : (CochainComplex.single₀ D).obj (R.obj F) ⟶ K :=
        (singleMapHomologicalComplex R (ComplexShape.up ℕ) 0).inv.app F ≫
          (R.mapHomologicalComplex _).map I.ι
      have eq : (singleObjCyclesSelfIso (ComplexShape.up ℕ) 0 (R.obj F)).inv ≫
          cyclesMap a 0 = I.toRightDerivedZero' R := by
        rw [← cancel_mono (K.iCycles 0), Category.assoc, cyclesMap_i,
          singleObjCyclesSelfIso_inv_iCycles_assoc, I.toRightDerivedZero'_comp_iCycles]
        simp only [a, comp_f, singleMapHomologicalComplex_inv_app_self,
          Functor.mapHomologicalComplex_map_f, Iso.inv_hom_id_assoc, Category.assoc,
          ← R.map_comp]
        congr 1
        have : (singleObjXSelf (ComplexShape.up ℕ) 0 F).inv = 𝟙 F := rfl
        rw [this, Category.id_comp]
      have : IsIso (cyclesMap a 0) := by
        rw [← isIso_comp_left_iff (singleObjCyclesSelfIso (ComplexShape.up ℕ) 0 (R.obj F)).inv,
          eq]
        infer_instance
      change QuasiIsoAt a 0
      rw [quasiIsoAt_iff_isIso_homologyMap]
      rw [← isIso_comp_left_iff (((CochainComplex.single₀ D).obj (R.obj F)).homologyπ 0),
        homologyπ_naturality]
      infer_instance
    | succ n =>
      apply (quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _)).2
      exact (exactAt_iff_isZero_homology _ _).mpr (IsZero.of_iso (h n) (I.isoRightDerivedObj R _).symm)

private abbrev natEmbedding := ComplexShape.embeddingUpNat

private instance (E : Type*) [Category* E] [Abelian E] :
    (natEmbedding.extendHomotopyFunctor E).Additive where
  map_add {K M} f g := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
    let Q := HomotopyCategory.quotient E (ComplexShape.up ℕ)
    obtain ⟨(f : K ⟶ M), rfl⟩ := Q.map_surjective f
    obtain ⟨(g : K ⟶ M), rfl⟩ := Q.map_surjective g
    rw [← Q.map_add]
    change (natEmbedding.extendFunctor E ⋙ HomotopyCategory.quotient E _).map (f + g) = _
    rw [Functor.map_add]
    rfl

private def mapHomEquiv {E E' : Type*} [Category* E] [Category* E']
    [Preadditive E] [Preadditive E'] (G : E ⥤ E') [G.Additive] {A B : E}
    (h : Function.Bijective (G.map : (A ⟶ B) → _)) :
    (A ⟶ B) ≃+ (G.obj A ⟶ G.obj B) :=
  AddEquiv.ofBijective G.mapAddHom h

/-- Ext computed by homotopy classes into the extension of an injective
resolution to a cochain complex indexed by the integers. -/
def extViaExtendedResolution {E : Type*} [Category* E] [Abelian E] [HasExt.{w} E]
    {F : E} (I : InjectiveResolution F) (P : E) (q : ℕ) :
    Ext P F q ≃+ ((HomotopyCategory.quotient E _).obj ((CochainComplex.singleFunctor E 0).obj P) ⟶
      (HomotopyCategory.quotient E _).obj ((I.cocomplex.extend natEmbedding)⟦(q : ℤ)⟧)) := by
  letI := HasDerivedCategory.standard E
  let Q := HomotopyCategory.quotient E (ComplexShape.up ℤ)
  let J := I.cocomplex.extend natEmbedding
  let K := (CochainComplex.singleFunctor E 0).obj P
  let a := (extendSingleIso natEmbedding F 0 0 rfl).inv ≫ extendMap I.ι natEmbedding
  have : QuasiIso a := by
    have : QuasiIso (extendMap I.ι natEmbedding) := (quasiIso_extendMap_iff _ _).mpr inferInstance
    dsimp only [a]
    infer_instance
  have : IsIso (DerivedCategory.Q.map a) := (DerivedCategory.isIso_Q_map_iff_quasiIso E a).mpr inferInstance
  let shiftD := shiftFunctor (DerivedCategory E) (q : ℤ)
  let eP := (DerivedCategory.singleFunctorIsoCompQ E 0).app P ≪≫
    (DerivedCategory.quotientCompQhIso E).symm.app K
  let eF := (DerivedCategory.singleFunctorIsoCompQ E 0).app F ≪≫
    asIso (DerivedCategory.Q.map a) ≪≫ (DerivedCategory.quotientCompQhIso E).symm.app J
  let eShift := (DerivedCategory.Qh.commShiftIso (q : ℤ)).app (Q.obj J)
  let eQ := (Q.commShiftIso (q : ℤ)).app J
  let e₁ : Ext P F q ≃+ _ := Ext.homAddEquiv.trans
    (homEquivOfIsos eP (shiftD.mapIso eF ≪≫ eShift.symm ≪≫ DerivedCategory.Qh.mapIso eQ.symm))
  have : CochainComplex.IsKInjective (J⟦(q : ℤ)⟧) :=
    (CochainComplex.isKInjective_shift_iff J _).mpr inferInstance
  let e₂ := mapHomEquiv DerivedCategory.Qh
    (A := Q.obj K) (B := Q.obj (J⟦(q : ℤ)⟧)) (CochainComplex.IsKInjective.Qh_map_bijective _ _)
  exact e₁.trans e₂.symm

private def extViaResolution {E : Type*} [Category* E] [Abelian E] [HasExt.{w} E]
    {F : E} (I : InjectiveResolution F) (P : E) (q : ℕ) :
    Ext P F q ≃+ ((HomotopyCategory.quotient E _).obj ((single E (ComplexShape.up ℕ) q).obj P) ⟶
      (HomotopyCategory.quotient E _).obj I.cocomplex) := by
  let Q := HomotopyCategory.quotient E (ComplexShape.up ℤ)
  let J := I.cocomplex.extend natEmbedding
  let K := (CochainComplex.singleFunctor E 0).obj P
  let shiftH := shiftFunctor (HomotopyCategory E (ComplexShape.up ℤ)) (q : ℤ)
  let eq := (HomotopyCategory.singleFunctors E).shiftIso (q : ℤ) 0 (q : ℤ) (add_zero _)
  let eSingle := Q.mapIso (extendSingleIso natEmbedding P q (q : ℤ) rfl)
  let eSource := shiftH.mapIso eSingle ≪≫ eq.app P
  let e₃ := homEquivOfIsos (Iso.refl (Q.obj K)) ((Q.commShiftIso (q : ℤ)).app J)
  let extend := natEmbedding.extendHomotopyFunctor E
  let e₄ := mapHomEquiv extend
    (A := (HomotopyCategory.quotient E _).obj ((single E (ComplexShape.up ℕ) q).obj P))
    (B := (HomotopyCategory.quotient E _).obj I.cocomplex)
    ⟨extend.map_injective, extend.map_surjective⟩
  let e₅ := mapHomEquiv shiftH
    (A := Q.obj (((single E (ComplexShape.up ℕ) q).obj P).extend natEmbedding))
    (B := Q.obj J) ⟨shiftH.map_injective, shiftH.map_surjective⟩
  exact (extViaExtendedResolution I P q).trans (e₃.trans
    ((homEquivOfIsos eSource.symm (Iso.refl _)).trans (e₅.symm.trans e₄.symm)))

/-- The Ext adjunction at an acyclic value of an injective-preserving right adjoint. -/
def extEquivOfAcyclic [HasExt.{w} C] [HasExt.{w'} D]
    {L : D ⥤ C} {R : C ⥤ D} [L.Additive] [R.Additive] [PreservesFiniteLimits R]
    [R.PreservesInjectiveObjects] (adj : L ⊣ R) {F : C}
    (h : ∀ q : ℕ, IsZero ((R.rightDerived (q + 1)).obj F)) (P : D) (q : ℕ) :
    Ext P (R.obj F) q ≃+ Ext (L.obj P) F q := by
  let I := injectiveResolution F
  let J := mapInjectiveResolution R I h
  let Q := HomotopyCategory.quotient C (ComplexShape.up ℕ)
  let s := (singleMapHomologicalComplex L (ComplexShape.up ℕ) q).app P
  exact (extViaResolution J P q).trans
    (((homotopyAdjunction adj _).homAddEquiv _ (Q.obj I.cocomplex)).symm.trans
      ((homEquivOfIsos (Q.mapIso s) (Iso.refl _)).trans (extViaResolution I (L.obj P) q).symm))

end PhilipponDerivedAdjunction

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits HomologicalComplex Opposite


namespace PhilipponDerivedHom

universe u v u' v' w

private abbrev e := ComplexShape.embeddingUpNat

section Extend

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  (G : C ⥤ D) [G.Additive] (I : CochainComplex C ℕ)

private abbrev mapped := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I

private def extendComponent (j : ℤ) :
    ((mapped G I).extend e).X j ≅ G.obj ((I.extend e).X j) := by
  classical
  by_cases h : ∃ n, e.f n = j
  · exact (mapped G I).extendXIso e h.choose_spec ≪≫ G.mapIso (I.extendXIso e h.choose_spec).symm
  · exact ((mapped G I).isZero_extend_X e j (fun n hn => h ⟨n, hn⟩)).iso
      (G.map_isZero (I.isZero_extend_X e j (fun n hn => h ⟨n, hn⟩)))

private theorem extendComponent_at {n : ℕ} {j : ℤ} (h : e.f n = j) :
    extendComponent G I j =
      (mapped G I).extendXIso e h ≪≫ G.mapIso (I.extendXIso e h).symm := by
  classical
  let r : ∃ m, e.f m = j := ⟨n, h⟩
  unfold extendComponent
  rw [dif_pos r]
  have uniqueIso (m : ℕ) (hm : e.f m = j) (hn : m = n) :
      (mapped G I).extendXIso e hm ≪≫ G.mapIso (I.extendXIso e hm).symm =
        (mapped G I).extendXIso e h ≪≫ G.mapIso (I.extendXIso e h).symm := by
    subst m
    rfl
  exact uniqueIso r.choose r.choose_spec (e.injective_f (r.choose_spec.trans h.symm))

/-- An additive functor commutes with extending a cochain complex by zero
from nonnegative to integer degrees. -/
def mapExtendIso : ((mapped G I).extend e) ≅ (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I.extend e) := by
  refine Hom.isoOfComponents (extendComponent G I) ?_
  intro j k _
  by_cases hj : ∃ n, e.f n = j
  · by_cases hk : ∃ n, e.f n = k
    · obtain ⟨n, hn⟩ := hj
      obtain ⟨m, hm⟩ := hk
      change (extendComponent G I j).hom ≫ G.map ((I.extend e).d j k) =
        ((mapped G I).extend e).d j k ≫ (extendComponent G I k).hom
      rw [extendComponent_at G I hn, extendComponent_at G I hm,
        extend_d_eq _ e hn hm, extend_d_eq _ e hn hm]
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp,
        Functor.mapHomologicalComplex_obj_d, Category.assoc, Iso.inv_hom_id_assoc]
      rw [← G.map_comp_assoc (I.extendXIso e hn).inv (I.extendXIso e hn).hom,
        Iso.inv_hom_id, G.map_id, Category.id_comp]
    · exact (G.map_isZero (I.isZero_extend_X e k (fun n hn => hk ⟨n, hn⟩))).eq_of_tgt _ _
  · exact ((mapped G I).isZero_extend_X e j (fun n hn => hj ⟨n, hn⟩)).eq_of_src _ _

end Extend

section Coyoneda

variable {C : Type u} [Category.{v} C] [Abelian C] (P : C)

private abbrev homFunctor := preadditiveCoyoneda.obj (op P)

private def homComplexIso (K : CochainComplex C ℤ) :
    ((homFunctor P).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ≅
      CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj P) K := by
  refine Hom.isoOfComponents (fun j => (CochainComplex.HomComplex.Cochain.fromSingleEquiv
    (X := P) (K := K) (p := 0) (zero_add j)).symm.toAddCommGrpIso) ?_
  intro j k _
  apply ConcreteCategory.hom_ext
  intro f
  change CochainComplex.HomComplex.δ j k
      (CochainComplex.HomComplex.Cochain.fromSingleMk f (zero_add j)) =
    CochainComplex.HomComplex.Cochain.fromSingleMk (f ≫ K.d j k) (zero_add k)
  exact CochainComplex.HomComplex.Cochain.δ_fromSingleMk f (zero_add j) _ _ (zero_add k)

/-- Compute Ext as the homology of the complex obtained by applying
`Hom(P, -)` to an injective resolution. -/
def extEquivHomology [HasExt.{w} C] {F : C} (I : InjectiveResolution F) (q : ℕ) :
    Ext P F q ≃+ (((homFunctor P).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homology q := by
  let J := I.cocomplex.extend e
  let K := (CochainComplex.singleFunctor C 0).obj P
  let G := homFunctor P
  let M := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let h := homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) (q : ℤ)
  let e₁ := PhilipponDerivedAdjunction.extViaExtendedResolution I P q
  let e₂ := (CochainComplex.HomComplex.CohomologyClass.homAddEquiv (K := K) (L := J) (n := (q : ℤ))).symm
  let e₃ := (CochainComplex.HomComplex.homologyAddEquiv K J (q : ℤ)).symm
  let e₄ := h.mapIso ((mapExtendIso G I.cocomplex ≪≫ homComplexIso P J).symm)
  let e₅ := M.extendHomologyIso e (j := q) (j' := (q : ℤ)) rfl
  exact e₁.trans (e₂.trans (e₃.trans
    ((e₄ ≪≫ e₅).addCommGroupIsoToAddEquiv)))

end Coyoneda

end PhilipponDerivedHom

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections)


namespace PhilipponEtaleDerivedSections

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

local instance (X : Scheme.{u}) : (globalSections X).Additive where
  map_add := rfl

private abbrev constants (X : Scheme.{u}) : Ab X :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))

private abbrev liftSections := AddCommGrpCat.uliftFunctor.{u + 1, u}

private def sectionsCoyonedaIso (X : Scheme.{u}) :
    preadditiveCoyoneda.obj (op (constants X)) ≅ globalSections X ⋙ liftSections.{u} := by
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let hT : IsTerminal T := IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal
  let adj := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT
  let e (F : Ab X) : (constants X ⟶ F) ≃+ (globalSections X).obj F :=
    (adj.homAddEquiv _ F).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _)
  refine NatIso.ofComponents (fun F => ((e F).trans AddEquiv.ulift.symm).toAddCommGrpIso) ?_
  intro F G a
  apply ConcreteCategory.hom_ext
  intro h
  change ULift.up (e G (h ≫ a)) = ULift.up ((globalSections X).map a (e F h))
  congr 1

/-- Étale cohomology can be computed as the homology of global sections of
any injective resolution, using the Ext definition of `Sheaf.H`. -/
def cohomologyEquivResolution {X : Scheme.{u}} (F : Ab X) (I : InjectiveResolution F) (n : ℕ) :
    F.H n ≃+ (((globalSections X).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homology n := by
  let Γ := globalSections X
  let K := (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let e₁ := PhilipponDerivedHom.extEquivHomology (constants X) I n
  let e₂ := (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) n).mapIso
    ((Functor.mapHomologicalComplexCompIso (sectionsCoyonedaIso X).symm (ComplexShape.up ℕ)).symm.app
      I.cocomplex)
  let e₃ := (K.sc n).mapHomologyIso liftSections
  exact e₁.trans ((e₂ ≪≫ e₃).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)

/-- The Ext definition of étale cohomology agrees with the right derived
functor of global sections. -/
def cohomologyEquivRightDerived {X : Scheme.{u}} (F : Ab X) (n : ℕ) :
    F.H n ≃+ (((globalSections X).rightDerived n).obj F) :=
  let I := injectiveResolution F
  (cohomologyEquivResolution F I n).trans
    (I.isoRightDerivedObj (globalSections X) n).symm.addCommGroupIsoToAddEquiv

end PhilipponEtaleDerivedSections

end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

theorem solution
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    let Γ := (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (op (Scheme.Etale.mk (𝟙 X)))
    letI : Γ.Additive := ⟨by intros; rfl⟩
    Nonempty (F.H n ≃+ ((Γ.rightDerived n).obj F)) := by
  exact ⟨PhilipponEtaleDerivedSections.cohomologyEquivRightDerived F n⟩


end
