-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_etale_geometric_fiber_comparison_of_projective_projection
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T01:14:37.254106+00:00
-- url     : https://prove2.me/submissions/7e9b2eee-4b29-47cd-a602-1e1e86fe5e4a

import Definitions.Def_AlgebraicGeometry_EtaleStrictLocalSectionGerms
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_Scheme_isIso_etale_globalSections_restrict_closed_fiber_of_strictly_henselian
import Theorems.Thm_AlgebraicGeometry_Scheme_isIso_etale_restrictGlobalSections_of_separably_closed_field_extension

set_option maxHeartbeats 1400000

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeMap (pushforwardCompIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDirectImageGerms
open PhilipponEtalePullbackComposition (pullbackCompIso unit_comp)
open PhilipponEtalePullbackSquareUnits
  (restrictionBaseChangeOver)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStalkPullback (stalkPullbackIso)


namespace PhilipponEtaleBaseChangeGerms

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

variable {K : Type u} [Field K] [IsSepClosed K]

private abbrev stalk {X : Scheme.{u}} (s : Spec (.of K) ⟶ X) :=
  (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})

@[reassoc]
theorem evalAtLiftOver_naturality {X Y : Scheme.{u}} (p : Y ⟶ X) (v : Spec (.of K) ⟶ Y)
    (s : Spec (.of K) ⟶ X) (h : v ≫ p = s) {F G : Ab Y} (a : F ⟶ G) :
    (stalk s).map ((pushforward p).map a) ≫ evalAtLiftOver p v s h G =
      evalAtLiftOver p v s h F ≫ (stalk v).map a := by
  subst s
  simpa only [evalAtLiftOver, eqToHom_refl, Category.id_comp] using evalAtLift_naturality p v a

set_option maxHeartbeats 900000 in
/-- The inverse-image comparison for a composite gives the successive
inverse-image comparisons on stalks. -/
theorem stalkPullbackIso_hom_comp {X Y Z : Scheme.{u}} (p : Y ⟶ X) (d : Z ⟶ Y)
    (v : Spec (.of K) ⟶ Z) (F : Ab X) :
    (stalk v).map ((pullbackCompIso p d).hom.app F) ≫
      (stalkPullbackIso (d ≫ p) v).hom.app F ≫
      eqToHom (congrArg (fun x => (stalk x).obj F) (Category.assoc v d p).symm) =
    (stalkPullbackIso d v).hom.app ((pullbackSheaves p).obj F) ≫
      (stalkPullbackIso p (v ≫ d)).hom.app F := by
  let s := (v ≫ d) ≫ p
  let t := v ≫ d
  let A := (pullbackSheaves p).obj F
  let B := (pullbackSheaves d).obj A
  let H := (pullbackSheaves (d ≫ p)).obj F
  let ηp := (pullbackAdjunction p).unit.app F
  let ηd := (pullbackAdjunction d).unit.app A
  let e := stalkPullbackIso p t
  let e' := stalkPullbackIso d v
  let β := (pullbackCompIso p d).hom.app F
  let hs : v ≫ (d ≫ p) = s := (Category.assoc v d p).symm
  let l := (stalkPullbackIso (d ≫ p) v).hom.app F ≫
    eqToHom (congrArg (fun x => (stalk x).obj F) hs)
  have h₁ : (stalk s).map ηp ≫ evalAtLift p t A = e.inv.app F := by
    apply (cancel_mono (e.hom.app F)).mp
    simp only [Category.assoc]
    exact (evalAtLift_unit p t F).trans (Iso.inv_hom_id_app e F).symm
  have h₂ : (stalk t).map ηd ≫ evalAtLift d v B = e'.inv.app A := by
    apply (cancel_mono (e'.hom.app A)).mp
    simp only [Category.assoc]
    exact (evalAtLift_unit d v A).trans (Iso.inv_hom_id_app e' A).symm
  have hc := evalAtLiftOver_comp p d v s rfl B
  simp only [evalAtLiftOver, eqToHom_refl, Category.id_comp] at hc
  have hc' : (stalk s).map ((pushforwardCompIso p d).hom.app B) ≫
      evalAtLiftOver (d ≫ p) v s hs B =
      evalAtLift p t ((pushforward d).obj B) ≫ evalAtLift d v B := hc
  change (stalk v).map β ≫ l = e'.hom.app A ≫ e.hom.app F
  apply (cancel_epi (e.inv.app F ≫ e'.inv.app A)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  calc
    _ = (stalk s).map ηp ≫ evalAtLift p t A ≫ (stalk t).map ηd ≫ evalAtLift d v B ≫
        (stalk v).map β ≫ l := by simp only [← reassoc_of% h₁, ← reassoc_of% h₂]
    _ = (stalk s).map (ηp ≫ (pushforward p).map ηd ≫ (pushforwardCompIso p d).hom.app B ≫
          (pushforward (d ≫ p)).map β) ≫ evalAtLiftOver (d ≫ p) v s hs H ≫ l := by
      simp only [Functor.map_comp, Category.assoc]
      have hNat : (stalk s).map ((pushforward (d ≫ p)).map β) ≫ evalAtLiftOver (d ≫ p) v s hs H =
          evalAtLiftOver (d ≫ p) v s hs B ≫ (stalk v).map β :=
        evalAtLiftOver_naturality (d ≫ p) v s hs β
      have hNat' : (stalk s).map ((pushforward p).map ηd) ≫ evalAtLift p t ((pushforward d).obj B) =
          evalAtLift p t A ≫ (stalk t).map ηd := evalAtLift_naturality p t ηd
      rw [reassoc_of% hNat, reassoc_of% hc', reassoc_of% hNat']
    _ = _ := by
      rw [show ηp ≫ (pushforward p).map ηd ≫ (pushforwardCompIso p d).hom.app B ≫
          (pushforward (d ≫ p)).map β = (pullbackAdjunction (d ≫ p)).unit.app F from unit_comp p d F]
      exact evalAtLiftOver_unit (d ≫ p) v s hs F

end PhilipponEtaleBaseChangeGerms

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDirectImageGerms (evalAtLift evalAtLiftOver)
open PhilipponEtaleGeometricStalks (algebraicallyClosedGeometricMap algebraicallyClosedGeometricPoints_conservative)
open PhilipponEtalePullbackComposition (pullbackCompIso)
open PhilipponEtalePullbackSquareUnits (restrictionBaseChangeOver)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleStalkPullback (stalkPullbackIso)
open PhilipponStrictHenselianEtaleCohomology (terminalGerm)


namespace PhilipponEtaleGeometricBaseChangeReduction

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private abbrev stalk {K : Type u} [Field K] [IsSepClosed K] {X : Scheme.{u}}
    (s : Spec (.of K) ⟶ X) := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})

/-- A stalk-to-geometric-fiber comparison compatible with evaluation at
every rational point of the fiber. -/
def HasFiberComparisons {X Y : Scheme.{u}} (i : Y ⟶ X) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ X)
    {T : Scheme.{u}} (j : T ⟶ Spec (.of K)) (a : T ⟶ Y) (h : IsPullback j a s i) (F : Ab Y),
    ∃ e : (stalk s).obj ((pushforward i).obj F) ≅ (globalSections T).obj ((pullbackSheaves a).obj F),
      ∀ (v : Spec (.of K) ⟶ T) (hv : v ≫ j = 𝟙 _),
        e.hom ≫ (terminalGerm v).app ((pullbackSheaves a).obj F) ≫ (stalkPullbackIso a v).hom.app F =
          evalAtLiftOver i (v ≫ a) s (by rw [Category.assoc, ← h.w, ← Category.assoc, hv, Category.id_comp]) F

end PhilipponEtaleGeometricBaseChangeReduction

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleBaseChangeGerms (stalkPullbackIso_hom_comp)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDirectImageGerms (evalAtLiftOver)
open PhilipponEtaleHenselianStalk (residueEmbedding)
open PhilipponEtaleLocalRing (evaluateGerm stalkRing)
open PhilipponEtalePullbackComposition (pullbackCompIso restrictGlobalSections_comp)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleSectionFiniteRefinement (restrictGlobalSections_germ)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleStalkPullback (stalkPullbackIso)
open PhilipponEtaleStrictHenselization (toBase closedPointInclusion evaluation_comp_toBase)
open PhilipponStrictHenselianEtaleCohomology (terminalGerm)
open PhilipponStrictLocalPresheaf
  (stalkDirectImageIsoStrictLocalSections germ_of_stalkDirectImageIsoStrictLocalSections)


namespace PhilipponEtaleStrictLocalGeometricComparison

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
  (s : Spec (.of K) ⟶ X) (f : Y ⟶ X) [IsProper f]

private abbrev Local := pullback (toBase s) f
private abbrev π : Local s f ⟶ Y := pullback.snd _ _

private abbrev stalk {Z : Scheme.{u}} (q : Spec (.of K) ⟶ Z) :=
  (Scheme.pointSmallEtale q).sheafFiber (A := AddCommGrpCat.{u})

set_option maxHeartbeats 1400000 in
/-- Restricting the strict-local sections to a geometric fiber, when that
restriction is invertible, gives the comparison compatible with germs. -/
theorem exists_comparison_of_isIso_strictLocalRestriction {T : Scheme.{u}}
    (j : T ⟶ Spec (.of K)) (d : T ⟶ Y) (h : IsPullback j d s f)
    (l : T ⟶ Local s f) (hj : l ≫ pullback.fst (toBase s) f = j ≫ Spec.map (evaluateGerm s))
    (hd : l ≫ π s f = d) (F : Ab Y)
    (hIso : IsIso ((restrictGlobalSections l).app ((pullbackSheaves (π s f)).obj F))) :
    ∃ e : (stalk s).obj ((pushforward f).obj F) ≅ (globalSections T).obj ((pullbackSheaves d).obj F),
      ∀ (v : Spec (.of K) ⟶ T) (hv : v ≫ j = 𝟙 _),
        e.hom ≫ (terminalGerm v).app ((pullbackSheaves d).obj F) ≫ (stalkPullbackIso d v).hom.app F =
          evalAtLiftOver f (v ≫ d) s (by rw [Category.assoc, ← h.w, ← Category.assoc, hv, Category.id_comp]) F := by
  subst d
  let p := π s f
  let A := (pullbackSheaves p).obj F
  let B := (pullbackSheaves (l ≫ p)).obj F
  let e₀ := stalkDirectImageIsoStrictLocalSections s f F
  let e₁ := asIso ((restrictGlobalSections l).app A)
  let β := (pullbackCompIso p l).app F
  let e₂ := (globalSections T).mapIso β
  refine ⟨e₀ ≪≫ e₁ ≪≫ e₂, fun v hv => ?_⟩
  have hLift : (v ≫ l) ≫ pullback.fst (toBase s) f = Spec.map (evaluateGerm s) := by
    rw [Category.assoc, hj, ← Category.assoc, hv, Category.id_comp]
  have hc : ((v ≫ l) ≫ p) ≫ f = s := by
    rw [Category.assoc v l p, Category.assoc, ← h.w, ← Category.assoc, hv, Category.id_comp]
  have hd' : (v ≫ (l ≫ p)) ≫ f = s := by rw [← Category.assoc, hc]
  let τ : (stalk (v ≫ (l ≫ p))).obj F ⟶ (stalk ((v ≫ l) ≫ p)).obj F :=
    eqToHom (congrArg (fun z => (stalk z).obj F) (Category.assoc v l p).symm)
  apply (cancel_mono τ).mp
  have hGerm : evalAtLiftOver f (v ≫ (l ≫ p)) s hd' F ≫ τ =
      evalAtLiftOver f ((v ≫ l) ≫ p) s hc F := by
    have hTransport (v₁ v₂ : Spec (.of K) ⟶ Y) (w : v₁ = v₂)
        (h₁ : v₁ ≫ f = s) (h₂ : v₂ ≫ f = s) :
        evalAtLiftOver f v₁ s h₁ F ≫ eqToHom (congrArg (fun z => (stalk z).obj F) w) =
          evalAtLiftOver f v₂ s h₂ F := by
      subst v₂
      simp only [eqToHom_refl, Category.comp_id]
    exact hTransport _ _ (Category.assoc v l p).symm hd' hc
  rw [hGerm]
  have hNat : (globalSections T).map β.hom ≫ (terminalGerm v).app B =
      (terminalGerm v).app ((pullbackSheaves l).obj A) ≫ (stalk v).map β.hom :=
    (terminalGerm v).naturality β.hom
  change (e₀.hom ≫ (restrictGlobalSections l).app A ≫ (globalSections T).map β.hom) ≫
    ((terminalGerm v).app B ≫ (stalkPullbackIso (l ≫ p) v).hom.app F) ≫ τ = _
  simp only [Category.assoc]
  rw [reassoc_of% hNat]
  have hComp : (stalk v).map β.hom ≫ (stalkPullbackIso (l ≫ p) v).hom.app F ≫ τ =
      (stalkPullbackIso l v).hom.app A ≫ (stalkPullbackIso p (v ≫ l)).hom.app F :=
    stalkPullbackIso_hom_comp p l v F
  rw [hComp]
  have hr : (restrictGlobalSections l).app A ≫ (terminalGerm v).app ((pullbackSheaves l).obj A) ≫
      (stalkPullbackIso l v).hom.app A = (terminalGerm (v ≫ l)).app A :=
    restrictGlobalSections_germ l v A
  rw [reassoc_of% hr]
  exact germ_of_stalkDirectImageIsoStrictLocalSections s f (v ≫ l) hLift hc F

set_option maxHeartbeats 1400000 in
/-- The strict-local comparison is invertible if restriction to the closed
fiber and then extension of its separably closed residue field are invertible. -/
theorem hasFiberComparisons_of_restrictions
    (hClosed : ∀ (R : Type u) [CommRing R] [HenselianLocalRing R]
      [IsSepClosed (IsLocalRing.ResidueField R)] {Z : Scheme.{u}}
      (g : Z ⟶ Spec (.of R)) [IsProper g] (F : Ab Z),
      IsIso ((restrictGlobalSections (pullback.snd
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) g)).app F))
    (hField : ∀ (L E : Type u) [Field L] [IsSepClosed L] [Field E] [IsAlgClosed E]
      (g : L →+* E) {Z B : Scheme.{u}} (p : Z ⟶ Spec (.of L)) [IsProper p]
      (j : B ⟶ Spec (.of E)) (a : B ⟶ Z) (_h : IsPullback j a (Spec.map (CommRingCat.ofHom g)) p)
      (F : Ab Z), IsIso ((restrictGlobalSections a).app F)) :
    PhilipponEtaleGeometricBaseChangeReduction.HasFiberComparisons f := by
  intro E _ _ x T j d h F
  let m := pullback.fst (toBase x) f
  let p := π x f
  let z := Spec.map (evaluateGerm x)
  let : IsProper m := inferInstanceAs (IsProper (pullback.fst (toBase x) f))
  let l := pullback.lift (j ≫ z) d (by rw [Category.assoc, evaluation_comp_toBase, h.w])
  have hlj : l ≫ m = j ≫ z := pullback.lift_fst _ _ _
  have hld : l ≫ p = d := pullback.lift_snd _ _ _
  have hl : IsPullback j l z m := by
    apply IsPullback.of_bot ?_ hlj.symm (IsPullback.of_hasPullback (toBase x) f)
    rw [hld, evaluation_comp_toBase]
    exact h
  let k := IsLocalRing.ResidueField (stalkRing x)
  let g := Spec.map (CommRingCat.ofHom (residueEmbedding x))
  let c := closedPointInclusion x
  let q := pullback.snd c m
  let a := pullback.fst c m
  let : IsProper a := inferInstanceAs (IsProper (pullback.fst c m))
  have hzc : g ≫ c = z := by
    change Spec.map (CommRingCat.ofHom (residueEmbedding x)) ≫ closedPointInclusion x =
      Spec.map (evaluateGerm x)
    rw [closedPointInclusion, ← Spec.map_comp]
    congr 1
  let v := pullback.lift (j ≫ g) l (by rw [Category.assoc, hzc, hlj])
  have hvj : v ≫ a = j ≫ g := pullback.lift_fst _ _ _
  have hvq : v ≫ q = l := pullback.lift_snd _ _ _
  have hv : IsPullback j v g a := by
    apply IsPullback.of_bot ?_ hvj.symm (IsPullback.of_hasPullback c m)
    rw [hvq, hzc]
    exact hl
  let A := (pullbackSheaves p).obj F
  let : IsIso ((restrictGlobalSections q).app A) := hClosed (stalkRing x) m A
  let : IsIso ((restrictGlobalSections v).app ((pullbackSheaves q).obj A)) :=
    hField k E (residueEmbedding x) a j v hv ((pullbackSheaves q).obj A)
  have hIso : IsIso ((restrictGlobalSections l).app A) := by
    rw [← hvq, ← restrictGlobalSections_comp q v A]
    infer_instance
  exact exists_comparison_of_isIso_strictLocalRestriction x f j d h l hlj hld F hIso

end PhilipponEtaleStrictLocalGeometricComparison

end

open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDirectImageGerms (evalAtLiftOver)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleStalkPullback (stalkPullbackIso)
open PhilipponStrictHenselianEtaleCohomology (terminalGerm)
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (R : Type u) [CommRing R] (n : ℕ) {P S : Scheme.{u}}
    (v : S ⟶ Spec (.of R))
    (a : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) (r : P ⟶ S)
    (h : IsPullback a r (ProjSpace.π R n) v) :
    ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S)
      {T : Scheme.{u}} (j : T ⟶ Spec (.of K)) (d : T ⟶ P) (h' : IsPullback j d s r)
      (F : Sheaf P.smallEtaleTopology AddCommGrpCat.{u}),
      ∃ e : (Scheme.pointSmallEtale s).sheafFiber.obj ((pushforward r).obj F) ≅
          (globalSections T).obj ((pullbackSheaves d).obj F),
        ∀ (w : Spec (.of K) ⟶ T) (hw : w ≫ j = 𝟙 _),
          e.hom ≫ (terminalGerm w).app ((pullbackSheaves d).obj F) ≫ (stalkPullbackIso d w).hom.app F =
            evalAtLiftOver r (w ≫ d) s
              (by rw [Category.assoc, ← h'.w, ← Category.assoc, hw, Category.id_comp]) F := by
  let : IsProper r := MorphismProperty.of_isPullback h (inferInstance : IsProper (ProjSpace.π R n))
  exact PhilipponEtaleStrictLocalGeometricComparison.hasFiberComparisons_of_restrictions r
    (fun R _ _ _ Z g _ F => by
      rw [PhilipponEtalePullbackComposition.restrictGlobalSections_app_eq]
      let : IsIso ((PhilipponEtaleAcyclicCohomology.globalSections Z).map
          ((PhilipponEtaleSmallSite.pullbackAdjunction (pullback.snd
            (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) g)).unit.app F)) :=
        AlgebraicGeometry.Scheme.isIso_etale_globalSections_restrict_closed_fiber_of_strictly_henselian R g F
      infer_instance)
    (fun L E _ _ _ _ g Z B p _ j a h F => AlgebraicGeometry.Scheme.isIso_etale_restrictGlobalSections_of_separably_closed_field_extension L E g p j a h F)


end
