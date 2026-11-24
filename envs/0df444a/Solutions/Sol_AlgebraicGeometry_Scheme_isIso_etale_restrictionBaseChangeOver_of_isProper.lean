-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.isIso_etale_restrictionBaseChangeOver_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T05:13:47.98646+00:00
-- url     : https://prove2.me/submissions/0e6f09ad-923f-471c-88eb-e155058312bc

import Definitions.Def_AlgebraicGeometry_EtaleStrictLocalSectionGerms
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_AlgebraicGeometry_Scheme_isIso_etale_globalSections_restrict_closed_fiber_of_strictly_henselian
import Theorems.Thm_AlgebraicGeometry_Scheme_isIso_etale_restrictGlobalSections_of_separably_closed_field_extension

set_option maxHeartbeats 1600000

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

set_option maxHeartbeats 900000 in
/-- Transposing the ordinary base-change map gives the pushed-forward
unit, after identifying the two direct images along the common map. -/
private theorem unit_restrictionBaseChangeOver {X P Z W : Scheme.{u}}
    (p : P ⟶ X) (i : Z ⟶ X) (j : W ⟶ P) (r : W ⟶ Z)
    (ρ : W ⟶ X) (hp : j ≫ p = ρ) (hi : r ≫ i = ρ) (B : Ab Z) :
    (pullbackAdjunction p).unit.app ((pushforward i).obj B) ≫
      (pushforward p).map (restrictionBaseChangeOver p i j r ρ hp hi B) ≫
      (pushforwardCompIso p j ≪≫ eqToIso (congrArg pushforward hp)).hom.app
        ((pullbackSheaves r).obj B) =
    (pushforward i).map ((pullbackAdjunction r).unit.app B) ≫
      (pushforwardCompIso i r ≪≫ eqToIso (congrArg pushforward hi)).hom.app
        ((pullbackSheaves r).obj B) := by
  let adj := pullbackAdjunction p
  let C := restrictionBaseChangeOver p i j r ρ hp hi B
  let P := pullbackSheaves r
  let e := pushforwardCompIso p j ≪≫ eqToIso (congrArg pushforward hp)
  let f := pushforwardCompIso i r ≪≫ eqToIso (congrArg pushforward hi)
  have h : adj.homEquiv _ _ C =
      (pushforward i).map ((pullbackAdjunction r).unit.app B) ≫
        (f ≪≫ e.symm).hom.app (P.obj B) := Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_unit] at h
  change adj.unit.app _ ≫ (pushforward p).map C ≫ e.hom.app (P.obj B) = _
  rw [← Category.assoc, h]
  simp only [P, f, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]

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

@[reassoc]
theorem evalAtLiftOver_comp_via {X Y Z : Scheme.{u}} (p : Y ⟶ X) (d : Z ⟶ Y)
    (ρ : Z ⟶ X) (hp : d ≫ p = ρ) (v : Spec (.of K) ⟶ Z)
    (s : Spec (.of K) ⟶ X) (h : v ≫ ρ = s) (F : Ab Z) :
    (stalk s).map ((pushforwardCompIso p d ≪≫ eqToIso (congrArg pushforward hp)).hom.app F) ≫
      evalAtLiftOver ρ v s h F =
    evalAtLiftOver p (v ≫ d) s ((Category.assoc _ _ _).trans
      ((congrArg (v ≫ ·) hp).trans h)) ((pushforward d).obj F) ≫ evalAtLift d v F := by
  subst ρ
  simpa only [eqToIso_refl, Iso.trans_refl] using evalAtLiftOver_comp p d v s
    ((Category.assoc _ _ _).trans h) F

set_option maxHeartbeats 900000 in
/-- On geometric stalks the ordinary base-change map preserves evaluation
at a geometric lift in the commutative square. -/
theorem evalAtLift_baseChangeOver {X S Y W : Scheme.{u}}
    (p : S ⟶ X) (i : Y ⟶ X) (j : W ⟶ S) (r : W ⟶ Y)
    (ρ : W ⟶ X) (hp : j ≫ p = ρ) (hi : r ≫ i = ρ)
    (v : Spec (.of K) ⟶ W) (F : Ab Y) :
    (stalk (v ≫ j)).map (restrictionBaseChangeOver p i j r ρ hp hi F) ≫
        evalAtLift j v ((pullbackSheaves r).obj F) ≫ (stalkPullbackIso r v).hom.app F =
      (stalkPullbackIso p (v ≫ j)).hom.app ((pushforward i).obj F) ≫
        evalAtLiftOver i (v ≫ r) ((v ≫ j) ≫ p) (by simp only [Category.assoc, hi, hp]) F := by
  let t := v ≫ j
  let s := t ≫ p
  let A := (pullbackSheaves r).obj F
  let G := (pushforward i).obj F
  let H := (pushforward j).obj A
  let δ := restrictionBaseChangeOver p i j r ρ hp hi F
  let α := (pushforwardCompIso p j ≪≫ eqToIso (congrArg pushforward hp)).hom.app A
  let β := (pushforwardCompIso i r ≪≫ eqToIso (congrArg pushforward hi)).hom.app A
  let eb := stalkPullbackIso p t
  let er := stalkPullbackIso r v
  let ηp := (pullbackAdjunction p).unit.app G
  let ηr := (pullbackAdjunction r).unit.app F
  have hv : v ≫ ρ = s := by simp only [s, t, Category.assoc, hp]
  have hr : (v ≫ r) ≫ i = s := by simp only [s, t, Category.assoc, hp, hi]
  have hU : (stalk s).map ηp ≫ evalAtLift p t ((pullbackSheaves p).obj G) = eb.inv.app G := by
    apply (cancel_mono (eb.hom.app G)).mp
    simp only [Category.assoc]
    exact (evalAtLift_unit p t G).trans (Iso.inv_hom_id_app eb G).symm
  have hLeft : (stalk s).map α ≫ evalAtLiftOver ρ v s hv A =
      evalAtLift p t H ≫ evalAtLift j v A := by
    simpa only [α, evalAtLiftOver, eqToHom_refl, Category.id_comp] using
      evalAtLiftOver_comp_via p j ρ hp v s hv A
  have hRight : (stalk s).map β ≫ evalAtLiftOver ρ v s hv A =
      evalAtLiftOver i (v ≫ r) s hr ((pushforward r).obj A) ≫ evalAtLift r v A :=
    evalAtLiftOver_comp_via i r ρ hi v s hv A
  change (stalk t).map δ ≫ evalAtLift j v A ≫ er.hom.app F =
    eb.hom.app G ≫ evalAtLiftOver i (v ≫ r) s hr F
  apply (cancel_epi (eb.inv.app G)).mp
  rw [Iso.inv_hom_id_app_assoc]
  calc
    _ = (stalk s).map ηp ≫ evalAtLift p t ((pullbackSheaves p).obj G) ≫
        (stalk t).map δ ≫ evalAtLift j v A ≫ er.hom.app F := by rw [← hU, Category.assoc]
    _ = (stalk s).map (ηp ≫ (pushforward p).map δ ≫ α) ≫
        evalAtLiftOver ρ v s hv A ≫ er.hom.app F := by
      have hNat : (stalk s).map ((pushforward p).map δ) ≫ evalAtLift p t H =
          evalAtLift p t ((pullbackSheaves p).obj G) ≫ (stalk t).map δ :=
        evalAtLift_naturality p t δ
      simp only [Functor.map_comp, Category.assoc]
      rw [← reassoc_of% hNat, reassoc_of% hLeft]
    _ = (stalk s).map ((pushforward i).map ηr) ≫
        evalAtLiftOver i (v ≫ r) s hr ((pushforward r).obj A) ≫ evalAtLift r v A ≫ er.hom.app F := by
      rw [show ηp ≫ (pushforward p).map δ ≫ α = (pushforward i).map ηr ≫ β from
        unit_restrictionBaseChangeOver p i j r ρ hp hi F]
      simp only [Functor.map_comp, Category.assoc]
      rw [reassoc_of% hRight]
    _ = _ := by
      have hNat : (stalk s).map ((pushforward i).map ηr) ≫
          evalAtLiftOver i (v ≫ r) s hr ((pushforward r).obj A) =
          evalAtLiftOver i (v ≫ r) s hr F ≫ (stalk (v ≫ r)).map ηr :=
        evalAtLiftOver_naturality i (v ≫ r) s hr ηr
      rw [reassoc_of% hNat, evalAtLift_unit r v F, Category.comp_id]

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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponStrictHenselianEtaleCohomology (terminalGerm)


namespace PhilipponEtaleRationalGerms

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}

/-- A closed point of a finite-type scheme over an algebraically closed
field is represented by a point with values in that field. -/
theorem exists_rationalPoint_of_isClosed (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed {x}) :
    ∃ v : Spec (.of K) ⟶ X, v ≫ f = 𝟙 _ ∧ v default = x := by
  let q := X.fromSpecResidueField x
  let m := q ≫ f
  let : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp hx
  let : IsFinite m := (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace (f := m)).mpr inferInstance
  let φ := Spec.preimage m
  let : Algebra K (X.residueField x) := φ.hom.toAlgebra
  have hm : Spec.map φ = m := Spec.map_preimage _
  have hFinite : IsFinite (Spec.map φ) := hm ▸ (inferInstance : IsFinite m)
  let : Module.Finite K (X.residueField x) :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff φ).mp hFinite)
  have hφ : Function.Bijective φ.hom := IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e := RingEquiv.ofBijective φ.hom hφ
  let w := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  have hw : w ≫ m = 𝟙 _ := by
    rw [← hm, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    exact e.symm_apply_apply a
  refine ⟨w ≫ q, (Category.assoc _ _ _).trans hw, ?_⟩
  let z : Spec (.of K) := default
  have h : q (w z) ∈ Set.range q := ⟨w z, rfl⟩
  rw [Scheme.range_fromSpecResidueField] at h
  change (w ≫ q) z = x
  rw [Scheme.Hom.comp_apply]
  exact Set.mem_singleton_iff.mp h

/-- Global sections on a finite-type scheme over an algebraically closed
field are determined by their germs at rational points. -/
theorem globalSections_eq_of_rational_germs (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (a b : ↥((globalSections X).obj F))
    (h : ∀ (v : Spec (.of K) ⟶ X), v ≫ f = 𝟙 _ →
      (terminalGerm v).app F a = (terminalGerm v).app F b) : a = b := by
  classical
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  let T := Scheme.Etale.mk (𝟙 X)
  let S := Presheaf.equalizerSieve (F := F.obj) (X := op T) a b
  have hRefine (x : X) (hx : IsClosed {x}) :
      ∃ (V : X.Etale) (g : V ⟶ T), S g ∧ x ∈ Set.range g.left := by
    obtain ⟨v, hv, hvx⟩ := exists_rationalPoint_of_isClosed f x hx
    let t : (Scheme.pointSmallEtale v).fiber.obj T := Over.homMk v (Category.comp_id _)
    have he : (Scheme.pointSmallEtale v).toPresheafFiber T t F.obj a =
        (Scheme.pointSmallEtale v).toPresheafFiber T t F.obj b := h v hv
    obtain ⟨V, g, t', ht, he'⟩ :=
      ((Scheme.pointSmallEtale v).toPresheafFiber_eq_iff' T t a b).mp he
    have hcomp : t'.left ≫ g.left = v := congrArg Over.Hom.left ht
    let z : Spec (.of K) := default
    refine ⟨V, g, he', t'.left z, ?_⟩
    calc
      g.left (t'.left z) = (t'.left ≫ g.left) z := (Scheme.Hom.comp_apply _ _ _).symm
      _ = v z := congrArg (fun m : Spec (.of K) ⟶ X => m z) hcomp
      _ = x := hvx
  choose V g hg hmem using fun x : closedPoints X => hRefine x.val x.property
  let U : Set X := ⋃ x : closedPoints X, Set.range (g x).left
  have hU : IsOpen U := isOpen_iUnion fun x => (g x).left.isOpenMap.isOpen_range
  have hClosedPoints : closedPoints X ⊆ U := fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hmem _⟩
  have hAll : U = Set.univ := by
    have he : Uᶜ ∩ closedPoints X = ∅ := Set.eq_empty_iff_forall_notMem.mpr
      fun x hx => hx.1 (hClosedPoints hx.2)
    have hc := closure_inter_closedPoints hU.isClosed_compl
    rw [he, closure_empty] at hc
    refine Set.eq_univ_of_forall fun x => ?_
    by_contra hx
    have hx' : x ∈ Uᶜ := hx
    rw [← hc] at hx'
    exact hx'
  have hS : S ∈ X.smallEtaleTopology T :=
    X.smallEtaleTopology.superset_covering
      ((Sieve.generate_le_iff _ _).mpr (by rintro _ _ ⟨x⟩; exact hg x))
      ((Scheme.ofArrows_mem_smallEtaleTopology_iff g).mpr hAll)
  have hSheaf := Presheaf.isSheaf_comp_of_isSheaf X.smallEtaleTopology F.obj
    (CategoryTheory.forget AddCommGrpCat) F.property
  exact ((isSheaf_iff_isSheaf_of_type _ _).mp hSheaf _ hS).isSeparatedFor.ext (fun _ _ he => he)

end PhilipponEtaleRationalGerms

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleBaseChangeGerms (evalAtLift_baseChangeOver stalkPullbackIso_hom_comp)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDirectImageGerms (evalAtLift evalAtLiftOver)
open PhilipponEtaleGeometricStalks (algebraicallyClosedGeometricMap algebraicallyClosedGeometricPoints_conservative)
open PhilipponEtalePullbackComposition (pullbackCompIso)
open PhilipponEtalePullbackSquareUnits (restrictionBaseChangeOver)
open PhilipponEtaleRationalGerms (globalSections_eq_of_rational_germs)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleStalkPullback (stalkPullbackIso)
open PhilipponStrictHenselianEtaleCohomology (terminalGerm)


namespace PhilipponEtaleGeometricBaseChangeReduction

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private abbrev stalk {K : Type u} [Field K] [IsSepClosed K] {X : Scheme.{u}}
    (s : Spec (.of K) ⟶ X) := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})

private theorem evalAtLiftOver_congr_lift {K : Type u} [Field K] [IsSepClosed K] {X Y : Scheme.{u}}
    (i : Y ⟶ X) {v v' : Spec (.of K) ⟶ Y} (h : v = v') (s : Spec (.of K) ⟶ X)
    (hv : v ≫ i = s) (hv' : v' ≫ i = s) (F : Ab Y) :
    evalAtLiftOver i v s hv F ≫ eqToHom (congrArg (fun w => (stalk w).obj F) h) =
      evalAtLiftOver i v' s hv' F := by
  subst v'
  simp only [eqToHom_refl, Category.comp_id]

private theorem evalAtLift_baseChangeOver_at {K : Type u} [Field K] [IsSepClosed K]
    {X S Y W : Scheme.{u}} (p : S ⟶ X) (i : Y ⟶ X) (j : W ⟶ S) (r : W ⟶ Y)
    (h : IsPullback j r p i) (v : Spec (.of K) ⟶ W) {s : Spec (.of K) ⟶ S} (hv : v ≫ j = s)
    (F : Ab Y) :
    (stalk s).map (restrictionBaseChangeOver p i j r (j ≫ p) rfl h.w.symm F) ≫
      evalAtLiftOver j v s hv ((pullbackSheaves r).obj F) ≫ (stalkPullbackIso r v).hom.app F =
      (stalkPullbackIso p s).hom.app ((pushforward i).obj F) ≫
        evalAtLiftOver i (v ≫ r) (s ≫ p) (by rw [Category.assoc, h.w.symm, ← Category.assoc, hv]) F := by
  subst s
  simpa only [evalAtLiftOver, eqToHom_refl, Category.id_comp] using
    evalAtLift_baseChangeOver p i j r (j ≫ p) rfl h.w.symm v F

/-- A stalk-to-geometric-fiber comparison compatible with evaluation at
every rational point of the fiber. -/
def HasFiberComparisons {X Y : Scheme.{u}} (i : Y ⟶ X) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ X)
    {T : Scheme.{u}} (j : T ⟶ Spec (.of K)) (a : T ⟶ Y) (h : IsPullback j a s i) (F : Ab Y),
    ∃ e : (stalk s).obj ((pushforward i).obj F) ≅ (globalSections T).obj ((pullbackSheaves a).obj F),
      ∀ (v : Spec (.of K) ⟶ T) (hv : v ≫ j = 𝟙 _),
        e.hom ≫ (terminalGerm v).app ((pullbackSheaves a).obj F) ≫ (stalkPullbackIso a v).hom.app F =
          evalAtLiftOver i (v ≫ a) s (by rw [Category.assoc, ← h.w, ← Category.assoc, hv, Category.id_comp]) F

set_option maxHeartbeats 1400000 in
/-- Geometric-fiber comparisons for the vertical maps give the ordinary
étale base-change isomorphism for a Cartesian square. -/
theorem isIso_restrictionBaseChangeOver {X S Y W : Scheme.{u}}
    (p : S ⟶ X) (i : Y ⟶ X) (j : W ⟶ S) (r : W ⟶ Y) (hp : IsPullback j r p i)
    [LocallyOfFiniteType j] (hi : HasFiberComparisons i) (hj : HasFiberComparisons j) (F : Ab Y) :
    IsIso (restrictionBaseChangeOver p i j r (j ≫ p) rfl hp.w.symm F) := by
  let δ := restrictionBaseChangeOver p i j r (j ≫ p) rfl hp.w.symm F
  let G := (pushforward i).obj F
  let A := (pullbackSheaves r).obj F
  let Q := ObjectProperty.ofObj fun x : S => Scheme.pointSmallEtale (algebraicallyClosedGeometricMap x)
  have hQ : Q.IsConservativeFamilyOfPoints := algebraicallyClosedGeometricPoints_conservative S
  apply ((hQ.jointlyReflectIsomorphisms AddCommGrpCat.{u}).isIso_iff δ).mpr
  intro Φ
  obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ _).mp Φ.property
  rw [← hx]
  let K := AlgebraicClosure (S.residueField x)
  let s := algebraicallyClosedGeometricMap x
  let T := pullback s j
  let a : T ⟶ W := pullback.snd s j
  let t : T ⟶ Spec (.of K) := pullback.fst s j
  have h₁ : IsPullback t a s j := IsPullback.of_hasPullback s j
  have h₂ : IsPullback t (a ≫ r) (s ≫ p) i := h₁.paste_vert hp
  obtain ⟨e₁, he₁⟩ := hj K s t a h₁ A
  obtain ⟨e₂, he₂⟩ := hi K (s ≫ p) t (a ≫ r) h₂ F
  let e := stalkPullbackIso p s
  let β := (pullbackCompIso r a).app F
  let γ := (globalSections T).mapIso β
  have he : (stalk s).map δ ≫ e₁.hom ≫ γ.hom = e.hom.app G ≫ e₂.hom := by
    apply ConcreteCategory.hom_ext
    intro z
    apply globalSections_eq_of_rational_germs t ((pullbackSheaves (a ≫ r)).obj F)
    intro v hv
    have ht : (v ≫ a) ≫ j = s := by
      rw [Category.assoc, ← h₁.w, ← Category.assoc, hv, Category.id_comp]
    let l := (stalkPullbackIso (a ≫ r) v).hom.app F ≫
      eqToHom (congrArg (fun w => (stalk w).obj F) (Category.assoc v a r).symm)
    apply (ConcreteCategory.bijective_of_isIso l).1
    have hLeft : (stalk s).map δ ≫ e₁.hom ≫ γ.hom ≫
        (terminalGerm v).app ((pullbackSheaves (a ≫ r)).obj F) ≫ l =
        (stalk s).map δ ≫ evalAtLiftOver j (v ≫ a) s ht A ≫ (stalkPullbackIso r (v ≫ a)).hom.app F := by
      have hNat := (terminalGerm v).naturality β.hom
      change (globalSections T).map β.hom ≫ (terminalGerm v).app _ =
        (terminalGerm v).app _ ≫ (stalk v).map β.hom at hNat
      have hComp : (stalk v).map β.hom ≫ l =
          (stalkPullbackIso a v).hom.app A ≫ (stalkPullbackIso r (v ≫ a)).hom.app F :=
        stalkPullbackIso_hom_comp r a v F
      simp only [γ, Functor.mapIso_hom]
      rw [reassoc_of% hNat, hComp, reassoc_of% (he₁ v hv)]
    have hRight : e.hom.app G ≫ e₂.hom ≫
        (terminalGerm v).app ((pullbackSheaves (a ≫ r)).obj F) ≫ l =
        e.hom.app G ≫ evalAtLiftOver i ((v ≫ a) ≫ r) (s ≫ p)
          (by rw [Category.assoc, hp.w.symm, ← Category.assoc, ht]) F := by
      simp only [l]
      rw [reassoc_of% (he₂ v hv)]
      rw [evalAtLiftOver_congr_lift i (Category.assoc v a r).symm]
    have hBase : (stalk s).map δ ≫ evalAtLiftOver j (v ≫ a) s ht A ≫
        (stalkPullbackIso r (v ≫ a)).hom.app F =
        e.hom.app G ≫ evalAtLiftOver i ((v ≫ a) ≫ r) (s ≫ p)
          (by rw [Category.assoc, hp.w.symm, ← Category.assoc, ht]) F := by
      exact evalAtLift_baseChangeOver_at p i j r hp (v ≫ a) ht F
    exact ConcreteCategory.congr_hom ((hLeft.trans (hBase.trans hRight.symm))) z
  have hh : IsIso ((stalk s).map δ ≫ e₁.hom ≫ γ.hom) := he.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_right ((stalk s).map δ) (e₁.hom ≫ γ.hom)

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

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves)
namespace PhilipponEtaleAcyclicBaseChange
universe u
private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
def OrdinaryBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ ⦃X' Y' : Scheme.{u}⦄ ⦃a : X' ⟶ X⦄ ⦃b : Y' ⟶ Y⦄ ⦃f' : X' ⟶ Y'⦄,
    IsPullback f' a b f → ∀ F : Ab X,
    Nonempty ((pullbackSheaves b).obj ((pushforward f).obj F) ≅
      (pushforward f').obj ((pullbackSheaves a).obj F))


end PhilipponEtaleAcyclicBaseChange

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicBaseChange (OrdinaryBaseChange)
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleGeometricBaseChangeReduction (HasFiberComparisons isIso_restrictionBaseChangeOver)
open PhilipponEtalePullbackComposition (restrictGlobalSections_app_eq)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtalePullbackSquareUnits (restrictionBaseChangeOver)
open PhilipponEtaleSmallSite (pullbackAdjunction)


namespace PhilipponEtaleProperOrdinaryBaseChange

universe u

/-- Geometric-fiber comparison for proper maps gives ordinary base change
for every proper map, including each finite map. -/
theorem ordinaryBaseChange_of_fiberComparisons
    (hComparison : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsProper f → HasFiberComparisons f)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] : OrdinaryBaseChange f := by
  intro X' Y' a b f' h F
  let : IsProper f' := MorphismProperty.of_isPullback h.flip (inferInstance : IsProper f)
  let d := restrictionBaseChangeOver b f f' a (f' ≫ b) rfl h.w.symm F
  have : IsIso d :=
    isIso_restrictionBaseChangeOver b f f' a h
      (hComparison f inferInstance) (hComparison f' inferInstance) F
  exact ⟨asIso d⟩

/-- Restriction over strictly henselian bases and extension of separably
closed fields suffice for ordinary base change for proper maps. -/
theorem ordinaryBaseChange_of_restrictions
    (hClosed : ∀ (R : Type u) [CommRing R] [HenselianLocalRing R]
      [IsSepClosed (IsLocalRing.ResidueField R)] {Z : Scheme.{u}}
      (g : Z ⟶ Spec (.of R)) [IsProper g] (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}),
      IsIso ((globalSections Z).map ((pullbackAdjunction (pullback.snd
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) g)).unit.app F)))
    (hField : ∀ (L E : Type u) [Field L] [IsSepClosed L] [Field E] [IsAlgClosed E]
      (g : L →+* E) {Z B : Scheme.{u}} (p : Z ⟶ Spec (.of L)) [IsProper p]
      (j : B ⟶ Spec (.of E)) (a : B ⟶ Z) (_h : IsPullback j a (Spec.map (CommRingCat.ofHom g)) p)
      (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}), IsIso ((restrictGlobalSections a).app F))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] : OrdinaryBaseChange f := by
  refine ordinaryBaseChange_of_fiberComparisons (fun {_ _} g hg => ?_) f
  let : IsProper g := hg
  refine PhilipponEtaleStrictLocalGeometricComparison.hasFiberComparisons_of_restrictions g ?_ hField
  intro R _ _ _ Z p _ F
  rw [restrictGlobalSections_app_eq]
  let : IsIso _ := hClosed R p F
  infer_instance

end PhilipponEtaleProperOrdinaryBaseChange

end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    {X Y S T : Scheme.{u}} (p : Y ⟶ X) [IsProper p]
    (i : S ⟶ X) (p₀ : T ⟶ S) (j : T ⟶ Y) (h : IsPullback p₀ j i p)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso (PhilipponEtalePullbackSquareUnits.restrictionBaseChangeOver i p p₀ j (p₀ ≫ i) rfl h.w.symm F) := by
  let : IsProper p₀ := MorphismProperty.of_isPullback h.flip (inferInstance : IsProper p)
  have hGeom {B D : Scheme.{u}} (g : D ⟶ B) [IsProper g] :
      PhilipponEtaleGeometricBaseChangeReduction.HasFiberComparisons g := by
    refine PhilipponEtaleStrictLocalGeometricComparison.hasFiberComparisons_of_restrictions g ?_ ?_
    · intro B _ _ _ Z f _ G
      rw [PhilipponEtalePullbackComposition.restrictGlobalSections_app_eq]
      let : IsIso _ := AlgebraicGeometry.Scheme.isIso_etale_globalSections_restrict_closed_fiber_of_strictly_henselian B f G
      infer_instance
    · intro L E _ _ _ _ φ Z B f _ b c hb G
      exact AlgebraicGeometry.Scheme.isIso_etale_restrictGlobalSections_of_separably_closed_field_extension L E φ f b c hb G
  exact PhilipponEtaleGeometricBaseChangeReduction.isIso_restrictionBaseChangeOver i p p₀ j h
    (hGeom p) (hGeom p₀) F

end
