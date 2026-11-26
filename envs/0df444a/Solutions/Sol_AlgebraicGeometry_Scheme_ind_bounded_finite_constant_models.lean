-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.ind_bounded_finite_constant_models
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-26T00:12:12.122433+00:00
-- url     : https://prove2.me/submissions/c6c15334-ca7d-4c73-bc3b-2e937e5bd88d

import Definitions.Def_AlgebraicGeometry_EtaleNoetherianBoundedConstantModels

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
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open PhilipponEtaleBaseChangeComparison (baseChange map_isPullback)
open PhilipponEtaleBaseChangeGerms (evalAtLiftOver_naturality)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleConstantDegreeZero (constantSheafIso continuousSheaf)
open PhilipponEtaleDirectImageGerms (evalAtLiftOver evalAtLift_germ_of_eq)
open PhilipponEtaleFinitePointLifts (exists_lift_in_open_of_finite)


namespace PhilipponEtaleConstantDirectImageStalk

universe u

private abbrev stalk {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (.of K) ⟶ X) := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})

private theorem eq_value_of_eq_germ {Y : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (.of K) ⟶ Y) (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    (V : Y.Etale) (v : (Scheme.pointSmallEtale s).fiber.obj V)
    (a b : C(V.left, M))
    (h : (Scheme.pointSmallEtale s).toPresheafFiber V v (continuousSheaf Y M).obj a =
      (Scheme.pointSmallEtale s).toPresheafFiber V v (continuousSheaf Y M).obj b) :
    a (v.left (default : Spec (.of K))) = b (v.left (default : Spec (.of K))) := by
  obtain ⟨W, g, w, hw, he⟩ := ((Scheme.pointSmallEtale s).toPresheafFiber_eq_iff' V v
    (P := (continuousSheaf Y M).obj) a b).mp h
  have hcomp : w.left ≫ g.left = v.left := congrArg Over.Hom.left hw
  let z : Spec (.of K) := default
  have hval := congrArg (fun c : C(W.left, M) => c (w.left z)) he
  change a (g.left (w.left z)) = b (g.left (w.left z)) at hval
  have hp : g.left (w.left z) = v.left z :=
    (Scheme.Hom.comp_apply w.left g.left z).symm.trans
      (congrArg (fun k : Spec (.of K) ⟶ V.left => k z) hcomp)
  exact (congrArg a hp).symm.trans (hval.trans (congrArg b hp))

private theorem ext_continuous_of_evaluations_eq {X Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p]
    {K : Type u} [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ X)
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    (x y : (stalk s).obj ((pushforward p).obj (continuousSheaf Y M)))
    (h : ∀ (r : Spec (.of K) ⟶ Y) (hr : r ≫ p = s),
      evalAtLiftOver p r s hr (continuousSheaf Y M) x =
      evalAtLiftOver p r s hr (continuousSheaf Y M) y) : x = y := by
  let Φ := Scheme.pointSmallEtale s
  let F := continuousSheaf Y M
  let H := (pushforward p).obj F
  obtain ⟨W, u, a, b, ha, hb⟩ := Φ.toPresheafFiber_jointly_surjective₂ (P := H.obj) x y
  let V := (baseChange p).obj W
  let d : V.left ⟶ W.left := pullback.fst W.hom p
  let q : V.left ⟶ Y := pullback.snd W.hom p
  let : IsFinite d := inferInstanceAs (IsFinite (pullback.fst W.hom p))
  change C(V.left, M) at a b
  have hEqOpen : IsOpen {z : V.left | a z = b z} :=
    (isOpen_discrete (Set.diagonal M)).preimage (a.continuous.prodMk b.continuous)
  let D : V.left.Opens := ⟨{z | a z ≠ b z}, (isClosed_eq a.continuous b.continuous).isOpen_compl⟩
  have hD : IsClosed (D : Set V.left) := hEqOpen.isClosed_compl
  let z₀ : Spec (.of K) := default
  have hAvoid : u.left z₀ ∉ d '' (D : Set V.left) := by
    rintro ⟨z, hz, hdz⟩
    obtain ⟨t, ht, htD⟩ := exists_lift_in_open_of_finite d u.left D ⟨z, hz, hdz⟩
    let r := t ≫ q
    have hr : r ≫ p = s := by
      change t ≫ pullback.snd W.hom p ≫ p = s
      rw [← pullback.condition, ← Category.assoc]
      change (t ≫ d) ≫ W.hom = s
      rw [ht]
      exact Over.w u
    let w : (Scheme.pointSmallEtale r).fiber.obj V := Over.homMk t rfl
    have hGerm : (Scheme.pointSmallEtale r).toPresheafFiber V w F.obj a =
        (Scheme.pointSmallEtale r).toPresheafFiber V w F.obj b := by
      let e := evalAtLiftOver p r s hr F
      let l := Φ.toPresheafFiber W u H.obj
      let v := (Scheme.pointSmallEtale r).toPresheafFiber V w F.obj
      have hg : l ≫ e = v := evalAtLift_germ_of_eq p r (s := s) hr F W u w ht
      have hval (c : H.obj.obj (op W)) : e (l c) = v c := by
        have hc : (l ≫ e) c = v c := ConcreteCategory.congr_hom hg c
        exact hc
      calc
        _ = e (l a) := (hval a).symm
        _ = e x := congrArg (fun z => e z) ha
        _ = e y := h r hr
        _ = e (l b) := congrArg (fun z => e z) hb.symm
        _ = _ := hval b
    exact htD (eq_value_of_eq_germ r M V w a b hGerm)
  let U : W.left.Opens := ⟨(d '' (D : Set V.left))ᶜ, (d.isClosedMap _ hD).isOpen_compl⟩
  let W' := Scheme.Etale.mk (U.ι ≫ W.hom)
  let g : W' ⟶ W := MorphismProperty.Over.homMk U.ι rfl
  have hU : Set.range u.left ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    have hz : z = z₀ := @Subsingleton.elim (Spec (.of K)) inferInstance z z₀
    rw [hz]
    exact ⟨⟨u.left z₀, hAvoid⟩, rfl⟩
  let v := IsOpenImmersion.lift U.ι u.left hU
  have hv : v ≫ U.ι = u.left := IsOpenImmersion.lift_fac _ _ _
  let u' : Φ.fiber.obj W' := Over.homMk v (by
    change v ≫ U.ι ≫ W.hom = s
    rw [← Category.assoc, hv]
    exact Over.w u)
  refine ha.symm.trans (Eq.trans ?_ hb)
  apply (Φ.toPresheafFiber_eq_iff' (P := H.obj) W u a b).mpr
  refine ⟨W', g, u', Over.OverMorphism.ext hv, ?_⟩
  let f := ((baseChange p).map g).left
  change (a.comp ⟨f, f.continuous⟩) = (b.comp ⟨f, f.continuous⟩)
  ext z
  change a (f z) = b (f z)
  by_contra hn
  have hImg : d (f z) ∈ d '' (D : Set V.left) := ⟨f z, hn, rfl⟩
  have hw : U.ι (pullback.fst W'.hom p z) = d (f z) := by
    let d' : ((baseChange p).obj W').left ⟶ W'.left := pullback.fst W'.hom p
    have hs : d' ≫ g.left = f ≫ d := (map_isPullback p g).w
    change (d' ≫ g.left) z = (f ≫ d) z
    exact congrArg (fun k : ((baseChange p).obj W').left ⟶ W.left => k z) hs
  have hNot : U.ι (pullback.fst W'.hom p z) ∉ d '' (D : Set V.left) :=
    (pullback.fst W'.hom p z).property
  exact hNot (hw.symm ▸ hImg)

/-- The lifts of an algebraically closed geometric point separate
stalk sections of the finite direct image of a constant abelian sheaf. -/
theorem ext_of_evaluations_eq {X Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p]
    {K : Type u} [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ X) (M : AddCommGrpCat.{u})
    (x y : (stalk s).obj ((pushforward p).obj ((constantSheaf Y.smallEtaleTopology _).obj M)))
    (h : ∀ (r : Spec (.of K) ⟶ Y) (hr : r ≫ p = s),
      evalAtLiftOver p r s hr ((constantSheaf Y.smallEtaleTopology _).obj M) x =
      evalAtLiftOver p r s hr ((constantSheaf Y.smallEtaleTopology _).obj M) y) : x = y := by
  let : TopologicalSpace M := ⊥
  let : DiscreteTopology M := ⟨rfl⟩
  let e := constantSheafIso Y M
  let d := (stalk s).mapIso ((pushforward p).mapIso e)
  apply (ConcreteCategory.bijective_of_isIso d.hom).1
  apply ext_continuous_of_evaluations_eq p s M
  intro r hr
  have hn := evalAtLiftOver_naturality p r s hr e.hom
  exact (ConcreteCategory.congr_hom hn x).trans
    ((congrArg ((stalk r).map e.hom) (h r hr)).trans (ConcreteCategory.congr_hom hn y).symm)

end PhilipponEtaleConstantDirectImageStalk

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)
open PhilipponEtaleBaseChangeGerms (evalAtLift_baseChangeOver)
open PhilipponEtaleBoundedFiniteModelReduction (boundedFiniteModel)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDirectImageGerms (evalAtLift evalAtLiftOver)
open PhilipponEtaleFinitePresentationModel (boundedFiniteModel_of_noetherian)
open PhilipponEtaleFinitePresentationDescent (exists_noetherian_model)
open PhilipponEtaleFinitePresentations
  (finiteEtalePresentations ind_boundedFiniteModel_of_finitePresentations)
open PhilipponEtaleGeometricStalks
  (algebraicallyClosedGeometricMap algebraicallyClosedGeometricPoints_conservative)
open PhilipponEtalePullbackSquareUnits (restrictionBaseChangeOver)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleStalkPullback (stalkPullbackIso)


namespace PhilipponEtaleFiniteModelPullback

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private abbrev stalk {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (.of K) ⟶ X) := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})

private abbrev comparison {X S Y W : Scheme.{u}} (f : S ⟶ X) (p : Y ⟶ X)
    (a : W ⟶ S) (b : W ⟶ Y) (h : IsPullback a b f p) (F : Ab Y) :=
  restrictionBaseChangeOver f p a b (a ≫ f) rfl h.w.symm F

private theorem eval_eq_of_baseChange_eq {X S Y W : Scheme.{u}} (f : S ⟶ X) (p : Y ⟶ X)
    (a : W ⟶ S) (b : W ⟶ Y) (h : IsPullback a b f p) (F : Ab Y)
    {K : Type u} [Field K] [IsSepClosed K] (s : Spec (.of K) ⟶ S)
    (x y : (stalk s).obj ((pullbackSheaves f).obj ((pushforward p).obj F)))
    (hxy : (stalk s).map (comparison f p a b h F) x =
      (stalk s).map (comparison f p a b h F) y)
    (r : Spec (.of K) ⟶ Y) (hr : r ≫ p = s ≫ f) :
    evalAtLiftOver p r (s ≫ f) hr F ((stalkPullbackIso f s).hom.app ((pushforward p).obj F) x) =
      evalAtLiftOver p r (s ≫ f) hr F ((stalkPullbackIso f s).hom.app ((pushforward p).obj F) y) := by
  obtain ⟨v, hs, ht⟩ := h.exists_lift s r hr.symm
  subst s
  subst r
  let q := evalAtLift a v ((pullbackSheaves b).obj F) ≫ (stalkPullbackIso b v).hom.app F
  let k := (stalk (v ≫ a)).map (comparison f p a b h F)
  have hn := evalAtLift_baseChangeOver f p a b (a ≫ f) rfl h.w.symm v F
  have he (z : (stalk (v ≫ a)).obj ((pullbackSheaves f).obj ((pushforward p).obj F))) :
      q (k z) = evalAtLiftOver p (v ≫ b) ((v ≫ a) ≫ f) hr F
        ((stalkPullbackIso f (v ≫ a)).hom.app ((pushforward p).obj F) z) :=
    ConcreteCategory.congr_hom hn z
  exact (he x).symm.trans ((congrArg q hxy).trans (he y))

/-- After arbitrary base change, the inverse image of a finite direct
image of a constant sheaf embeds in the corresponding direct image
on the pullback square. -/
theorem mono_baseChange_finite_constant {X S Y W : Scheme.{u}} (f : S ⟶ X) (p : Y ⟶ X)
    [IsFinite p] (a : W ⟶ S) (b : W ⟶ Y) (h : IsPullback a b f p) (M : AddCommGrpCat.{u}) :
    Mono (comparison f p a b h ((constantSheaf Y.smallEtaleTopology _).obj M)) := by
  let F := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj M
  let m := comparison f p a b h F
  let P := ObjectProperty.ofObj fun x : S => Scheme.pointSmallEtale (algebraicallyClosedGeometricMap x)
  have hP : P.IsConservativeFamilyOfPoints := algebraicallyClosedGeometricPoints_conservative S
  let : ∀ Φ : P.FullSubcategory, Mono (Φ.obj.sheafFiber.map m) := by
    intro Φ
    obtain ⟨z, hz⟩ := (ObjectProperty.ofObj_iff _ _).mp Φ.property
    rw [← hz]
    let s := algebraicallyClosedGeometricMap z
    apply (AddCommGrpCat.mono_iff_injective _).mpr
    intro x y hxy
    let e := (stalkPullbackIso f s).app ((pushforward p).obj F)
    apply (ConcreteCategory.bijective_of_isIso e.hom).1
    apply PhilipponEtaleConstantDirectImageStalk.ext_of_evaluations_eq p (s ≫ f) M
    intro r hr
    exact eval_eq_of_baseChange_eq f p a b h F s x y hxy r hr
  exact (hP.jointlyReflectMonomorphisms AddCommGrpCat.{u}).mono m

/-- The property of admitting a bounded finite constant model survives
pullback along any morphism of schemes. -/
theorem boundedFiniteModel_pullback {X S : Scheme.{u}} (f : S ⟶ X) (N : ℕ) (F : Ab X)
    (hF : boundedFiniteModel X N F) : boundedFiniteModel S N ((pullbackSheaves f).obj F) := by
  obtain ⟨Y, p, _, _, M, hM, hN, m, hm⟩ := hF
  let W := pullback f p
  let a : W ⟶ S := pullback.fst f p
  let b : W ⟶ Y := pullback.snd f p
  let F₀ := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj M
  let c := comparison f p a b (IsPullback.of_hasPullback f p) F₀
  let e := (pushforward a).mapIso ((pullbackConstantIso b).app M)
  let : Mono m := hm
  let : Mono c := mono_baseChange_finite_constant f p a b (IsPullback.of_hasPullback f p) M
  refine ⟨W, a, inferInstanceAs (IsFinite (pullback.fst f p)),
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst f p)), M, hM, hN,
    (pullbackSheaves f).map m ≫ c ≫ e.hom, ?_⟩
  infer_instance

/-- An abelian étale sheaf over an affine scheme annihilated by a positive
integer is a filtered colimit of bounded finite constant models. -/
theorem ind_boundedFiniteModel {X : Scheme.{u}} [IsAffine X] (N : ℕ) (hN : N ≠ 0)
    (F : Ab X) (hF : N • 𝟙 F = 0) :
    ObjectProperty.ind.{u} (boundedFiniteModel X N) F := by
  refine ind_boundedFiniteModel_of_finitePresentations X N F hF ?_
  intro E hE
  obtain ⟨A, _, _, f, E₀, hE₀, ⟨e⟩⟩ := exists_noetherian_model hE
  have hModel := boundedFiniteModel_of_noetherian A N hN E₀ hE₀
  obtain ⟨Y, p, hp, hfp, M, hM, hAnnihilated, m, hm⟩ := boundedFiniteModel_pullback f N E₀ hModel
  let : Mono m := hm
  exact ⟨Y, p, hp, hfp, M, hM, hAnnihilated, e.inv ≫ m, inferInstance⟩

end PhilipponEtaleFiniteModelPullback

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves)
universe u

theorem solution
    (X : Scheme.{u}) [IsAffine X] (N : ℕ) (hN : N ≠ 0)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (hF : N • 𝟙 F = 0) :
    ObjectProperty.ind.{u} (fun E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} =>
        ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (_ : IsFinite p) (_ : LocallyOfFinitePresentation p)
          (M : AddCommGrpCat.{u}) (_ : Finite M), N • 𝟙 M = 0 ∧
            ∃ m : E ⟶ (pushforward p).obj ((constantSheaf Y.smallEtaleTopology
              AddCommGrpCat.{u}).obj M), Mono m) F := by
  exact PhilipponEtaleFiniteModelPullback.ind_boundedFiniteModel N hN F hF

end

end
