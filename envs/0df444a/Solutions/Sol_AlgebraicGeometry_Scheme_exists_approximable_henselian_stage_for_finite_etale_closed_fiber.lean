-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_approximable_henselian_stage_for_finite_etale_closed_fiber
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T19:58:17.145221+00:00
-- url     : https://prove2.me/submissions/d0e2bd8b-9a18-417e-8ec7-8ae03bc89602
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_EtaleClosedFiberSections
import Mathlib
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.RingTheory.RingHom.Etale
import Theorems.Thm_Algebra_Etale_exists_moduleFinite_model_subalgebra_fg
import Theorems.Thm_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd
import Theorems.Thm_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_proper_finitePresentation_envelope_with_noetherian_baseChange
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation
import Theorems.Thm_IsLocalRing_exists_approximable_henselization_of_localization_atPrime

noncomputable section

section

section

set_option maxHeartbeats 1000000


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct


namespace PhilipponEtaleFilteredDescent

universe u v w

variable {J : Type w} [Category.{v} J] [IsFiltered J]
  (F : J ⥤ CommRingCat.{u}) {c : Cocone F} (hc : IsColimit c)
  [PreservesColimit F (forget CommRingCat.{u})]

include hc in
private theorem exists_subalgebra_factorization [Algebra (ULift.{u} ℤ) c.pt]
    (A₀ : Subalgebra (ULift.{u} ℤ) c.pt) (hfg : A₀.FG) :
    ∃ (i : J) (kᵢ : CommRingCat.of A₀ ⟶ F.obj i),
      CommRingCat.ofHom A₀.val.toRingHom = kᵢ ≫ c.ι.app i := by
  let Z := CommRingCat.of (ULift.{u} ℤ)
  let A := CommRingCat.of A₀
  let z : Z ⟶ A := CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A₀)
  let hZ : IsInitial Z := CommRingCat.isInitial
  let α : (Functor.const J).obj Z ⟶ F :=
    { app := fun i => hZ.to (F.obj i)
      naturality := fun _ _ _ => hZ.hom_ext _ _ }
  let k : A ⟶ c.pt := CommRingCat.ofHom A₀.val.toRingHom
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : Algebra.FiniteType (ULift.{u} ℤ) A₀ := A₀.fg_iff_finiteType.mp hfg
  have hz : z.hom.FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr
      (Algebra.FinitePresentation.of_finiteType.mp inferInstance)
  obtain ⟨i, kᵢ, _, hi⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    Z F α z c hc hz k (fun i => hZ.hom_ext _ _)
  exact ⟨i, kᵢ, hi⟩

include hc in
/-- Every finite étale algebra over a filtered colimit of rings is the base
change of a finite étale algebra from a stage of the diagram. -/
theorem exists_finite_etale_model (B : Type u) [CommRing B] [Algebra c.pt B]
    [Algebra.Etale c.pt B] [Module.Finite c.pt B] :
    ∃ (i : J) (Bᵢ : Type u) (_ : CommRing Bᵢ) (_ : Algebra (F.obj i) Bᵢ),
      Algebra.Etale (F.obj i) Bᵢ ∧ Module.Finite (F.obj i) Bᵢ ∧
        letI : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
        Nonempty (c.pt ⊗[F.obj i] Bᵢ ≃ₐ[c.pt] B) := by
  let : Algebra (ULift.{u} ℤ) c.pt := ULift.algebra' ℤ c.pt
  obtain ⟨A₀, B₀, _, _, hfg, he, hfin, ⟨e⟩⟩ :=
    Algebra.Etale.exists_moduleFinite_model_subalgebra_fg (ULift.{u} ℤ) c.pt B
  obtain ⟨i, kᵢ, hi⟩ := exists_subalgebra_factorization F hc A₀ hfg
  let : Algebra A₀ (F.obj i) := kᵢ.hom.toAlgebra
  let : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
  let : IsScalarTower A₀ (F.obj i) c.pt :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hi)
  let : Algebra.Etale A₀ B₀ := he
  let : Module.Finite A₀ B₀ := hfin
  refine ⟨i, (F.obj i) ⊗[A₀] B₀, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨(Algebra.TensorProduct.cancelBaseChange A₀ (F.obj i) c.pt c.pt B₀).trans e⟩

omit [IsFiltered J] [PreservesColimit F (forget CommRingCat.{u})] in
private theorem exists_pushout_of_equiv {B : CommRingCat.{u}} (p : c.pt ⟶ B) (i : J)
    (T : Type u) [CommRing T] [Algebra (F.obj i) T]
    (h : letI : Algebra c.pt B := p.hom.toAlgebra
      letI : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
      Nonempty (c.pt ⊗[F.obj i] T ≃ₐ[c.pt] B)) :
    ∃ q : CommRingCat.of T ⟶ B,
      IsPushout (c.ι.app i) (CommRingCat.ofHom (algebraMap (F.obj i) T)) p q := by
  let : Algebra c.pt B := p.hom.toAlgebra
  let : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
  obtain ⟨e⟩ := h
  let T' := CommRingCat.of T
  let e' := e.toRingEquiv.toCommRingCatIso
  let q : T' ⟶ B := CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ e'.hom
  have hleft : CommRingCat.ofHom (algebraMap c.pt (c.pt ⊗[F.obj i] T)) ≫ e'.hom = p := by
    apply ConcreteCategory.hom_ext
    intro x
    exact e.commutes x
  refine ⟨q, ?_⟩
  exact (CommRingCat.isPushout_tensorProduct (F.obj i) c.pt T).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e'
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
    (by rw [Iso.refl_hom, Category.id_comp]; exact hleft)
    (by rw [Iso.refl_hom, Category.id_comp])

include hc in
/-- A finite étale ring map with source the colimit descends as a finite
étale ring map. -/
theorem exists_finite_etale_pushout {B : CommRingCat.{u}} (p : c.pt ⟶ B)
    (hp : p.hom.Etale) (hfin : p.hom.Finite) :
    ∃ (i : J) (Bᵢ : CommRingCat.{u}) (g : F.obj i ⟶ Bᵢ) (q : Bᵢ ⟶ B),
      g.hom.Etale ∧ g.hom.Finite ∧ IsPushout (c.ι.app i) g p q := by
  let : Algebra c.pt B := p.hom.toAlgebra
  let : Algebra.Etale c.pt B := RingHom.etale_algebraMap.mp hp
  let : Module.Finite c.pt B := RingHom.finite_algebraMap.mp hfin
  obtain ⟨i, T, _, _, hT, hfinT, h⟩ := exists_finite_etale_model F hc B
  obtain ⟨q, hq⟩ := exists_pushout_of_equiv F p i T h
  exact ⟨i, .of T, _, q, RingHom.etale_algebraMap.mpr hT, RingHom.finite_algebraMap.mpr hfinT, hq⟩

end PhilipponEtaleFilteredDescent

end

section

set_option maxHeartbeats 1000000


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite


namespace PhilipponEtaleAffineLimitDescent

universe u v w

variable {J : Type w} [Category.{v} J] [IsFiltered J]
  (F : J ⥤ CommRingCat.{u}) {c : Cocone F} (hc : IsColimit c)
  [PreservesColimit F (forget CommRingCat.{u})]

include hc in
/-- A finite étale cover of the spectrum of a filtered colimit descends
to a finite étale cover at one of the stages. -/
theorem exists_finite_etale_model {Y : Scheme.{u}} (f : Y ⟶ Spec c.pt) [IsFinite f] [Etale f] :
    ∃ (i : J) (Yᵢ : Scheme.{u}) (fᵢ : Yᵢ ⟶ Spec (F.obj i)) (g : Y ⟶ Yᵢ),
      IsFinite fᵢ ∧ Etale fᵢ ∧ IsPullback f g (Spec.map (c.ι.app i)) fᵢ := by
  let : IsAffine Y := isAffine_of_isAffineHom f
  obtain ⟨p, hp⟩ := Spec.map_surjective (Y.isoSpec.inv ≫ f)
  have hpEt : Etale (Spec.map p) := hp.symm ▸ (inferInstance : Etale (Y.isoSpec.inv ≫ f))
  have hpFin : IsFinite (Spec.map p) := hp.symm ▸ (inferInstance : IsFinite (Y.isoSpec.inv ≫ f))
  obtain ⟨i, T, d, q, hd, hfin, h⟩ := PhilipponEtaleFilteredDescent.exists_finite_etale_pushout F hc p
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp hpEt) ((IsFinite.SpecMap_iff p).mp hpFin)
  have hSpec : IsPullback (Spec.map p) (Spec.map q) (Spec.map (c.ι.app i)) (Spec.map d) :=
    h.op.flip.map Scheme.Spec
  refine ⟨i, Spec T, Spec.map d, Y.isoSpec.hom ≫ Spec.map q, (IsFinite.SpecMap_iff d).mpr hfin,
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hd, ?_⟩
  apply hSpec.of_iso Y.isoSpec.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa using hp
  · simp
  · simp
  · simp

section Pushout

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  (D : I ⥤ CommRingCat.{u}) {d : Cocone D} (hd : IsColimit d)
  {A B : CommRingCat.{u}} (b : A ⟶ B) (s : (Functor.const I).obj A ⟶ D)
  (a : A ⟶ d.pt) (h : ∀ i, s.app i ≫ d.ι.app i = a)

private abbrev pushoutFunctor := Under.lift D s ⋙ Under.pushout b ⋙ Under.forget B

private abbrev pushoutCocone : Cocone (pushoutFunctor D b s) :=
  (Under.pushout b ⋙ Under.forget B).mapCocone (Under.liftCocone D s d a h)

include hd in
/-- An affine finite étale cover after extension of the base ring descends
to an intermediate base change along a filtered approximation of that ring. -/
theorem exists_finite_etale_model_of_pushout {Y : Scheme.{u}}
    (f : Y ⟶ Spec (pushout a b)) [IsFinite f] [Etale f] :
    ∃ (i : I) (Yᵢ : Scheme.{u}) (fᵢ : Yᵢ ⟶ Spec (pushout (s.app i) b)) (g : Y ⟶ Yᵢ),
      IsFinite fᵢ ∧ Etale fᵢ ∧ IsPullback f g
        (Spec.map (pushout.map (s.app i) b a b (d.ι.app i) (𝟙 B) (𝟙 A)
          (by simpa using h i) (by simp))) fᵢ := by
  let : IsConnected I := IsFiltered.isConnected I
  let E := pushoutFunctor D b s
  let e := pushoutCocone D b s a h
  have he : IsColimit e := isColimitOfPreserves (Under.pushout b ⋙ Under.forget B)
    (Under.isColimitLiftCocone D s d a h hd)
  obtain ⟨i, Yᵢ, fᵢ, g, hfin, het, hpull⟩ := exists_finite_etale_model E he f
  refine ⟨i, Yᵢ, fᵢ, g, hfin, het, ?_⟩
  have hi : e.ι.app i = pushout.map (s.app i) b a b (d.ι.app i) (𝟙 B) (𝟙 A)
      (by simpa using h i) (by simp) := by
    change pushout.desc (f := s.app i) (g := b) (d.ι.app i ≫ pushout.inl a b) (pushout.inr a b) _ = _
    apply pushout.hom_ext <;> simp [pushout.map]
  rwa [hi] at hpull

end Pushout

end PhilipponEtaleAffineLimitDescent

end

section

set_option maxHeartbeats 1000000


set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits


namespace PhilipponPullbackLimit

universe u v u' v'

variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C] [HasPullbacks C]
  {S X Y : J ⥤ C} (f : X ⟶ S) (g : Y ⟶ S)

/-- The pullbacks taken pointwise in a diagram of cospans. -/
def diagram : J ⥤ C where
  obj j := pullback (f.app j) (g.app j)
  map h := pullback.map _ _ _ _ (X.map h) (Y.map h) (S.map h)
    (f.naturality h).symm (g.naturality h).symm
  map_id j := by
    apply pullback.hom_ext <;> simp [pullback.map]
  map_comp h k := by
    apply pullback.hom_ext <;> simp [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc]

/-- Projection to the first diagram. -/
def first : diagram f g ⟶ X where
  app j := pullback.fst (f.app j) (g.app j)
  naturality i j h := by simp [diagram, pullback.map, pullback.lift_fst]

/-- Projection to the second diagram. -/
def second : diagram f g ⟶ Y where
  app j := pullback.snd (f.app j) (g.app j)
  naturality i j h := by simp [diagram, pullback.map, pullback.lift_snd]

theorem projection_condition (j : J) :
    (first f g).app j ≫ f.app j = (second f g).app j ≫ g.app j := pullback.condition

variable {cX : Cone X} {cY : Cone Y} {cS : Cone S} (a : cX.pt ⟶ cS.pt) (b : cY.pt ⟶ cS.pt)
  (ha : ∀ j, cX.π.app j ≫ f.app j = a ≫ cS.π.app j)
  (hb : ∀ j, cY.π.app j ≫ g.app j = b ≫ cS.π.app j)

/-- The cone on pointwise pullbacks whose vertex is the pullback of the cone vertices. -/
abbrev cone : Cone (diagram f g) where
  pt := pullback a b
  π :=
    { app := fun j => pullback.map _ _ _ _ (cX.π.app j) (cY.π.app j) (cS.π.app j) (ha j).symm (hb j).symm
      naturality := by
        intro i j h
        apply pullback.hom_ext <;> simp [diagram, pullback.map, Category.assoc, pullback.lift_fst,
          pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Cone.w] }

@[reassoc (attr := simp)]
theorem cone_first (j : J) :
    (cone f g a b ha hb).π.app j ≫ (first f g).app j = pullback.fst a b ≫ cX.π.app j :=
  pullback.lift_fst ..

@[reassoc (attr := simp)]
theorem cone_second (j : J) :
    (cone f g a b ha hb).π.app j ≫ (second f g).app j = pullback.snd a b ≫ cY.π.app j :=
  pullback.lift_snd ..

variable (hX : IsLimit cX) (hY : IsLimit cY) (hS : IsLimit cS)

private def liftFirst (t : Cone (diagram f g)) : t.pt ⟶ cX.pt :=
  hX.lift ((Cone.postcompose (first f g)).obj t)

private def liftSecond (t : Cone (diagram f g)) : t.pt ⟶ cY.pt :=
  hY.lift ((Cone.postcompose (second f g)).obj t)

@[reassoc (attr := simp)]
private theorem liftFirst_fac (t : Cone (diagram f g)) (j : J) :
    liftFirst f g hX t ≫ cX.π.app j = t.π.app j ≫ (first f g).app j :=
  hX.fac _ j

@[reassoc (attr := simp)]
private theorem liftSecond_fac (t : Cone (diagram f g)) (j : J) :
    liftSecond f g hY t ≫ cY.π.app j = t.π.app j ≫ (second f g).app j :=
  hY.fac _ j

include ha hb hS in
private theorem lift_condition (t : Cone (diagram f g)) :
    liftFirst f g hX t ≫ a = liftSecond f g hY t ≫ b := by
  apply hS.hom_ext
  intro j
  simp only [Category.assoc, ← ha j, ← hb j, liftFirst_fac_assoc, liftSecond_fac_assoc,
    projection_condition f g j]

/-- The pullback of limit cones is a limit of the pointwise pullbacks. -/
def isLimit : IsLimit (cone f g a b ha hb) where
  lift t := pullback.lift (liftFirst f g hX t) (liftSecond f g hY t)
    (lift_condition f g a b ha hb hX hY hS t)
  fac t j := by
    apply pullback.hom_ext
    · change (_ ≫ (cone f g a b ha hb).π.app j) ≫ (first f g).app j = _
      rw [Category.assoc, cone_first, pullback.lift_fst_assoc, liftFirst_fac]
      rfl
    · change (_ ≫ (cone f g a b ha hb).π.app j) ≫ (second f g).app j = _
      rw [Category.assoc, cone_second, pullback.lift_snd_assoc, liftSecond_fac]
      rfl
  uniq t k hk := by
    apply pullback.hom_ext
    · apply hX.hom_ext
      intro j
      have h := congrArg (fun m => m ≫ (first f g).app j) (hk j)
      change (k ≫ (cone f g a b ha hb).π.app j) ≫ (first f g).app j = _ at h
      rw [Category.assoc, cone_first] at h
      rw [Category.assoc, pullback.lift_fst, liftFirst_fac]
      exact h
    · apply hY.hom_ext
      intro j
      have h := congrArg (fun m => m ≫ (second f g).app j) (hk j)
      change (k ≫ (cone f g a b ha hb).π.app j) ≫ (second f g).app j = _ at h
      rw [Category.assoc, cone_second] at h
      rw [Category.assoc, pullback.lift_snd, liftSecond_fac]
      exact h

end PhilipponPullbackLimit

end

section

set_option maxHeartbeats 1000000


set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponFiniteMorphismLimitDescent

universe u

variable {I : Type u} [Category.{u} I]
  (D : I ⥤ Scheme.{u}) {c : Cone D} (hc : IsLimit c) {S : Scheme.{u}}
  (t : D ⟶ (Functor.const I).obj S) (a : c.pt ⟶ S) (ha : ∀ i, c.π.app i ≫ t.app i = a)
  {V : Scheme.{u}} (p : V ⟶ S)

abbrev diagram := PhilipponPullbackLimit.diagram t ((Functor.const I).map p)

abbrev toBase := PhilipponPullbackLimit.first t ((Functor.const I).map p)

abbrev toModel := PhilipponPullbackLimit.second t ((Functor.const I).map p)

abbrev cone : Cone (diagram D t p) :=
  PhilipponPullbackLimit.cone t ((Functor.const I).map p)
    (cX := c) (cY := constCone I V) (cS := constCone I S) a p
    (fun i => (ha i).trans (Category.comp_id a).symm)
    (fun _ => (Category.id_comp p).trans (Category.comp_id p).symm)

@[reassoc]
theorem projection_fst (i : I) :
    (cone D t a ha p).π.app i ≫ pullback.fst (t.app i) p = pullback.fst a p ≫ c.π.app i :=
  PhilipponPullbackLimit.cone_first ..

@[reassoc]
theorem projection_snd (i : I) :
    (cone D t a ha p).π.app i ≫ pullback.snd (t.app i) p = pullback.snd a p := by
  exact (PhilipponPullbackLimit.cone_second ..).trans (Category.comp_id _)

@[reassoc]
theorem transition_fst {i j : I} (e : i ⟶ j) :
    (diagram D t p).map e ≫ pullback.fst (t.app j) p = pullback.fst (t.app i) p ≫ D.map e :=
  (toBase D t p).naturality e

@[reassoc]
theorem transition_snd {i j : I} (e : i ⟶ j) :
    (diagram D t p).map e ≫ pullback.snd (t.app j) p = pullback.snd (t.app i) p :=
  ((toModel D t p).naturality e).trans (Category.comp_id _)

theorem transition_isPullback {i j : I} (e : i ⟶ j) :
    IsPullback ((diagram D t p).map e) (pullback.fst (t.app i) p)
      (pullback.fst (t.app j) p) (D.map e) := by
  have h : D.map e ≫ t.app j = t.app i := (t.naturality e).trans (Category.comp_id _)
  refine IsPullback.of_right (h₁₂ := pullback.snd (t.app j) p) (h₂₂ := t.app j) (v₁₃ := p)
    ?_ (transition_fst D t p e) (IsPullback.of_hasPullback (t.app j) p).flip
  rw [transition_snd D t p e, h]
  exact (IsPullback.of_hasPullback (t.app i) p).flip

theorem projection_isPullback (i : I) :
    IsPullback ((cone D t a ha p).π.app i) (pullback.fst a p)
      (pullback.fst (t.app i) p) (c.π.app i) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd (t.app i) p) (h₂₂ := t.app i) (v₁₃ := p)
    ?_ (projection_fst D t a ha p i) (IsPullback.of_hasPullback (t.app i) p).flip
  rw [projection_snd D t a ha p i, ha i]
  exact (IsPullback.of_hasPullback a p).flip

section Finite

variable [IsCofiltered I]

include hc in
def isLimit : IsLimit (cone D t a ha p) := by
  let : IsConnected I := IsCofiltered.isConnected I
  exact PhilipponPullbackLimit.isLimit t ((Functor.const I).map p) a p _ _
    hc (isLimitConstCone I V) (isLimitConstCone I S)

variable [QuasiCompact p] [QuasiSeparated p] [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

private instance (i : I) : CompactSpace ((diagram D t p).obj i) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.fst (t.app i) p)

private instance (i : I) : QuasiSeparatedSpace ((diagram D t p).obj i) :=
  quasiSeparatedSpace_of_quasiSeparated (pullback.fst (t.app i) p)

private instance {i j : I} (f : i ⟶ j) : IsAffineHom ((diagram D t p).map f) :=
  MorphismProperty.of_isPullback (transition_isPullback D t p f).flip inferInstance

private abbrev overS : diagram D t p ⟶ (Functor.const I).obj S := toBase D t p ≫ t

include hc in
/-- A morphism from the pullback of a finite model to a finitely presented
target over the same base comes from a morphism at one stage. -/
theorem exists_morphism {W : Scheme.{u}} (q : W ⟶ S) [LocallyOfFinitePresentation q]
    (f : pullback a p ⟶ W) (hf : f ≫ q = pullback.fst a p ≫ a) :
    ∃ (i : I) (g : pullback (t.app i) p ⟶ W),
      (cone D t a ha p).π.app i ≫ g = f ∧ g ≫ q = pullback.fst (t.app i) p ≫ t.app i := by
  let C := cone D t a ha p
  let m : C.pt ⟶ W := f
  refine Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (diagram D t p)
    (overS D t p) q C (isLimit D hc t a ha p) m ?_
  ext i
  change (cone D t a ha p).π.app i ≫ (toBase D t p).app i ≫ t.app i = f ≫ q
  rw [← Category.assoc, PhilipponPullbackLimit.cone_first, Category.assoc, ha i, hf]

omit [QuasiSeparated p] [∀ i, QuasiSeparatedSpace (D.obj i)] in
include hc in
/-- Two morphisms over the base which agree after passage to the limit
already agree at a stage of the diagram. -/
theorem exists_equalizer_stage {W : Scheme.{u}} (q : W ⟶ S) [LocallyOfFiniteType q] {i : I}
    (f g : pullback (t.app i) p ⟶ W)
    (hf : f ≫ q = pullback.fst (t.app i) p ≫ t.app i)
    (hg : g ≫ q = pullback.fst (t.app i) p ≫ t.app i)
    (h : (cone D t a ha p).π.app i ≫ f = (cone D t a ha p).π.app i ≫ g) :
    ∃ (j : I) (e : j ⟶ i), (diagram D t p).map e ≫ f = (diagram D t p).map e ≫ g := by
  let E := diagram D t p
  let f' : E.obj i ⟶ W := f
  let g' : E.obj i ⟶ W := g
  exact Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType E (overS D t p) q
    (cone D t a ha p) (isLimit D hc t a ha p) (i := i) f' g' hf.symm hg.symm h

include hc in
/-- A map between two pullbacks over the limit base is the pullback of
a map over some stage. -/
theorem exists_pullback_morphism {W : Scheme.{u}} (q : W ⟶ S) [LocallyOfFinitePresentation q]
    (f : pullback a p ⟶ pullback a q) (hf : f ≫ pullback.fst a q = pullback.fst a p) :
    ∃ (i : I) (g : pullback (t.app i) p ⟶ pullback (t.app i) q),
      g ≫ pullback.fst (t.app i) q = pullback.fst (t.app i) p ∧
      (cone D t a ha p).π.app i ≫ g = f ≫ (cone D t a ha q).π.app i := by
  have hq : (f ≫ pullback.snd a q) ≫ q = pullback.fst a p ≫ a := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hf]
  obtain ⟨i, m, hm, hc'⟩ := exists_morphism D hc t a ha p q (f ≫ pullback.snd a q) hq
  let g := pullback.lift (pullback.fst (t.app i) p) m hc'.symm
  refine ⟨i, g, pullback.lift_fst .., ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, show g ≫ pullback.fst (t.app i) q = _ from pullback.lift_fst ..,
      projection_fst D t a ha p i, Category.assoc, projection_fst D t a ha q i, reassoc_of% hf]
  · rw [Category.assoc, show g ≫ pullback.snd (t.app i) q = m from pullback.lift_snd ..,
      hm, Category.assoc, projection_snd D t a ha q i]

omit [QuasiSeparated p] [∀ i, QuasiSeparatedSpace (D.obj i)] in
include hc in
/-- Equality of maps between two stage pullbacks descends along a
transition of the diagram. -/
theorem exists_pullback_equalizer_stage {W : Scheme.{u}} (q : W ⟶ S) [LocallyOfFiniteType q] {i : I}
    (f g : pullback (t.app i) p ⟶ pullback (t.app i) q)
    (hf : f ≫ pullback.fst (t.app i) q = pullback.fst (t.app i) p)
    (hg : g ≫ pullback.fst (t.app i) q = pullback.fst (t.app i) p)
    (h : (cone D t a ha p).π.app i ≫ f = (cone D t a ha p).π.app i ≫ g) :
    ∃ (j : I) (e : j ⟶ i), (diagram D t p).map e ≫ f = (diagram D t p).map e ≫ g := by
  let r := pullback.snd (t.app i) q
  have hcomm : r ≫ q = pullback.fst (t.app i) q ≫ t.app i := pullback.condition.symm
  obtain ⟨j, e, he⟩ := exists_equalizer_stage D hc t a ha p q (f ≫ r) (g ≫ r)
    (by rw [Category.assoc, hcomm, reassoc_of% hf]) (by rw [Category.assoc, hcomm, reassoc_of% hg])
    (by rw [← Category.assoc, h, Category.assoc])
  refine ⟨j, e, pullback.hom_ext ?_ ?_⟩
  · simp only [Category.assoc, hf, hg]
  · exact he

end Finite

section Restriction

variable {W : Scheme.{u}} (q : W ⟶ S) {i j : I} (e : i ⟶ j)
  (f : pullback (t.app j) p ⟶ pullback (t.app j) q)
  (hf : f ≫ pullback.fst (t.app j) q = pullback.fst (t.app j) p)

/-- Pull a map over a stage back along a transition map. -/
def restrictMorphism : pullback (t.app i) p ⟶ pullback (t.app i) q :=
  pullback.lift (pullback.fst (t.app i) p) ((diagram D t p).map e ≫ f ≫ pullback.snd (t.app j) q) (by
    rw [Category.assoc, Category.assoc, ← pullback.condition, reassoc_of% hf, transition_fst_assoc]
    have he : D.map e ≫ t.app j = t.app i := (t.naturality e).trans (Category.comp_id _)
    rw [he])

@[reassoc]
theorem restrictMorphism_fst : restrictMorphism D t p q e f hf ≫ pullback.fst (t.app i) q =
    pullback.fst (t.app i) p := pullback.lift_fst ..

@[reassoc]
theorem restrictMorphism_snd : restrictMorphism D t p q e f hf ≫ pullback.snd (t.app i) q =
    (diagram D t p).map e ≫ f ≫ pullback.snd (t.app j) q := pullback.lift_snd ..

@[reassoc]
theorem restrictMorphism_comp_transition :
    restrictMorphism D t p q e f hf ≫ (diagram D t q).map e = (diagram D t p).map e ≫ f := by
  apply pullback.hom_ext
  · change (_ ≫ _) ≫ pullback.fst (t.app j) q = (_ ≫ _) ≫ pullback.fst (t.app j) q
    rw [Category.assoc, transition_fst D t q e, restrictMorphism_fst_assoc, Category.assoc, hf,
      transition_fst D t p e]
  · change (_ ≫ _) ≫ pullback.snd (t.app j) q = (_ ≫ _) ≫ pullback.snd (t.app j) q
    rw [Category.assoc, transition_snd D t q e, restrictMorphism_snd, Category.assoc]

theorem restrictMorphism_projection (F : pullback a p ⟶ pullback a q)
    (hF : F ≫ pullback.fst a q = pullback.fst a p)
    (h : (cone D t a ha p).π.app j ≫ f = F ≫ (cone D t a ha q).π.app j) :
    (cone D t a ha p).π.app i ≫ restrictMorphism D t p q e f hf = F ≫ (cone D t a ha q).π.app i := by
  apply pullback.hom_ext
  · rw [Category.assoc, restrictMorphism_fst, projection_fst D t a ha p i, Category.assoc,
      projection_fst D t a ha q i, reassoc_of% hF]
  · rw [Category.assoc, restrictMorphism_snd, ← Category.assoc, Cone.w, reassoc_of% h,
      projection_snd D t a ha q j, Category.assoc, projection_snd D t a ha q i]

end Restriction

private theorem restrictMorphism_inv {W : Scheme.{u}} (q : W ⟶ S) {i j : I} (e : i ⟶ j)
    (f : pullback (t.app j) p ⟶ pullback (t.app j) q)
    (g : pullback (t.app j) q ⟶ pullback (t.app j) p)
    (hf : f ≫ pullback.fst (t.app j) q = pullback.fst (t.app j) p)
    (hg : g ≫ pullback.fst (t.app j) p = pullback.fst (t.app j) q)
    (h : (diagram D t p).map e ≫ (f ≫ g) = (diagram D t p).map e) :
    restrictMorphism D t p q e f hf ≫ restrictMorphism D t q p e g hg = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, restrictMorphism_fst, restrictMorphism_fst, Category.id_comp]
  · have hs := congrArg (fun k => k ≫ pullback.snd (t.app j) p) h
    simp only [Category.assoc] at hs
    rw [Category.assoc, restrictMorphism_snd, restrictMorphism_comp_transition_assoc,
      hs, transition_snd D t p e, Category.id_comp]

section Iso

variable [IsCofiltered I] [QuasiCompact p] [QuasiSeparated p] [LocallyOfFinitePresentation p]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

include hc in
/-- An isomorphism between two finitely presented models after
base change to the limit descends to an isomorphism at some stage. -/
theorem exists_pullback_iso {W : Scheme.{u}} (q : W ⟶ S) [QuasiCompact q] [QuasiSeparated q]
    [LocallyOfFinitePresentation q]
    (F : pullback a p ≅ pullback a q) (hF : F.hom ≫ pullback.fst a q = pullback.fst a p) :
    ∃ (i : I) (G : pullback (t.app i) p ≅ pullback (t.app i) q),
      G.hom ≫ pullback.fst (t.app i) q = pullback.fst (t.app i) p ∧
      (cone D t a ha p).π.app i ≫ G.hom = F.hom ≫ (cone D t a ha q).π.app i := by
  have hF' : F.inv ≫ pullback.fst a p = pullback.fst a q := by
    rw [← hF, Iso.inv_hom_id_assoc]
  obtain ⟨i, x, hx, hx'⟩ := exists_pullback_morphism D hc t a ha p q F.hom hF
  obtain ⟨j, y, hy, hy'⟩ := exists_pullback_morphism D hc t a ha q p F.inv hF'
  let k := IsCofiltered.min i j
  let f := restrictMorphism D t p q (IsCofiltered.minToLeft i j) x hx
  let g := restrictMorphism D t q p (IsCofiltered.minToRight i j) y hy
  have hf : f ≫ pullback.fst (t.app k) q = pullback.fst (t.app k) p := restrictMorphism_fst ..
  have hg : g ≫ pullback.fst (t.app k) p = pullback.fst (t.app k) q := restrictMorphism_fst ..
  have hf' : (cone D t a ha p).π.app k ≫ f = F.hom ≫ (cone D t a ha q).π.app k :=
    restrictMorphism_projection D t a ha p q _ x hx F.hom hF hx'
  have hg' : (cone D t a ha q).π.app k ≫ g = F.inv ≫ (cone D t a ha p).π.app k :=
    restrictMorphism_projection D t a ha q p _ y hy F.inv hF' hy'
  have hfg : (cone D t a ha p).π.app k ≫ (f ≫ g) = (cone D t a ha p).π.app k := by
    rw [← Category.assoc, hf', Category.assoc, hg', Iso.hom_inv_id_assoc]
  have hgf : (cone D t a ha q).π.app k ≫ (g ≫ f) = (cone D t a ha q).π.app k := by
    rw [← Category.assoc, hg', Category.assoc, hf', Iso.inv_hom_id_assoc]
  obtain ⟨l, e, he⟩ := exists_pullback_equalizer_stage D hc t a ha p p (i := k) (f ≫ g) (𝟙 _)
    (by rw [Category.assoc, hg, hf]) (Category.id_comp _)
    (hfg.trans (Category.comp_id _).symm)
  obtain ⟨m, d, hd⟩ := exists_pullback_equalizer_stage D hc t a ha q q (i := k) (g ≫ f) (𝟙 _)
    (by rw [Category.assoc, hf, hg]) (Category.id_comp _)
    (hgf.trans (Category.comp_id _).symm)
  have he' : (diagram D t p).map e ≫ (f ≫ g) = (diagram D t p).map e := he.trans (Category.comp_id _)
  have hd' : (diagram D t q).map d ≫ (g ≫ f) = (diagram D t q).map d := hd.trans (Category.comp_id _)
  obtain ⟨n, u, v, huv⟩ := IsCofiltered.cospan e d
  let r := u ≫ e
  have h₁ : (diagram D t p).map r ≫ (f ≫ g) = (diagram D t p).map r := by
    rw [show r = u ≫ e from rfl, Functor.map_comp, Category.assoc, he']
  have h₂ : (diagram D t q).map r ≫ (g ≫ f) = (diagram D t q).map r := by
    rw [show r = v ≫ d from huv, Functor.map_comp, Category.assoc, hd']
  let G : pullback (t.app n) p ≅ pullback (t.app n) q :=
    ⟨restrictMorphism D t p q r f hf, restrictMorphism D t q p r g hg,
      restrictMorphism_inv D t p q r f g hf hg h₁, restrictMorphism_inv D t q p r g f hg hf h₂⟩
  exact ⟨n, G, restrictMorphism_fst D t p q r f hf,
    restrictMorphism_projection D t a ha p q r f hf F.hom hF hf'⟩

end Iso

section OverStage

variable [IsCofiltered I] [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

include hc in
/-- Two schemes of finite presentation over a fixed stage which become
isomorphic over the limit are isomorphic after a common transition. -/
theorem exists_later_pullback_iso {i : I} {Y Z : Scheme.{u}}
    (p : Y ⟶ D.obj i) (q : Z ⟶ D.obj i)
    [QuasiCompact p] [QuasiSeparated p] [LocallyOfFinitePresentation p]
    [QuasiCompact q] [QuasiSeparated q] [LocallyOfFinitePresentation q]
    (F : pullback (c.π.app i) p ≅ pullback (c.π.app i) q)
    (hF : F.hom ≫ pullback.fst (c.π.app i) q = pullback.fst (c.π.app i) p) :
    ∃ (j : I) (f : j ⟶ i) (G : pullback (D.map f) p ≅ pullback (D.map f) q),
      G.hom ≫ pullback.fst (D.map f) q = pullback.fst (D.map f) p := by
  let E := Over.forget i ⋙ D
  let d := c.whisker (Over.forget i)
  have hd : IsLimit d := (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  let t : E ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    { app j := D.map j.hom
      naturality j j' f := by
        change D.map f.left ≫ D.map j'.hom = D.map j.hom ≫ 𝟙 _
        rw [← Functor.map_comp, Over.w f, Category.comp_id] }
  have h (j : Over i) : d.π.app j ≫ t.app j = c.π.app i := c.w j.hom
  have (j : Over i) : CompactSpace (E.obj j) := inferInstanceAs (CompactSpace (D.obj j.left))
  have (j : Over i) : QuasiSeparatedSpace (E.obj j) := inferInstanceAs (QuasiSeparatedSpace (D.obj j.left))
  have {j j' : Over i} (f : j ⟶ j') : IsAffineHom (E.map f) := inferInstanceAs (IsAffineHom (D.map f.left))
  obtain ⟨j, G, eq, _⟩ := exists_pullback_iso E hd t (c.π.app i) h p q F hF
  exact ⟨j.left, j.hom, G, eq⟩

end OverStage

end PhilipponFiniteMorphismLimitDescent

end

section

set_option maxHeartbeats 1000000


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite


namespace PhilipponEtaleRefinementAffine

universe u

section Algebra

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

private abbrev stage (s : Finset A) := Algebra.adjoin R (s : Set A)

/-- The rings generated by finite subsets of an algebra form a directed
diagram with inclusion as transition maps. -/
def finiteSubalgebraDiagram : Finset A ⥤ CommRingCat.{u} where
  obj s := CommRingCat.of (stage R A s)
  map h := CommRingCat.ofHom (Subalgebra.inclusion
    (Algebra.adjoin_mono (Finset.coe_subset.mpr (leOfHom h)))).toRingHom
  map_id s := by ext x; rfl
  map_comp f g := by ext x; rfl

def finiteSubalgebraCocone : Cocone (finiteSubalgebraDiagram R A) where
  pt := CommRingCat.of A
  ι.app s := CommRingCat.ofHom (stage R A s).val.toRingHom
  ι.naturality _ _ f := by ext x; rfl

def structureMaps : (Functor.const (Finset A)).obj (CommRingCat.of R) ⟶
    finiteSubalgebraDiagram R A where
  app s := CommRingCat.ofHom (algebraMap R (stage R A s))
  naturality _ _ f := by ext x; rfl

def finiteSubalgebraIsColimit : IsColimit (finiteSubalgebraCocone R A) := by
  classical
  let F := finiteSubalgebraDiagram R A
  let forgetRing := forget CommRingCat.{u}
  have : ReflectsColimit F forgetRing := reflectsColimit_of_reflectsIsomorphisms F forgetRing
  apply isColimitOfReflects forgetRing
  apply Types.FilteredColimit.isColimitOf
  · intro a
    let s : Finset A := {a}
    refine ⟨s, ⟨a, Algebra.subset_adjoin ?_⟩, rfl⟩
    simp [s]
  · intro s t a b h
    let v := s ∪ t
    have hs : s ≤ v := Finset.subset_union_left
    have ht : t ≤ v := Finset.subset_union_right
    refine ⟨v, homOfLE hs, homOfLE ht, ?_⟩
    exact Subtype.ext h

end Algebra

end PhilipponEtaleRefinementAffine

end

section

set_option maxHeartbeats 1000000


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleRefinementAffine (finiteSubalgebraDiagram finiteSubalgebraCocone
  finiteSubalgebraIsColimit structureMaps)


namespace PhilipponParameterSystem

universe u

variable (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]

abbrev StageIndex := (Finset C)ᵒᵖ

abbrev stageRing (i : StageIndex C) : Subalgebra A C := Algebra.adjoin A (↑i.unop : Set C)

abbrev diagram : StageIndex C ⥤ Scheme.{u} := (finiteSubalgebraDiagram A C).op ⋙ Scheme.Spec

abbrev cone : Cone (diagram A C) := Scheme.Spec.mapCone (finiteSubalgebraCocone A C).op

def isLimit : IsLimit (cone A C) := isLimitOfPreserves Scheme.Spec (finiteSubalgebraIsColimit A C).op

abbrev limitToBase := Spec.map (CommRingCat.ofHom (algebraMap A C))

def stagesToBase : diagram A C ⟶ (Functor.const (StageIndex C)).obj (Spec (.of A)) where
  app i := Spec.map ((structureMaps A C).app i.unop)
  naturality i j f := by
    change Spec.map ((finiteSubalgebraDiagram A C).map f.unop) ≫
      Spec.map ((structureMaps A C).app j.unop) = Spec.map ((structureMaps A C).app i.unop) ≫ 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp]
    congr 1

theorem projection_toBase (i : StageIndex C) :
    (cone A C).π.app i ≫ (stagesToBase A C).app i = limitToBase A C := by
  change Spec.map ((finiteSubalgebraCocone A C).ι.app i.unop) ≫
    Spec.map ((structureMaps A C).app i.unop) = _
  rw [← Spec.map_comp]
  congr 1

instance stage_isAffine (i : StageIndex C) : IsAffine ((diagram A C).obj i) :=
  inferInstanceAs (IsAffine (Spec (.of (stageRing A C i))))

instance transition_isAffine {i j : StageIndex C} (f : i ⟶ j) : IsAffineHom ((diagram A C).map f) :=
  inferInstanceAs (IsAffineHom (Spec.map ((finiteSubalgebraDiagram A C).map f.unop)))

instance stage_finiteType (i : StageIndex C) : Algebra.FiniteType A (stageRing A C i) :=
  (stageRing A C i).fg_iff_finiteType.mp ⟨i.unop, rfl⟩

variable {X : Scheme.{u}} (g : X ⟶ Spec (.of A))

abbrev schemes := PhilipponFiniteMorphismLimitDescent.diagram (diagram A C) (stagesToBase A C) g

abbrev schemeCone :=
  PhilipponFiniteMorphismLimitDescent.cone (diagram A C) (c := cone A C) (stagesToBase A C)
    (limitToBase A C) (projection_toBase A C) g

abbrev toX := PhilipponFiniteMorphismLimitDescent.toModel (diagram A C) (stagesToBase A C) g

abbrev toRing := PhilipponFiniteMorphismLimitDescent.toBase (diagram A C) (stagesToBase A C) g

def schemeIsLimit : IsLimit (schemeCone A C g) :=
  PhilipponFiniteMorphismLimitDescent.isLimit (diagram A C) (isLimit A C) (stagesToBase A C)
    (limitToBase A C) (projection_toBase A C) g

theorem schemeProjection_isPullback (i : StageIndex C) :
    IsPullback (pullback.fst (limitToBase A C) g) ((schemeCone A C g).π.app i)
      ((cone A C).π.app i) ((toRing A C g).app i) :=
  (PhilipponFiniteMorphismLimitDescent.projection_isPullback (diagram A C) (c := cone A C) (stagesToBase A C)
    (limitToBase A C) (projection_toBase A C) g i).flip

theorem schemeTransition_isPullback {i j : StageIndex C} (f : i ⟶ j) :
    IsPullback ((toRing A C g).app i) ((schemes A C g).map f)
      ((diagram A C).map f) ((toRing A C g).app j) :=
  (PhilipponFiniteMorphismLimitDescent.transition_isPullback (diagram A C) (stagesToBase A C) g f).flip

instance schemeTransition_isAffine {i j : StageIndex C} (f : i ⟶ j) :
    IsAffineHom ((schemes A C g).map f) := MorphismProperty.of_isPullback
  (schemeTransition_isPullback A C g f) inferInstance

instance schemeStage_isAffine (i : StageIndex C) [IsAffine X] : IsAffine ((schemes A C g).obj i) := by
  let : IsAffineHom ((stagesToBase A C).app i) := inferInstanceAs
    (IsAffineHom (Spec.map ((structureMaps A C).app i.unop)))
  let : IsAffineHom (pullback.snd ((stagesToBase A C).app i) g) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) inferInstance
  exact isAffine_of_isAffineHom (pullback.snd ((stagesToBase A C).app i) g)

end PhilipponParameterSystem

end

section

set_option maxHeartbeats 1000000


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleRefinementAffine (finiteSubalgebraDiagram finiteSubalgebraCocone
  finiteSubalgebraIsColimit structureMaps)


namespace PhilipponAffineFiniteEtaleParameters

universe u

private theorem isPullback_specPushout {A B C : CommRingCat.{u}} (a : A ⟶ C) (b : A ⟶ B)
    {X : Scheme.{u}} (g : X ⟶ Spec A) (e : X ≅ Spec B) (he : e.inv ≫ g = Spec.map b) :
    IsPullback (Spec.map (pushout.inr a b) ≫ e.inv) (Spec.map (pushout.inl a b)) g (Spec.map a) := by
  refine ((IsPushout.of_hasPushout a b).op.map Scheme.Spec).of_iso
    (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simpa using he.symm
  · simp

section Stage

open PhilipponParameterSystem

variable (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]
  {X : Scheme.{u}} (g : X ⟶ Spec (.of A)) [IsAffine X]

/-- A finite étale morphism to a scalar extension of an affine scheme
descends to a stage of the finite-subalgebra system. -/
theorem exists_affine_stage {Y : Scheme.{u}} (f : Y ⟶ (schemeCone A C g).pt) [IsFinite f] [Etale f] :
    ∃ (i : StageIndex C) (Yᵢ : Scheme.{u}) (fᵢ : Yᵢ ⟶ (schemes A C g).obj i) (q : Y ⟶ Yᵢ),
      IsFinite fᵢ ∧ Etale fᵢ ∧ IsPullback f q ((schemeCone A C g).π.app i) fᵢ := by
  let e := X.isoSpec
  obtain ⟨b, hb⟩ := Spec.map_surjective (e.inv ≫ g)
  let F := finiteSubalgebraDiagram A C
  let c := finiteSubalgebraCocone A C
  let s := structureMaps A C
  let a : CommRingCat.of A ⟶ c.pt := CommRingCat.ofHom (algebraMap A C)
  have hs (i : Finset C) : s.app i ≫ c.ι.app i = a := CommRingCat.hom_ext rfl
  let h := (isPullback_specPushout a b g e hb.symm).flip
  let p := h.isoPullback
  let w : Y ⟶ Spec (pushout a b) := f ≫ p.inv
  let : IsFinite w := inferInstanceAs (IsFinite (f ≫ p.inv))
  let : Etale w := inferInstanceAs (Etale (f ≫ p.inv))
  obtain ⟨i, U, v, q, hfin, het, hq⟩ :=
    PhilipponEtaleAffineLimitDescent.exists_finite_etale_model_of_pushout F
      (finiteSubalgebraIsColimit A C) b s a hs w
  let hᵢ := (isPullback_specPushout (s.app i) b g e hb.symm).flip
  let pᵢ := hᵢ.isoPullback
  let d := pushout.map (s.app i) b a b (c.ι.app i) (𝟙 _) (𝟙 _)
    (by simpa using hs i) (by simp)
  let r : (schemeCone A C g).pt ⟶ (schemes A C g).obj (op i) := (schemeCone A C g).π.app (op i)
  have hproj : p.hom ≫ r = Spec.map d ≫ pᵢ.hom := by
    apply pullback.hom_ext
    · have hinl : pushout.inl (s.app i) b ≫ d = c.ι.app i ≫ pushout.inl a b := by simp [d]
      have hr : r ≫ pullback.fst (Spec.map (s.app i)) g =
          pullback.fst (Spec.map a) g ≫ Spec.map (c.ι.app i) :=
        PhilipponFiniteMorphismLimitDescent.projection_fst (diagram A C) (c := cone A C)
          (stagesToBase A C) _ (projection_toBase A C) g (op i)
      simp only [Category.assoc]
      change p.hom ≫ (r ≫ pullback.fst (Spec.map (s.app i)) g) =
        Spec.map d ≫ (pᵢ.hom ≫ pullback.fst (Spec.map (s.app i)) g)
      rw [hr, ← Category.assoc p.hom, h.isoPullback_hom_fst, hᵢ.isoPullback_hom_fst,
        ← Spec.map_comp, ← Spec.map_comp, hinl]
    · have hinr : pushout.inr (s.app i) b ≫ d = pushout.inr a b := by simp [d]
      have hr : r ≫ pullback.snd (Spec.map (s.app i)) g = pullback.snd (Spec.map a) g :=
        PhilipponFiniteMorphismLimitDescent.projection_snd (diagram A C) (c := cone A C)
          (stagesToBase A C) _ (projection_toBase A C) g (op i)
      simp only [Category.assoc]
      change p.hom ≫ (r ≫ pullback.snd (Spec.map (s.app i)) g) =
        Spec.map d ≫ (pᵢ.hom ≫ pullback.snd (Spec.map (s.app i)) g)
      rw [hr, h.isoPullback_hom_snd, hᵢ.isoPullback_hom_snd, ← Spec.map_comp_assoc, hinr]
  let : IsFinite v := hfin
  let : Etale v := het
  refine ⟨op i, U, v ≫ pᵢ.hom, q, inferInstance, inferInstance, ?_⟩
  exact hq.of_iso (Iso.refl _) p (Iso.refl _) pᵢ (by simp [w]) (by simp) hproj.symm (by simp)

end Stage
end PhilipponAffineFiniteEtaleParameters

end

section

set_option maxHeartbeats 1000000


set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponEtalePropertiesAtStage

universe u

section Diagram

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) {c : Cone D} (hc : IsLimit c)
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
  [∀ {i j} (e : i ⟶ j), IsAffineHom (D.map e)]
  {X Y : Scheme.{u}} (t : D ⟶ (Functor.const I).obj X) (a : c.pt ⟶ X)
  (ha : ∀ i, c.π.app i ≫ t.app i = a) (f : Y ⟶ X)
  [QuasiCompact f] [QuasiSeparated f] [LocallyOfFinitePresentation f]

include hc ha in
/-- If the limit of a pullback model also has a finite étale model at a
stage, then the given model becomes finite étale at some later stage. -/
theorem exists_finite_etale_stage_of_model {i : I} {Z : Scheme.{u}}
    (q : Z ⟶ D.obj i) [IsFinite q] [Etale q] (r : pullback a f ⟶ Z)
    (hr : IsPullback (pullback.fst a f) r (c.π.app i) q) :
    ∃ j : I, IsFinite (pullback.fst (t.app j) f) ∧ Etale (pullback.fst (t.app j) f) := by
  let p := pullback.fst (t.app i) f
  let h := (PhilipponFiniteMorphismLimitDescent.projection_isPullback D t a ha f i).flip
  let F := h.isoPullback.symm ≪≫ hr.isoPullback
  have hF : F.hom ≫ pullback.fst (c.π.app i) q = pullback.fst (c.π.app i) p := by
    change (h.isoPullback.inv ≫ hr.isoPullback.hom) ≫ pullback.fst (c.π.app i) q = _
    rw [Category.assoc, hr.isoPullback_hom_fst, h.isoPullback_inv_fst]
  let : QuasiCompact p := inferInstanceAs (QuasiCompact (pullback.fst (t.app i) f))
  let : QuasiSeparated p := inferInstanceAs (QuasiSeparated (pullback.fst (t.app i) f))
  let : LocallyOfFinitePresentation p := inferInstanceAs (LocallyOfFinitePresentation (pullback.fst (t.app i) f))
  obtain ⟨j, e, G, hG⟩ := PhilipponFiniteMorphismLimitDescent.exists_later_pullback_iso D hc p q F hF
  let k := (PhilipponFiniteMorphismLimitDescent.transition_isPullback D t f e).flip
  let H := k.isoPullback ≪≫ G
  have hH : H.hom ≫ pullback.fst (D.map e) q = pullback.fst (t.app j) f := by
    change (k.isoPullback.hom ≫ G.hom) ≫ pullback.fst (D.map e) q = _
    rw [Category.assoc, hG, k.isoPullback_hom_fst]
  refine ⟨j, ?_, ?_⟩ <;> rw [← hH] <;> infer_instance

end Diagram

open PhilipponParameterSystem

variable (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]
  {X Y : Scheme.{u}} (g : X ⟶ Spec (.of A)) [IsAffine X] (f : Y ⟶ X)
  [QuasiCompact f] [QuasiSeparated f] [LocallyOfFinitePresentation f]

/-- Over an affine chart, finiteness and étaleness of a finitely presented
morphism after scalar extension already hold at a parameter stage. -/
theorem exists_finite_etale_affine_stage
    [IsFinite (pullback.fst (pullback.snd (limitToBase A C) g) f)]
    [Etale (pullback.fst (pullback.snd (limitToBase A C) g) f)] :
    ∃ i : StageIndex C, IsFinite (pullback.fst ((toX A C g).app i) f) ∧
      Etale (pullback.fst ((toX A C g).app i) f) := by
  let D := schemes A C g
  let c := schemeCone A C g
  let t := toX A C g
  let a := pullback.snd (limitToBase A C) g
  have h (i : StageIndex C) : c.π.app i ≫ t.app i = a :=
    PhilipponFiniteMorphismLimitDescent.projection_snd (diagram A C) (c := cone A C)
      (stagesToBase A C) _ (projection_toBase A C) g i
  have (i : StageIndex C) : IsAffine (D.obj i) := schemeStage_isAffine A C g i
  have (i : StageIndex C) : CompactSpace (D.obj i) := inferInstance
  have (i : StageIndex C) : QuasiSeparatedSpace (D.obj i) := inferInstance
  have {i j : StageIndex C} (e : i ⟶ j) : IsAffineHom (D.map e) := schemeTransition_isAffine A C g e
  obtain ⟨i, Z, q, r, hfin, het, hr⟩ :=
    PhilipponAffineFiniteEtaleParameters.exists_affine_stage A C g (pullback.fst a f)
  let : IsFinite q := hfin
  let : Etale q := het
  exact exists_finite_etale_stage_of_model D (schemeIsLimit A C g) t a h f q r hr

end PhilipponEtalePropertiesAtStage

end

section

set_option maxHeartbeats 1000000


set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponParameterSystem


namespace PhilipponEtalePropertySpread

universe u

section Chart

variable {S T X U Y : Scheme.{u}} (g : X ⟶ S) (i : U ⟶ X) (a : T ⟶ S)

private abbrev chartMap : pullback a (i ≫ g) ⟶ pullback a g :=
  pullback.map a (i ≫ g) a g (𝟙 _) i (𝟙 _) (by simp) (by simp)

@[reassoc]
private theorem chartMap_fst : chartMap g i a ≫ pullback.fst a g = pullback.fst a (i ≫ g) := by
  simp [chartMap, pullback.map]

@[reassoc]
private theorem chartMap_snd : chartMap g i a ≫ pullback.snd a g = pullback.snd a (i ≫ g) ≫ i := by
  simp [chartMap, pullback.map]

private theorem chart_isPullback :
    IsPullback (chartMap g i a) (pullback.snd a (i ≫ g)) (pullback.snd a g) i :=
  IsPullback.of_right (h₁₂ := pullback.fst a g) (h₂₂ := g) (v₁₃ := a)
    (by rw [chartMap_fst]; exact IsPullback.of_hasPullback a (i ≫ g))
    (chartMap_snd g i a) (IsPullback.of_hasPullback a g)

private theorem chart_property_iff (f : Y ⟶ X) (P : MorphismProperty Scheme.{u}) [P.RespectsIso] :
    P (pullback.fst (pullback.snd a (i ≫ g)) (pullback.fst i f)) ↔
      P (pullback.snd (pullback.fst (pullback.snd a g) f) (chartMap g i a)) := by
  let v := pullback.snd a (i ≫ g)
  have h := (IsPullback.of_hasPullback v (pullback.fst i f)).paste_vert (IsPullback.of_hasPullback i f)
  rw [← chartMap_snd g i a] at h
  have h' := IsPullback.of_bot' h (IsPullback.of_hasPullback (pullback.snd a g) f)
  rw [← h'.flip.isoPullback_hom_snd, P.cancel_left_of_respectsIso]

private abbrev chartCover (𝒰 : X.OpenCover) : (pullback a g).OpenCover := by
  let d := pullback.snd a g
  let 𝒱 := 𝒰.pullback₁ d
  refine Scheme.Cover.copy 𝒱 𝒰.I₀ (fun i => pullback a (𝒰.f i ≫ g)) (fun i => chartMap g (𝒰.f i) a)
    (Equiv.refl _) (fun i => (chart_isPullback g (𝒰.f i) a).isoPullback) ?_
  intro i
  exact (chart_isPullback g (𝒰.f i) a).isoPullback_hom_fst.symm

end Chart

variable (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]
  {X Y : Scheme.{u}} (g : X ⟶ Spec (.of A)) (f : Y ⟶ X) [CompactSpace X]
  [QuasiCompact f] [QuasiSeparated f] [LocallyOfFinitePresentation f]

/-- A finitely presented morphism over a quasi-compact base whose scalar
extension is finite étale becomes finite étale at one parameter stage. -/
theorem exists_finite_etale_stage
    [IsFinite (pullback.fst (pullback.snd (limitToBase A C) g) f)]
    [Etale (pullback.fst (pullback.snd (limitToBase A C) g) f)] :
    ∃ i : StageIndex C, IsFinite (pullback.fst ((toX A C g).app i) f) ∧
      Etale (pullback.fst ((toX A C g).app i) f) := by
  classical
  obtain ⟨s, hs, hu⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).mp
    (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X)))
  let : Fintype s := hs.fintype
  let U (i : s) : X.Opens := i.val.val
  let 𝒰 := Scheme.openCoverOfIsOpenCover X U (by change (⨆ i, U i) = ⊤; rw [iSup_subtype]; exact hu.symm)
  let d (i : s) := (U i).ι
  let gᵢ (i : s) := d i ≫ g
  let fᵢ (i : s) := pullback.fst (d i) f
  have hlocal (i : s) : ∃ j : StageIndex C,
      IsFinite (pullback.fst ((toX A C (gᵢ i)).app j) (fᵢ i)) ∧
      Etale (pullback.fst ((toX A C (gᵢ i)).app j) (fᵢ i)) := by
    let : IsAffine ((U i).toScheme) := i.val.property
    let a := limitToBase A C
    let : IsFinite (pullback.fst (pullback.snd a (gᵢ i)) (fᵢ i)) :=
      (chart_property_iff g (d i) a f @IsFinite).mpr inferInstance
    let : Etale (pullback.fst (pullback.snd a (gᵢ i)) (fᵢ i)) :=
      (chart_property_iff g (d i) a f @Etale).mpr inferInstance
    exact PhilipponEtalePropertiesAtStage.exists_finite_etale_affine_stage A C (gᵢ i) (fᵢ i)
  choose j hfin het using hlocal
  let k : StageIndex C := op (Finset.univ.biUnion (fun i : s => (j i).unop))
  have step (i : s) : k ⟶ j i := (homOfLE (Finset.subset_biUnion_of_mem _ (Finset.mem_univ i))).op
  let a := (stagesToBase A C).app k
  let 𝒱 := chartCover g a 𝒰
  refine ⟨k, ?_, ?_⟩
  · refine (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) 𝒱).mpr fun i => ?_
    let i : s := i
    let h := PhilipponFiniteMorphismLimitDescent.transition_isPullback
      (schemes A C (gᵢ i)) (toX A C (gᵢ i)) (fᵢ i) (step i)
    exact (chart_property_iff g (d i) a f @IsFinite).mp (MorphismProperty.of_isPullback h (hfin i))
  · refine (IsZariskiLocalAtTarget.iff_of_openCover (P := @Etale) 𝒱).mpr fun i => ?_
    let i : s := i
    let h := PhilipponFiniteMorphismLimitDescent.transition_isPullback
      (schemes A C (gᵢ i)) (toX A C (gᵢ i)) (fᵢ i) (step i)
    exact (chart_property_iff g (d i) a f @Etale).mp (MorphismProperty.of_isPullback h (het i))

end PhilipponEtalePropertySpread

end

section

set_option maxHeartbeats 1000000


set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponParameterSystem


namespace PhilipponFiniteEtaleGlobalModel

universe u

private abbrev base (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

private theorem base_comp (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    base B C ≫ base A B = base A C := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq A B C]

section Scalar

variable {X S T U : Scheme.{u}} (g : X ⟶ S) {a : T ⟶ S} {b : U ⟶ S}
  (v : U ⟶ T) (h : v ≫ a = b)

private def scalarProjection : pullback g b ⟶ pullback g a :=
  pullback.lift (pullback.fst g b) (pullback.snd g b ≫ v) (by
    rw [Category.assoc, h, pullback.condition])

@[reassoc]
private theorem scalarProjection_fst : scalarProjection g v h ≫ pullback.fst g a = pullback.fst g b :=
  pullback.lift_fst ..

@[reassoc]
private theorem scalarProjection_snd : scalarProjection g v h ≫ pullback.snd g a = pullback.snd g b ≫ v :=
  pullback.lift_snd ..

private theorem scalarProjection_isPullback :
    IsPullback (scalarProjection g v h) (pullback.snd g b) (pullback.snd g a) v :=
  IsPullback.of_right (h₁₂ := pullback.fst g a) (h₂₂ := a) (v₁₃ := g)
    (by rw [scalarProjection_fst, h]; exact IsPullback.of_hasPullback g b)
    (scalarProjection_snd g v h) (IsPullback.of_hasPullback g a)

end Scalar

variable (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]
  [IsNoetherianRing A] [IsNoetherianRing C]
  {X Y : Scheme.{u}} (g : X ⟶ Spec (.of A)) [IsProper g]
  (f : Y ⟶ pullback g (base A C)) [IsFinite f]

/-- Spread a finite morphism to a finitely presented relative morphism
over a finitely generated subalgebra. The two squares retain the original
finite morphism and the structural projection to the base ring. -/
theorem exists_morphism_model :
    ∃ (R : Subalgebra A C), R.FG ∧
      ∃ (V Z : Scheme.{u}) (g₀ : Z ⟶ Spec (.of R)) (x₀ : Z ⟶ X)
        (p : V ⟶ Z) (x : pullback g (base A C) ⟶ Z) (y : Y ⟶ V),
        IsPullback x₀ g₀ g (base A R) ∧
        IsPullback x (pullback.snd g (base A C)) g₀ (base R C) ∧
        x ≫ x₀ = pullback.fst g (base A C) ∧
        IsPullback f y x p ∧ QuasiCompact p ∧ QuasiSeparated p ∧ LocallyOfFinitePresentation p := by
  let v := f ≫ pullback.snd g (base A C)
  let : IsProper v := inferInstanceAs (IsProper (f ≫ pullback.snd g (base A C)))
  let : LocallyOfFinitePresentation v := inferInstanceAs (LocallyOfFinitePresentation (f ≫ pullback.snd g (base A C)))
  obtain ⟨T, hT, _, W, q, z, hqfp, hqqc, hqqs, hY⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation (A₀ := A) v ∅
  let : LocallyOfFinitePresentation q := hqfp
  let : QuasiCompact q := hqqc
  let : QuasiSeparated q := hqqs
  let G := pullback.snd g (base A T)
  let hX := scalarProjection_isPullback g (base T C) (base_comp A T C)
  let e := hY.isoPullback
  let d := hX.isoPullback
  let m := e.inv ≫ f ≫ d.hom
  have hm : m ≫ pullback.snd G (base T C) = pullback.snd q (base T C) := by
    change (e.inv ≫ f ≫ d.hom) ≫ pullback.snd G (base T C) = _
    rw [Category.assoc, Category.assoc, hX.isoPullback_hom_snd]
    exact hY.isoPullback_inv_snd
  let : LocallyOfFinitePresentation G := inferInstanceAs (LocallyOfFinitePresentation (pullback.snd g (base A T)))
  obtain ⟨R, hR, _, p, hp, hmodel⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      q G m hm ∅
  let R' := R.restrictScalars A
  let : Algebra A R := R.algebra'
  let : IsScalarTower A T R := inferInstance
  let : Algebra.FiniteType A T := T.fg_iff_finiteType.mp hT
  let : Algebra.FiniteType T R := R.fg_iff_finiteType.mp hR
  let hRT : Algebra.FiniteType A R := Algebra.FiniteType.trans (S := T) inferInstance inferInstance
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing A R
  let k := base T R
  let l := base R C
  let r := pullback.snd q k
  let s := pullback.snd G k
  let X₀ := pullback.fst G k ≫ pullback.fst g (base A T)
  let u₁ := scalarProjection q l (base_comp T R C)
  let u₂ := scalarProjection G l (base_comp T R C)
  let Y₀ := e.hom ≫ u₁
  let X₁ := d.hom ≫ u₂
  have hu₂ : u₂ ≫ pullback.fst G k = pullback.fst G (base T C) := scalarProjection_fst ..
  have hX₀ : IsPullback X₀ s g (base A R') := by
    have h := (IsPullback.of_hasPullback G k).paste_horiz (IsPullback.of_hasPullback g (base A T))
    change IsPullback X₀ s g (base T R ≫ base A T) at h
    rw [base_comp A T R] at h
    exact h
  have hX₁ : IsPullback X₁ (pullback.snd g (base A C)) s l := by
    refine (scalarProjection_isPullback G l (base_comp T R C)).of_iso d.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ (Category.comp_id _ |>.trans (Category.id_comp _).symm)
      (Category.comp_id _ |>.trans (Category.id_comp _).symm)
    · change u₂ ≫ 𝟙 _ = d.inv ≫ (d.hom ≫ u₂)
      rw [Category.comp_id, Iso.inv_hom_id_assoc]
    · rw [Iso.refl_hom, Category.comp_id]
      exact hX.isoPullback_inv_snd.symm
  have hY₀ : IsPullback Y₀ v r l := by
    refine (scalarProjection_isPullback q l (base_comp T R C)).of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ (Category.comp_id _ |>.trans (Category.id_comp _).symm)
      (Category.comp_id _ |>.trans (Category.id_comp _).symm)
    · change u₁ ≫ 𝟙 _ = e.inv ≫ (e.hom ≫ u₁)
      rw [Category.comp_id, Iso.inv_hom_id_assoc]
    · rw [Iso.refl_hom, Category.comp_id]
      exact hY.isoPullback_inv_snd.symm
  have hcomp : X₁ ≫ X₀ = pullback.fst g (base A C) := by
    change (d.hom ≫ u₂) ≫ pullback.fst G k ≫ pullback.fst g (base A T) = _
    rw [Category.assoc, reassoc_of% hu₂, ← Category.assoc d.hom, hX.isoPullback_hom_fst]
    exact scalarProjection_fst ..
  have hcomm : f ≫ X₁ = Y₀ ≫ p := by
    have H := hmodel u₁ u₂ (scalarProjection_fst ..) (scalarProjection_snd ..)
      (scalarProjection_fst ..) (scalarProjection_snd ..)
    change f ≫ d.hom ≫ u₂ = (e.hom ≫ u₁) ≫ p
    rw [Category.assoc, H]
    simp [m]
  have hpull : IsPullback f Y₀ X₁ p := by
    apply IsPullback.of_right (h₁₂ := pullback.snd g (base A C)) (h₂₂ := s) (v₁₃ := l)
    · rw [hp]
      exact hY₀.flip
    · exact hcomm
    · exact hX₁.flip
  let : QuasiCompact r := inferInstanceAs (QuasiCompact (pullback.snd q k))
  let : QuasiSeparated r := inferInstanceAs (QuasiSeparated (pullback.snd q k))
  let : LocallyOfFiniteType r := inferInstanceAs (LocallyOfFiniteType (pullback.snd q k))
  let : IsProper s := inferInstanceAs (IsProper (pullback.snd (pullback.snd g (base A T)) k))
  let : IsLocallyNoetherian (pullback G k) := LocallyOfFiniteType.isLocallyNoetherian s
  let : QuasiCompact (p ≫ s) := hp.symm ▸ inferInstanceAs (QuasiCompact r)
  let : QuasiSeparated (p ≫ s) := hp.symm ▸ inferInstanceAs (QuasiSeparated r)
  let : LocallyOfFiniteType (p ≫ s) := hp.symm ▸ inferInstanceAs (LocallyOfFiniteType r)
  let : LocallyOfFiniteType p := locallyOfFiniteType_of_comp p s
  exact ⟨R', R'.fg_iff_finiteType.mpr hRT, _, _, s, X₀, p, X₁, Y₀, hX₀, hX₁,
    hcomp, hpull, QuasiCompact.of_comp p s, QuasiSeparated.of_comp p s, inferInstance⟩

/-- A finite étale cover after scalar extension descends to a finite étale
cover over a finitely generated subalgebra of the scalar extension. -/
theorem exists_finite_etale_model [Etale f] :
    ∃ (R : Subalgebra A C), R.FG ∧
      ∃ (V : Scheme.{u}) (p : V ⟶ pullback g (base A R)) (x : pullback g (base A C) ⟶ pullback g (base A R))
        (y : Y ⟶ V),
        x ≫ pullback.fst g (base A R) = pullback.fst g (base A C) ∧
        x ≫ pullback.snd g (base A R) = pullback.snd g (base A C) ≫ base R C ∧
        IsFinite p ∧ Etale p ∧ IsPullback f y x p := by
  obtain ⟨R, hR, V, Z, s, z, p, x, y, hZ, hX, hx, hY, hq, hqs, hfp⟩ := exists_morphism_model A C g f
  let : QuasiCompact p := hq
  let : QuasiSeparated p := hqs
  let : LocallyOfFinitePresentation p := hfp
  let : IsProper s := MorphismProperty.of_isPullback hZ inferInstance
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace s
  let : Algebra.FiniteType A R := R.fg_iff_finiteType.mp hR
  let a := base R C
  let e := hX.flip.isoPullback
  have he : IsPullback (f ≫ e.hom) y (pullback.snd a s) p := by
    refine hY.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_ (by simp)
    rw [Iso.refl_hom, Category.comp_id]
    exact hX.flip.isoPullback_hom_snd.symm
  let fC := pullback.fst (pullback.snd a s) p
  let : IsFinite fC := by
    have h : IsFinite (f ≫ e.hom) := inferInstance
    rwa [← he.isoPullback_hom_fst, MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)] at h
  let : Etale fC := by
    have h : Etale (f ≫ e.hom) := inferInstance
    rwa [← he.isoPullback_hom_fst, MorphismProperty.cancel_left_of_respectsIso (P := @Etale)] at h
  obtain ⟨i, hi, hi'⟩ := PhilipponEtalePropertySpread.exists_finite_etale_stage R C s p
  let B := stageRing R C i
  let B' := B.restrictScalars A
  let : Algebra A B := B.algebra'
  let : IsScalarTower A R B := inferInstance
  let : Algebra.FiniteType R B := stage_finiteType R C i
  let hBT : Algebra.FiniteType A B := Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  let b := (stagesToBase R C).app i
  let d := pullback.snd b s
  let r := pullback.fst b s
  let α := pullback.fst d p
  let q := e.hom ≫ (schemeCone R C s).π.app i
  have hb : b = base R B := rfl
  have h₀ : IsPullback (d ≫ z) r g (base A B') := by
    have h := (IsPullback.of_hasPullback b s).flip.paste_horiz hZ
    rw [hb, base_comp A R B] at h
    exact h
  let L := h₀.isoPullback
  have hqd : q ≫ d = x := by
    have H := PhilipponFiniteMorphismLimitDescent.projection_snd (diagram R C) (c := cone R C)
      (stagesToBase R C) (limitToBase R C) (projection_toBase R C) s i
    change e.hom ≫ (schemeCone R C s).π.app i ≫ d = x
    rw [H, hX.flip.isoPullback_hom_snd]
  have hqr : q ≫ r = pullback.snd g (base A C) ≫ base B' C := by
    have H := PhilipponFiniteMorphismLimitDescent.projection_fst (diagram R C) (c := cone R C)
      (stagesToBase R C) (limitToBase R C) (projection_toBase R C) s i
    change e.hom ≫ (schemeCone R C s).π.app i ≫ r = _
    rw [H, ← Category.assoc, hX.flip.isoPullback_hom_fst]
    rfl
  have hP : IsPullback y f p (q ≫ d) := by rw [hqd]; exact hY.flip
  let u := pullback.lift (f ≫ q) y (by rw [Category.assoc, hqd, hY.w])
  have h : IsPullback u f α q :=
    IsPullback.of_right (h₁₂ := pullback.snd d p) (v₁₃ := p) (h₂₂ := d)
      (by rw [show u ≫ pullback.snd d p = y from pullback.lift_snd ..]; exact hP)
      (pullback.lift_fst ..) (IsPullback.of_hasPullback d p).flip
  let π := α ≫ L.hom
  let v := q ≫ L.hom
  have h' : IsPullback f u v π := h.flip.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) L
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
    (Category.id_comp v).symm (Category.id_comp π).symm
  let : IsFinite α := hi
  let : Etale α := hi'
  refine ⟨B', B'.fg_iff_finiteType.mpr hBT, _, π, v, u, ?_, ?_,
    inferInstanceAs (IsFinite (α ≫ L.hom)), inferInstanceAs (Etale (α ≫ L.hom)), h'⟩
  · rw [Category.assoc, h₀.isoPullback_hom_fst, ← Category.assoc, hqd, hx]
  · rw [Category.assoc, h₀.isoPullback_hom_snd, hqr]

end PhilipponFiniteEtaleGlobalModel

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponProperFinitePresentationSpread

universe u

private theorem pullback_property {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    {X Y S T : Scheme.{u}} {a : X ⟶ Y} {f : X ⟶ S} {g : Y ⟶ T} {b : S ⟶ T}
    (h : IsPullback a f g b) (hf : P f) : P (pullback.snd g b) := by
  rw [← h.isoPullback_hom_snd, P.cancel_left_of_respectsIso] at hf
  exact hf

private abbrev base (A R : Type u) [CommRing A] [CommRing R] [Algebra A R] :=
  Spec.map (CommRingCat.ofHom (algebraMap A R))

private theorem change_stage {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]
    (T : Subalgebra A R) {X Y : Scheme.{u}}
    {a : X ⟶ Y} {f : X ⟶ Spec (.of R)} {g : Y ⟶ Spec (.of A)}
    (h : IsPullback a f g (base A R)) :
    ∃ π : X ⟶ pullback g (base A T), IsPullback π f (pullback.snd g (base A T)) (base T R) := by
  have hb : base T R ≫ base A T = base A R := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have he : a ≫ g = (f ≫ base T R) ≫ base A T := by
    rw [Category.assoc, hb]
    exact h.w
  let π := pullback.lift a (f ≫ base T R) he
  refine ⟨π, IsPullback.of_right (h₁₂ := pullback.fst g (base A T)) (v₁₃ := g)
    (h₂₂ := base A T) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)⟩
  change IsPullback (pullback.lift _ _ _ ≫ pullback.fst _ _) f g (base T R ≫ base A T)
  rw [pullback.lift_fst, hb]
  exact h

/-- A proper finitely presented scheme descends to a proper model over a finitely
generated subalgebra, with a prescribed finite set of coefficients included. -/
theorem exists_proper_model {A R : Type u} [CommRing A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] [LocallyOfFinitePresentation f] (s : Finset R) :
    ∃ (T : Subalgebra A R), T.FG ∧ (↑s : Set R) ⊆ T ∧
      ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of T)) (a : X ⟶ Y),
        IsProper g ∧ IsPullback a f g (base T R) := by
  obtain ⟨B, hB, hSeed, Y₀, g₀, a₀, hfp₀, hqc₀, hqs₀, h₀⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation (A₀ := A) f s
  let _ := hfp₀
  let _ := hqc₀
  let _ := hqs₀
  let : Algebra.FiniteType A B := (Subalgebra.fg_iff_finiteType B).mp hB
  let : IsSeparated (pullback.snd g₀ (base B R)) := pullback_property (P := @IsSeparated) h₀ inferInstance
  obtain ⟨C, hC, _, hSep⟩ :=
    AlgebraicGeometry.IsSeparated.exists_fg_subalgebra_of_isSeparated_pullback_snd (A := R) g₀ ∅
  let _ := hSep
  let : Algebra.FiniteType B C := (Subalgebra.fg_iff_finiteType C).mp hC
  let : Algebra.FiniteType A C := Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  let : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
  let g₁ := pullback.snd g₀ (base B C)
  obtain ⟨a₁, h₁⟩ := change_stage C h₀
  let : QuasiCompact g₁ := MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ hqc₀
  let : LocallyOfFinitePresentation g₁ := MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ hfp₀
  let : IsProper (pullback.snd g₁ (base C R)) := pullback_property (P := @IsProper) h₁ inferInstance
  obtain ⟨D, hD, _, hProper⟩ :=
    AlgebraicGeometry.IsProper.exists_fg_subalgebra_of_isProper_pullback_snd (A := R) g₁ ∅
  obtain ⟨a₂, h₂⟩ := change_stage D h₁
  let : Algebra.FiniteType C D := (Subalgebra.fg_iff_finiteType D).mp hD
  let hFin : Algebra.FiniteType A D := Algebra.FiniteType.trans (S := C) inferInstance inferInstance
  refine ⟨D.restrictScalars A, (Subalgebra.fg_iff_finiteType _).mpr hFin, ?_, _, _, a₂, hProper, h₂⟩
  intro r hr
  let x : B := ⟨r, hSeed hr⟩
  let y : C := ⟨r, C.algebraMap_mem x⟩
  exact D.algebraMap_mem y

end PhilipponProperFinitePresentationSpread

end

section

set_option autoImplicit false

namespace PhilipponNoetherianLocalModels

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]

abbrev span (s : Finset R) := Algebra.adjoin ℤ (↑s : Set R)

abbrev center (s : Finset R) := (IsLocalRing.maximalIdeal R).comap (span s).val.toRingHom

instance (s : Finset R) : (center s).IsPrime :=
  (IsLocalRing.maximalIdeal.isMaximal R).isPrime.comap (span s).val.toRingHom

/-- The algebra generated by the chosen elements, localized at the base ring's closed point. -/
abbrev ring (s : Finset R) := Localization.AtPrime (center s)

instance (s : Finset R) : IsNoetherianRing (ring s) := by
  let S := span s
  let : Algebra.FiniteType ℤ S := (Subalgebra.fg_iff_finiteType S).mp (Subalgebra.fg_adjoin_finset s)
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  exact IsLocalization.isNoetherianRing (center s).primeCompl (ring s) inferInstance

private theorem units (s : Finset R) (t : (center s).primeCompl) :
    IsUnit ((span s).val.toRingHom t.val) := IsLocalRing.notMem_maximalIdeal.mp t.property

/-- The inclusion of the local model into the original local ring. -/
noncomputable def inclusion (s : Finset R) : ring s →+* R := IsLocalization.lift (units s)

@[simp]
theorem inclusion_algebraMap (s : Finset R) (a : span s) :
    inclusion s (algebraMap (span s) (ring s) a) = a.val := IsLocalization.lift_eq (units s) a

theorem inclusion_injective (s : Finset R) : Function.Injective (inclusion s) := by
  apply (IsLocalization.lift_injective_iff (units s)).mpr
  intro a b
  exact ⟨fun h => (inclusion_algebraMap s a).symm.trans ((congrArg (inclusion s) h).trans
    (inclusion_algebraMap s b)), fun h => congrArg (algebraMap (span s) (ring s)) (Subtype.ext h)⟩

instance (s : Finset R) : IsLocalHom (inclusion s) := by
  constructor
  intro z hz
  obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq (center s).primeCompl z
  have hl := hz.mul ((IsLocalization.map_units (ring s) t).map (inclusion s))
  rw [← map_mul, IsLocalization.mk'_spec, inclusion_algebraMap] at hl
  have hp : a ∈ (center s).primeCompl := IsLocalRing.notMem_maximalIdeal.mpr hl
  have hu := (IsLocalization.AtPrime.isUnit_to_map_iff (ring s) (center s) a).mpr hp
  rw [← IsLocalization.mk'_spec (ring s) a t] at hu
  exact (IsUnit.mul_iff.mp hu).1

theorem subset_range_inclusion (s : Finset R) : (↑s : Set R) ⊆ Set.range (inclusion s) := by
  intro r hr
  let a : span s := ⟨r, Algebra.subset_adjoin hr⟩
  exact ⟨algebraMap (span s) (ring s) a, inclusion_algebraMap s a⟩

/-- Any finite collection in a local ring is contained in the image of an
injective local map from a Noetherian local ring. -/
theorem exists_noetherian_local_model (s : Finset R) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsLocalRing A) (_ : IsNoetherianRing A)
      (f : A →+* R), Function.Injective f ∧ IsLocalHom f ∧ (↑s : Set R) ⊆ Set.range f :=
  ⟨ring s, inferInstance, inferInstance, inferInstance, inclusion s, inclusion_injective s,
    inferInstance, subset_range_inclusion s⟩

/-- A Noetherian local model can capture finite collections in the base ring
and in its residue field at the same time. -/
theorem exists_noetherian_local_model_with_residueField {R : Type u} [CommRing R] [IsLocalRing R]
    (s : Finset R) (t : Finset (IsLocalRing.ResidueField R)) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsLocalRing A) (_ : IsNoetherianRing A)
      (f : A →+* R) (hf : IsLocalHom f), Function.Injective f ∧ (↑s : Set R) ⊆ Set.range f ∧
        (let _ := hf; (↑t : Set (IsLocalRing.ResidueField R)) ⊆ Set.range (IsLocalRing.ResidueField.map f)) := by
  classical
  choose lift hl using IsLocalRing.residue_surjective (R := R)
  obtain ⟨A, hRing, hLocal, hNoeth, f, hInj, hf, hRange⟩ :=
    exists_noetherian_local_model (s ∪ t.image lift)
  let _ := hf
  refine ⟨A, hRing, hLocal, hNoeth, f, hf, hInj, ?_, ?_⟩
  · intro r hr
    exact hRange (Finset.mem_union_left _ hr)
  · change (↑t : Set (IsLocalRing.ResidueField R)) ⊆ Set.range (IsLocalRing.ResidueField.map f)
    intro r hr
    have hmem : lift r ∈ s ∪ t.image lift := Finset.mem_union_right _ (Finset.mem_image_of_mem lift hr)
    obtain ⟨a, ha⟩ := hRange hmem
    refine ⟨IsLocalRing.residue A a, ?_⟩
    rw [IsLocalRing.ResidueField.map_residue, ha, hl]

end PhilipponNoetherianLocalModels

end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open PhilipponNoetherianLocalModels (center inclusion inclusion_algebraMap inclusion_injective ring span)


namespace PhilipponNoetherianLocalDiagram

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]

private abbrev spanMap {s t : Finset R} (h : s ⊆ t) : span s →ₐ[ℤ] span t :=
  Subalgebra.inclusion (Algebra.adjoin_mono h)

private theorem complement_le_comap {S T : Subalgebra ℤ R} (h : S ≤ T) :
    ((IsLocalRing.maximalIdeal R).comap S.val.toRingHom).primeCompl ≤
      (((IsLocalRing.maximalIdeal R).comap T.val.toRingHom).primeCompl).comap
        (Subalgebra.inclusion h).toRingHom := fun _ hx => hx

/-- The transition map between local models induced by inclusion of generators. -/
def transition {s t : Finset R} (h : s ⊆ t) : ring s →+* ring t :=
  IsLocalization.map (M := (center s).primeCompl) (T := (center t).primeCompl)
    (ring t) (spanMap h).toRingHom (complement_le_comap (Algebra.adjoin_mono h))

private theorem transition_algebraMap {s t : Finset R} (h : s ⊆ t) (x : span s) :
    transition h (algebraMap (span s) (ring s) x) = algebraMap (span t) (ring t) (spanMap h x) :=
  IsLocalization.map_eq (complement_le_comap (Algebra.adjoin_mono h)) x

@[simp]
theorem inclusion_comp_transition {s t : Finset R} (h : s ⊆ t) :
    (inclusion t).comp (transition h) = inclusion s := by
  apply IsLocalization.ringHom_ext (center s).primeCompl
  ext x
  change inclusion t (transition h (algebraMap (span s) (ring s) x)) =
    inclusion s (algebraMap (span s) (ring s) x)
  rw [transition_algebraMap, inclusion_algebraMap, inclusion_algebraMap]
  rfl

private theorem inclusion_transition {s t : Finset R} (h : s ⊆ t) (x : ring s) :
    inclusion t (transition h x) = inclusion s x :=
  DFunLike.congr_fun (inclusion_comp_transition h) x

instance {s t : Finset R} (h : s ⊆ t) : IsLocalHom (transition h) where
  map_nonunit x hx := by
    apply (isUnit_map_iff (inclusion s) x).mp
    rw [← inclusion_transition h]
    exact hx.map (inclusion t)

end PhilipponNoetherianLocalDiagram

end

section

set_option autoImplicit false

namespace PhilipponHenselianStageCoefficients

open PhilipponNoetherianLocalModels
open PhilipponNoetherianLocalDiagram

universe u

/-- Polynomial approximation modulo the maximal ideal. -/
abbrev Approximates (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] : Prop :=
  let C := AdicCompletion (IsLocalRing.maximalIdeal R) R
  ∀ (n m : ℕ) (P : Fin m → MvPolynomial (Fin n) R) (x' : Fin n → C),
    (∀ k, MvPolynomial.aeval x' (P k) = 0) →
    ∃ x : Fin n → R, (∀ k, MvPolynomial.aeval x (P k) = 0) ∧
      ∀ k, IsLocalRing.residue C (x' k) = IsLocalRing.ResidueField.map (algebraMap R C)
        (IsLocalRing.residue R (x k))

/-- A family of ordinary local coefficient rings can be mapped to approximating
Noetherian henselian rings over the original base. -/
abbrev HasHenselianStages (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ t : Finset A, ∃ (R : Type u) (_ : CommRing R) (_ : HenselianLocalRing R)
    (_ : IsNoetherianRing R) (a : R →+* A) (_ : IsLocalHom a)
    (b : ring t →+* R) (_ : IsLocalHom b), a.comp b = inclusion t ∧ Approximates R

/-- Enlarging the finite coefficient set permits prescribed residue-field
coefficients to be captured in a later approximating stage. -/
theorem exists_enlargement {A : Type u} [CommRing A] [IsLocalRing A]
    (h : HasHenselianStages A) (s : Finset A) (d : Finset (IsLocalRing.ResidueField A)) :
    ∃ (R : Type u) (_ : CommRing R) (_ : HenselianLocalRing R) (_ : IsNoetherianRing R)
      (a : R →+* A) (_ : IsLocalHom a) (b : ring s →+* R) (_ : IsLocalHom b),
      a.comp b = inclusion s ∧ Approximates R ∧
        (↑d : Set (IsLocalRing.ResidueField A)) ⊆ Set.range (IsLocalRing.ResidueField.map a) := by
  classical
  choose lift hl using IsLocalRing.residue_surjective (R := A)
  let t := s ∪ d.image lift
  have hst : s ⊆ t := Finset.subset_union_left
  obtain ⟨R, hR, hH, hN, a, ha, c, hc, he, hA⟩ := h t
  let := hR
  let := hH
  let := ha
  let := hc
  let b := c.comp (transition hst)
  refine ⟨R, hR, hH, hN, a, ha, b, inferInstance, ?_, hA, ?_⟩
  · change a.comp (c.comp (transition hst)) = inclusion s
    rw [← RingHom.comp_assoc, he, inclusion_comp_transition]
  · intro x hx
    have ht : lift x ∈ t := Finset.mem_union_right _ (Finset.mem_image_of_mem lift hx)
    obtain ⟨y, hy⟩ := subset_range_inclusion t ht
    refine ⟨IsLocalRing.residue R (c y), ?_⟩
    rw [IsLocalRing.ResidueField.map_residue,
      show a (c y) = inclusion t y from DFunLike.congr_fun he y, hy, hl]

/-- Finitely generated coefficient subalgebras factor through an injective
ring map whenever the scalar ring and a generating set are in its image. -/
theorem exists_factor {K L M : Type u} [CommRing K] [CommRing L] [CommRing M] [Algebra K L]
    (B : Subalgebra K L) (p : M →+* L) (hp : Function.Injective p) (q : K →+* M)
    (hpq : p.comp q = algebraMap K L) (d : Finset L)
    (hd : Algebra.adjoin K (↑d : Set L) = B) (hr : (↑d : Set L) ⊆ Set.range p) :
    ∃ w : B →+* M, p.comp w = B.val.toRingHom ∧ w.comp (algebraMap K B) = q := by
  let D : Subalgebra K L :=
    { p.range with
      algebraMap_mem' := fun x => ⟨q x, DFunLike.congr_fun hpq x⟩ }
  have hBD : B ≤ D := by
    rw [← hd, Algebra.adjoin_le_iff]
    exact hr
  let e : M ≃+* p.range := RingEquiv.ofBijective p.rangeRestrict
    ⟨fun _ _ h => hp (congrArg Subtype.val h), p.rangeRestrict_surjective⟩
  let w := e.symm.toRingHom.comp (Subalgebra.inclusion hBD).toRingHom
  have hw : p.comp w = B.val.toRingHom := by
    ext x
    exact congrArg Subtype.val (e.apply_symm_apply ((Subalgebra.inclusion hBD) x))
  refine ⟨w, hw, ?_⟩
  ext x
  apply hp
  change (p.comp w) (algebraMap K B x) = p (q x)
  rw [hw]
  exact (DFunLike.congr_fun hpq x).symm

end PhilipponHenselianStageCoefficients

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponHenselianStageCoefficients (Approximates HasHenselianStages)
open PhilipponNoetherianLocalModels (span ring inclusion)


namespace PhilipponFiniteEtaleHenselianStage

universe u

private abbrev spec {R A : Type u} [CommRing R] [CommRing A] (a : R →+* A) :=
  Spec.map (CommRingCat.ofHom a)

private abbrev res {R A : Type u} [CommRing R] [CommRing A] [IsLocalRing R] [IsLocalRing A]
    (a : R →+* A) [IsLocalHom a] := spec (IsLocalRing.ResidueField.map a)

private theorem spec_comp {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    (b : R →+* S) (a : S →+* A) : spec a ≫ spec b = spec (a.comp b) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

private theorem residue_square {R A : Type u} [CommRing R] [CommRing A] [IsLocalRing R] [IsLocalRing A]
    (a : R →+* A) [IsLocalHom a] :
    res a ≫ spec (IsLocalRing.residue R) = spec (IsLocalRing.residue A) ≫ spec a := by
  rw [spec_comp, spec_comp, IsLocalRing.ResidueField.map_comp_residue]

private theorem factor_stage {X Y S R A : Scheme.{u}} {f : X ⟶ A} {g : Y ⟶ S}
    {x : X ⟶ Y} {a : A ⟶ R} {b : R ⟶ S} (h : IsPullback x f g (a ≫ b)) :
    ∃ v : X ⟶ pullback g b,
      v ≫ pullback.fst g b = x ∧ IsPullback v f (pullback.snd g b) a := by
  let v := pullback.lift x (f ≫ a) (by rw [Category.assoc]; exact h.w)
  have hv : v ≫ pullback.fst g b = x := pullback.lift_fst ..
  refine ⟨v, hv, IsPullback.of_right (h₁₂ := pullback.fst g b) (v₁₃ := g) (h₂₂ := b)
    (by rw [hv]; exact h) (pullback.lift_snd ..) (IsPullback.of_hasPullback _ _)⟩

private theorem exists_local_model {A : Type u} [CommRing A] [IsLocalRing A]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of A)) [IsProper g] [LocallyOfFinitePresentation g] :
    ∃ (s : Finset A) (X : Scheme.{u}) (g₀ : X ⟶ Spec (.of (ring s))) (v : Y ⟶ X),
      IsProper g₀ ∧ IsPullback v g g₀ (spec (inclusion s)) := by
  let : Algebra (ULift.{u} ℤ) A := ULift.algebra' ℤ A
  let : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  obtain ⟨B, hB, _, P, q, p, hq, hp⟩ :=
    PhilipponProperFinitePresentationSpread.exists_proper_model (A := ULift.{u} ℤ) g ∅
  obtain ⟨s, hs⟩ := hB
  let D : Subalgebra (ULift.{u} ℤ) A :=
    { (span s).toSubring with
      algebraMap_mem' := fun n => (span s).algebraMap_mem n.down }
  have hBD : B ≤ D := by
    rw [← hs, Algebra.adjoin_le_iff]
    exact fun _ hx => Algebra.subset_adjoin hx
  let m : B →+* span s := B.val.toRingHom.codRestrict (span s) (fun x => hBD x.2)
  let b := (algebraMap (span s) (ring s)).comp m
  have he : (inclusion s).comp b = B.val.toRingHom := by
    ext x
    exact PhilipponNoetherianLocalModels.inclusion_algebraMap s (m x)
  have h : IsPullback p g q (spec (inclusion s) ≫ spec b) := by
    rw [spec_comp, he]
    exact hp
  obtain ⟨v, _, hv⟩ := factor_stage h
  let := hq
  exact ⟨s, _, _, v, inferInstance, hv⟩

private theorem fiber_map {R A : Type u} [CommRing R] [CommRing A] [IsLocalRing R] [IsLocalRing A]
    (a : R →+* A) [IsLocalHom a] {X Y T : Scheme.{u}}
    {g₀ : X ⟶ Spec (.of R)} {g : Y ⟶ Spec (.of A)} {v : Y ⟶ X}
    (h : IsPullback v g g₀ (spec a))
    {s : T ⟶ Spec (.of (IsLocalRing.ResidueField A))} {j : T ⟶ Y}
    (hf : IsPullback s j (spec (IsLocalRing.residue A)) g) :
    ∃ z : T ⟶ pullback (spec (IsLocalRing.residue R)) g₀,
      z ≫ pullback.snd (spec (IsLocalRing.residue R)) g₀ = j ≫ v ∧
      IsPullback z s (pullback.fst (spec (IsLocalRing.residue R)) g₀) (res a) := by
  let r := spec (IsLocalRing.residue R)
  have h' : IsPullback (j ≫ v) s g₀ (res a ≫ r) := by
    rw [residue_square]
    exact hf.flip.paste_horiz h
  let z : T ⟶ pullback r g₀ :=
    pullback.lift (s ≫ res a) (j ≫ v) (by rw [Category.assoc]; exact h'.w.symm)
  have hz : z ≫ pullback.snd r g₀ = j ≫ v := pullback.lift_snd ..
  refine ⟨z, hz, IsPullback.of_right (h₁₂ := pullback.snd r g₀) (v₁₃ := g₀) (h₂₂ := r)
      (by rw [hz]; exact h') (pullback.lift_fst ..) (IsPullback.of_hasPullback r g₀).flip⟩

/-- The closed-fiber stage follows from polynomial approximation for
henselizations of the ordinary local coefficient models. -/
theorem exists_stage {A : Type u} [CommRing A] [HenselianLocalRing A]
    (hA : HasHenselianStages A) {Y T : Scheme.{u}} (g : Y ⟶ Spec (.of A)) [IsProper g]
    (s : T ⟶ Spec (.of (IsLocalRing.ResidueField A))) (j : T ⟶ Y)
    (h : IsPullback s j (spec (IsLocalRing.residue A)) g) (V : T.Etale) [IsFinite V.hom] :
    ∃ (R : Type u) (_ : CommRing R) (_ : HenselianLocalRing R) (_ : IsNoetherianRing R)
      (a : R →+* A) (_ : IsLocalHom a) (X : Scheme.{u}) (g₁ : X ⟶ Spec (.of R)) (_ : IsProper g₁)
      (v : Y ⟶ X),
      let r := spec (IsLocalRing.residue R)
      ∃ (z : T ⟶ pullback r g₁) (B : (pullback r g₁).Etale),
        g ≫ spec a = v ≫ g₁ ∧
        s ≫ res a = z ≫ pullback.fst r g₁ ∧
        j ≫ v = z ≫ pullback.snd r g₁ ∧
        IsFinite B.hom ∧ Nonempty ((baseChange z).obj B ≅ V) ∧ Approximates R := by
  obtain ⟨P, gP, i, hProper, hFP, _, hgi, hP⟩ :=
    AlgebraicGeometry.Scheme.exists_proper_finitePresentation_envelope_with_noetherian_baseChange g _ s j h
  let := hProper
  let := hFP
  obtain ⟨t, X₀, g₀, v₀, hg₀, h₀⟩ := exists_local_model gP
  let := hg₀
  let a₀ := inclusion t
  let k₀ := IsLocalRing.ResidueField (ring t)
  let kA := IsLocalRing.ResidueField A
  let r₀ := spec (IsLocalRing.residue (ring t))
  let q₀ := pullback.fst r₀ g₀
  let : Algebra k₀ kA := (IsLocalRing.ResidueField.map a₀).toAlgebra
  let : IsProper q₀ := inferInstanceAs (IsProper (pullback.fst r₀ g₀))
  obtain ⟨z₀, hz₀, hT⟩ := fiber_map a₀ h₀ hP
  let e := hT.isoPullback
  let f := V.hom ≫ e.hom
  let : IsFinite f := inferInstanceAs (IsFinite (V.hom ≫ e.hom))
  let : Etale f := inferInstanceAs (Etale (V.hom ≫ e.hom))
  obtain ⟨D, hD, Q, p, x, u, hx₁, hx₂, hp, hEt, hV⟩ :=
    PhilipponFiniteEtaleGlobalModel.exists_finite_etale_model k₀ kA q₀ f
  obtain ⟨d, hd⟩ := hD
  obtain ⟨R, hR, hH, hN, a, ha, b, hb, he, hApprox, hCoeffs⟩ :=
    PhilipponHenselianStageCoefficients.exists_enlargement hA t d
  let := hR
  let := hH
  let := hN
  let := ha
  let := hb
  let aK := IsLocalRing.ResidueField.map a
  let bK := IsLocalRing.ResidueField.map b
  have hK : aK.comp bK = algebraMap k₀ kA := by
    change _ = IsLocalRing.ResidueField.map a₀
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := ring t) x
    dsimp only [aK, bK, RingHom.comp_apply]
    rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue,
      IsLocalRing.ResidueField.map_residue]
    exact congrArg (IsLocalRing.residue A) (DFunLike.congr_fun he x)
  obtain ⟨w, hw, hw'⟩ := PhilipponHenselianStageCoefficients.exists_factor D aK
    aK.injective bK hK d hd hCoeffs
  have hbase : IsPullback v₀ gP g₀ (spec a ≫ spec b) := by
    rw [spec_comp, he]
    exact h₀
  obtain ⟨v₁, hv₁, h₁⟩ := factor_stage hbase
  let G := pullback.snd g₀ (spec b)
  let r := spec (IsLocalRing.residue R)
  let q := pullback.fst r G
  let : IsProper G := inferInstanceAs (IsProper (pullback.snd g₀ (spec b)))
  obtain ⟨z, hz, hzpb⟩ := fiber_map a h₁ hP
  obtain ⟨m, hm, hmpb⟩ := fiber_map b (IsPullback.of_hasPullback g₀ (spec b))
    (IsPullback.of_hasPullback r G)
  have hzm : z ≫ m = z₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hmpb.w, ← Category.assoc, hzpb.w, Category.assoc, spec_comp, hK]
      exact hT.w.symm
    · rw [Category.assoc, hm, ← Category.assoc, hz,
        Category.assoc, Category.assoc, hv₁, hz₀, Category.assoc]
  let y := pullback.lift m (q ≫ spec w) (by
    rw [hmpb.w, Category.assoc, spec_comp, hw'])
  have hxy : z ≫ y = e.hom ≫ x := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hzm, Category.assoc, hx₁]
      exact hT.isoPullback_hom_fst.symm
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc z, hzpb.w, Category.assoc,
        spec_comp, hw, Category.assoc, hx₂, ← Category.assoc]
      congr 1
      exact hT.isoPullback_hom_snd.symm
  have hV' : IsPullback V.hom u (z ≫ y) p := by
    exact hV.of_iso' (Iso.refl _) e (Iso.refl _) (Iso.refl _)
      (by simp [f]) (by simp) (by simpa using hxy.symm) (by simp)
  let := hp
  let := hEt
  let W := (baseChange y).obj (Scheme.Etale.mk p)
  have hW : IsFinite W.hom := inferInstanceAs (IsFinite (pullback.snd p y))
  let U := pullback.lift u (V.hom ≫ z) (by rw [Category.assoc]; exact hV'.w.symm)
  have hpb : IsPullback U V.hom W.hom z := by
    apply IsPullback.of_right (h₁₂ := pullback.fst p y) (v₁₃ := p) (h₂₂ := y)
      (by rw [show U ≫ pullback.fst p y = u from pullback.lift_fst ..]; exact hV'.flip)
      (pullback.lift_snd ..) (IsPullback.of_hasPullback p y)
  refine ⟨R, hR, hH, hN, a, ha, _, G, inferInstance, i ≫ v₁, z, W,
    ?_, hzpb.w.symm, ?_, hW, ⟨MorphismProperty.Over.isoMk hpb.isoPullback.symm
      hpb.isoPullback_inv_snd⟩, hApprox⟩
  · rw [Category.assoc, h₁.w, ← Category.assoc, hgi]
  · rw [← Category.assoc, hz]

end PhilipponFiniteEtaleHenselianStage

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeComparison (baseChange)
universe u

theorem solution
    (A : Type u) [CommRing A] [HenselianLocalRing A] {Y T : Scheme.{u}}
    (g : Y ⟶ Spec (.of A)) [IsProper g]
    (s : T ⟶ Spec (.of (IsLocalRing.ResidueField A))) (j : T ⟶ Y)
    (h : IsPullback s j (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) g)
    (V : T.Etale) [IsFinite V.hom] :
    ∃ (R : Type u) (_ : CommRing R) (_ : HenselianLocalRing R) (_ : IsNoetherianRing R)
      (a : R →+* A) (_ : IsLocalHom a) (X : Scheme.{u}) (g₀ : X ⟶ Spec (.of R)) (_ : IsProper g₀)
      (v : Y ⟶ X),
      let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
      let C := AdicCompletion (IsLocalRing.maximalIdeal R) R
      ∃ (z : T ⟶ pullback r g₀) (B : (pullback r g₀).Etale),
        g ≫ Spec.map (CommRingCat.ofHom a) = v ≫ g₀ ∧
        s ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map a)) = z ≫ pullback.fst r g₀ ∧
        j ≫ v = z ≫ pullback.snd r g₀ ∧
        IsFinite B.hom ∧ Nonempty ((baseChange z).obj B ≅ V) ∧
        (∀ (n m : ℕ) (P : Fin m → MvPolynomial (Fin n) R) (x' : Fin n → C),
          (∀ k, MvPolynomial.aeval x' (P k) = 0) →
          ∃ x : Fin n → R, (∀ k, MvPolynomial.aeval x (P k) = 0) ∧
            ∀ k, IsLocalRing.residue C (x' k) = IsLocalRing.ResidueField.map (algebraMap R C)
              (IsLocalRing.residue R (x k))) := by
  apply PhilipponFiniteEtaleHenselianStage.exists_stage _ g s j h V
  intro t
  let D := PhilipponNoetherianLocalModels.span t
  let S := PhilipponNoetherianLocalModels.ring t
  let : Algebra.FiniteType ℤ D := (Subalgebra.fg_iff_finiteType D).mp (Subalgebra.fg_adjoin_finset t)
  exact IsLocalRing.exists_approximable_henselization_of_localization_atPrime D S A (PhilipponNoetherianLocalModels.center t)
    (PhilipponNoetherianLocalModels.inclusion t)

end

end
