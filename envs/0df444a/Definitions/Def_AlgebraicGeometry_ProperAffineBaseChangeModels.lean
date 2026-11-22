-- Prove2me | Definitions.Def_AlgebraicGeometry_ProperAffineBaseChangeModels
-- name    : AlgebraicGeometry_ProperAffineBaseChangeModels
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-22T07:13:26.012181+00:00
-- url     : https://prove2.me/theorems/50d79304-8388-450f-9964-7b76dc896d33
-- title:
--   Affine models by base change
-- statement:
--   A proper morphism over one stage gives a diagram of proper affine models by base change.

import Definitions.Def_AlgebraicGeometry_Scheme_ProperAffineModels
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Connected

noncomputable section

section

section

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

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite


namespace PhilipponAmbientModelsOfBaseChange

universe u

variable {J : Type u} [Category.{u} J] [IsCofiltered J]
  {R : Type u} [CommRing R]
  (A : Jᵒᵖ ⥤ CommRingCat.{u})
  (ι : A ⟶ (Functor.const Jᵒᵖ).obj (CommRingCat.of R))
  {B : CommRingCat.{u}} (σ : (Functor.const Jᵒᵖ).obj B ⟶ A)
  (τ : B ⟶ CommRingCat.of R) (hστ : ∀ j, σ.app j ≫ ι.app j = τ)
  {Y : Scheme.{u}} (g : Y ⟶ Spec B)

private abbrev baseCocone : Cocone A := ⟨CommRingCat.of R, ι⟩
private abbrev baseCone := Scheme.Spec.mapCone (coneRightOpOfCocone (baseCocone A ι))

private def toModel : A.rightOp ⋙ Scheme.Spec ⟶ (Functor.const J).obj (Spec B) where
  app j := Spec.map (σ.app (op j))
  naturality i j v := by
    change Spec.map (A.map v.op) ≫ Spec.map (σ.app (op j)) = Spec.map (σ.app (op i)) ≫ 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp]
    congr 1
    exact ((Category.id_comp _).symm.trans (σ.naturality v.op)).symm

private abbrev constantModel : (Functor.const J).obj Y ⟶ (Functor.const J).obj (Spec B) :=
  (Functor.const J).map g

private abbrev ambient := PhilipponPullbackLimit.diagram (toModel A σ) (constantModel (J := J) g)

include hστ in
omit [IsCofiltered J] in
private theorem toModel_compat (j : J) :
    (baseCone A ι).π.app j ≫ (toModel A σ).app j = Spec.map τ ≫ (constCone J (Spec B)).π.app j := by
  change Spec.map (ι.app (op j)) ≫ Spec.map (σ.app (op j)) = Spec.map τ ≫ 𝟙 _
  rw [← Spec.map_comp, hστ, Category.comp_id]

omit [IsCofiltered J] in
private theorem constantModel_compat (j : J) :
    (constCone J Y).π.app j ≫ (constantModel (J := J) g).app j =
      g ≫ (constCone J (Spec B)).π.app j := by
  change 𝟙 Y ≫ g = g ≫ 𝟙 _
  simp

private abbrev ambientCone :=
  PhilipponPullbackLimit.cone (toModel A σ) (constantModel (J := J) g)
    (cX := baseCone A ι) (cY := constCone J Y) (cS := constCone J (Spec B))
    (Spec.map τ) g (toModel_compat A ι σ τ hστ) (constantModel_compat g)

omit [IsCofiltered J] in
private theorem stage_affine (j : J) :
    IsAffineHom ((PhilipponPullbackLimit.second (toModel A σ) (constantModel (J := J) g)).app j) := by
  change IsAffineHom (pullback.snd (Spec.map (σ.app (op j))) g)
  exact isAffineHom_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (Spec.map (σ.app (op j))) g)
    (inferInstanceAs (IsAffineHom (Spec.map (σ.app (op j)))))

omit [IsCofiltered J] in
private theorem transition_affine {i j : J} (v : i ⟶ j) : IsAffineHom ((ambient A σ g).map v) := by
  let p := PhilipponPullbackLimit.second (toModel A σ) (constantModel (J := J) g)
  let : IsAffineHom (p.app j) := stage_affine A σ g j
  have h : (ambient A σ g).map v ≫ p.app j = p.app i := by
    exact (p.naturality v).trans (Category.comp_id _)
  let : IsAffineHom ((ambient A σ g).map v ≫ p.app j) := by
    rw [h]
    exact stage_affine A σ g i
  exact IsAffineHom.of_comp ((ambient A σ g).map v) (p.app j)

omit [IsCofiltered J] in
private theorem projection_compat (j : J) :
    (ambientCone A ι σ τ hστ g).π.app j ≫
        (PhilipponPullbackLimit.first (toModel A σ) (constantModel (J := J) g)).app j =
      pullback.fst (Spec.map τ) g ≫ Spec.map (ι.app (op j)) :=
  PhilipponPullbackLimit.cone_first (toModel A σ) (constantModel (J := J) g)
    (cX := baseCone A ι) (cY := constCone J Y) (cS := constCone J (Spec B))
    (Spec.map τ) g (toModel_compat A ι σ τ hστ) (constantModel_compat g) j

private def ambientIsLimit (hA : IsColimit (baseCocone A ι)) : IsLimit (ambientCone A ι σ τ hστ g) := by
  let : IsConnected J := IsCofiltered.isConnected J
  exact PhilipponPullbackLimit.isLimit (toModel A σ) (constantModel (J := J) g)
    (cX := baseCone A ι) (cY := constCone J Y) (cS := constCone J (Spec B))
    (Spec.map τ) g (toModel_compat A ι σ τ hστ) (constantModel_compat g)
    (isLimitOfPreserves Scheme.Spec (isLimitConeRightOpOfCocone A hA))
    (isLimitConstCone J Y) (isLimitConstCone J (Spec B))

/-- A proper morphism over one stage gives a proper approximation over any
Noetherian base diagram that admits compatible maps from that stage. -/
def affineOfBaseChange (hA : IsColimit (baseCocone A ι)) [IsProper g]
    [∀ j, IsNoetherianRing (A.obj j)] :
    PhilipponProperAffineApproximation.AffineModels (pullback.fst (Spec.map τ) g) where
  index := J
  category := inferInstance
  cofiltered := inferInstance
  rings := A
  noetherian := inferInstance
  baseInclusion := ι
  baseColimit := hA
  ambient := ambient A σ g
  affine := transition_affine A σ g
  maps := PhilipponPullbackLimit.first (toModel A σ) (constantModel (J := J) g)
  proper j := inferInstanceAs (IsProper (pullback.fst ((toModel A σ).app j) g))
  projection := (ambientCone A ι σ τ hστ g).π
  ambientLimit := ambientIsLimit A ι σ τ hστ g hA
  commutes := projection_compat A ι σ τ hστ g

end PhilipponAmbientModelsOfBaseChange

end

end


