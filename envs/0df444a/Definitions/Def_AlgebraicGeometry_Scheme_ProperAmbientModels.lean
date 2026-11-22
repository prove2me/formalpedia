-- Prove2me | Definitions.Def_AlgebraicGeometry_Scheme_ProperAmbientModels
-- name    : AlgebraicGeometry_Scheme_ProperAmbientModels
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-22T00:19:16.837642+00:00
-- url     : https://prove2.me/theorems/962a80ac-2f50-447d-a84b-59d64bb96a82
-- title:
--   Proper ambient models over Noetherian local rings
-- statement:
--   An ambient approximation and its induced limit diagram of closed fibers.

import Definitions.Def_AlgebraicGeometry_Scheme_ProperClosedFiberModels
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

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

open CategoryTheory CategoryTheory.Limits IsLocalRing


namespace PhilipponResidueFieldColimit

universe u

variable {J : Type u} [Category.{u} J] (F : J ⥤ CommRingCat.{u})
  [∀ j, IsLocalRing (F.obj j)] [∀ {i j : J} (h : i ⟶ j), IsLocalHom (F.map h).hom]

/-- Apply the residue field construction to a diagram of local rings and local maps. -/
abbrev diagram : J ⥤ CommRingCat.{u} where
  obj j := .of (ResidueField (F.obj j))
  map h := CommRingCat.ofHom (ResidueField.map (F.map h).hom)
  map_id j := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨y, rfl⟩ := residue_surjective x
    change residue (F.obj j) ((F.map (𝟙 j)).hom y) = residue (F.obj j) y
    exact congrArg (residue (F.obj j)) (ConcreteCategory.congr_hom (F.map_id j) y)
  map_comp h k := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨y, rfl⟩ := residue_surjective x
    change residue _ ((F.map (h ≫ k)).hom y) = residue _ ((F.map k).hom ((F.map h).hom y))
    exact congrArg (residue _) (ConcreteCategory.congr_hom (F.map_comp h k) y)

/-- The residue maps commute with the transition maps of local rings. -/
def quotient : F ⟶ diagram F where
  app j := CommRingCat.ofHom (residue (F.obj j))
  naturality _ _ h := CommRingCat.hom_ext (ResidueField.map_comp_residue (F.map h).hom).symm

variable (c : Cocone F) [IsLocalRing c.pt] [∀ j, IsLocalHom (c.ι.app j).hom]

/-- The residue field of a cocone vertex receives all the stage residue fields. -/
abbrev cocone : Cocone (diagram F) where
  pt := .of (ResidueField c.pt)
  ι :=
    { app := fun j => CommRingCat.ofHom (ResidueField.map (c.ι.app j).hom)
      naturality := by
        intro i j h
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro x
        obtain ⟨y, rfl⟩ := residue_surjective x
        change residue c.pt ((c.ι.app j).hom ((F.map h).hom y)) = residue c.pt ((c.ι.app i).hom y)
        exact congrArg (residue c.pt) (ConcreteCategory.congr_hom (c.w h) y) }

@[reassoc]
theorem cocone_quotient (j : J) :
    (quotient F).app j ≫ (cocone F c).ι.app j =
      c.ι.app j ≫ CommRingCat.ofHom (residue c.pt) :=
  CommRingCat.hom_ext (ResidueField.map_comp_residue (R := F.obj j) (S := c.pt) (c.ι.app j).hom)

variable [IsFiltered J] (hc : IsColimit c)

private abbrev forgetResidue (t : Cocone (diagram F)) : Cocone F where
  pt := t.pt
  ι := quotient F ≫ t.ι

omit [∀ j, IsLocalHom (c.ι.app j).hom] in
private theorem desc_mem_zero (t : Cocone (diagram F)) (x : c.pt) (hx : x ∈ maximalIdeal c.pt) :
    (hc.desc (forgetResidue F t)).hom x = 0 := by
  obtain ⟨j, y, hxy⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget CommRingCat.{u}) hc) x
  change (c.ι.app j).hom y = x at hxy
  rw [← hxy] at hx ⊢
  have hy : y ∈ maximalIdeal (F.obj j) := by
    by_contra hn
    have hu : IsUnit (M := F.obj j) y := (notMem_maximalIdeal (R := F.obj j)).mp hn
    have hv : IsUnit (M := c.pt) ((c.ι.app j).hom y) := hu.map (c.ι.app j).hom
    exact ((notMem_maximalIdeal (R := c.pt)).mpr hv) hx
  have h := ConcreteCategory.congr_hom (hc.fac (forgetResidue F t) j) y
  change (hc.desc (forgetResidue F t)).hom ((c.ι.app j).hom y) =
    (t.ι.app j).hom (residue (F.obj j) y) at h
  rw [show residue (F.obj j) y = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hy, map_zero] at h
  exact h

private def desc (t : Cocone (diagram F)) : (cocone F c).pt ⟶ t.pt :=
  CommRingCat.ofHom (Ideal.Quotient.lift _ (hc.desc (forgetResidue F t)).hom (desc_mem_zero F c hc t))

private theorem quotient_desc (t : Cocone (diagram F)) :
    CommRingCat.ofHom (residue c.pt) ≫ desc F c hc t = hc.desc (forgetResidue F t) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  rfl

/-- Residue fields commute with filtered colimits of local rings and local maps. -/
def isColimit : IsColimit (cocone F c) where
  desc := desc F c hc
  fac t j := by
    have : Epi ((quotient F).app j) :=
      ConcreteCategory.epi_of_surjective _ (residue_surjective (R := F.obj j))
    apply (cancel_epi ((quotient F).app j)).mp
    rw [← Category.assoc, cocone_quotient, Category.assoc, quotient_desc]
    exact hc.fac (forgetResidue F t) j
  uniq t m hm := by
    have : Epi (CommRingCat.ofHom (residue c.pt)) :=
      ConcreteCategory.epi_of_surjective _ (residue_surjective (R := c.pt))
    apply (cancel_epi (CommRingCat.ofHom (residue c.pt))).mp
    rw [quotient_desc]
    apply hc.uniq (forgetResidue F t)
    intro j
    rw [← Category.assoc, ← cocone_quotient, Category.assoc, hm j]
    rfl

end PhilipponResidueFieldColimit

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponProperClosedFiberApproximation (ClosedFiberModels)


namespace PhilipponClosedFiberModelDiagram

universe u

variable {J : Type u} [Category.{u} J] [IsCofiltered J]
  (A : Jᵒᵖ ⥤ CommRingCat.{u}) [∀ j, IsLocalRing (A.obj j)]
  [∀ {j k : Jᵒᵖ} (v : j ⟶ k), IsLocalHom (A.map v).hom]
  (cA : Cocone A) [IsLocalRing cA.pt] [∀ j, IsLocalHom (cA.ι.app j).hom]

private abbrev κ := PhilipponResidueFieldColimit.diagram A
private abbrev cκ := PhilipponResidueFieldColimit.cocone A cA

private abbrev baseCone := Scheme.Spec.mapCone (coneRightOpOfCocone cA)
private abbrev residueCone := Scheme.Spec.mapCone (coneRightOpOfCocone (cκ A cA))

private abbrev residueDiagram : (κ A).rightOp ⋙ Scheme.Spec ⟶ A.rightOp ⋙ Scheme.Spec :=
  Functor.whiskerRight (PhilipponResidueFieldColimit.quotient A).rightOp Scheme.Spec

private abbrev residueAtLimit := Spec.map (CommRingCat.ofHom (IsLocalRing.residue cA.pt))

omit [IsCofiltered J] in
private theorem residue_compat (j : J) :
    (residueCone A cA).π.app j ≫ (residueDiagram A).app j =
      residueAtLimit A cA ≫ (baseCone A cA).π.app j := by
  have h := PhilipponResidueFieldColimit.cocone_quotient A cA (op j)
  change Scheme.Spec.map ((cκ A cA).ι.app (op j)).op ≫
      Scheme.Spec.map ((PhilipponResidueFieldColimit.quotient A).app (op j)).op =
    Scheme.Spec.map (CommRingCat.ofHom (IsLocalRing.residue cA.pt)).op ≫ Scheme.Spec.map (cA.ι.app (op j)).op
  simpa only [op_comp, Functor.map_comp] using congrArg (fun r => Scheme.Spec.map r.op) h

variable {Y : J ⥤ Scheme.{u}} (q : Y ⟶ A.rightOp ⋙ Scheme.Spec)
  [∀ j, IsProper (q.app j)]

private abbrev fibers := PhilipponPullbackLimit.diagram (residueDiagram A) q

omit [IsCofiltered J] in
private theorem closedImmersion_residue (j : J) : IsClosedImmersion ((residueDiagram A).app j) :=
  IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (IsLocalRing.residue (A.obj (op j))))
    IsLocalRing.residue_surjective

omit [IsCofiltered J] [∀ j, IsProper (q.app j)] in
private theorem fibers_affine [∀ {j k : J} (v : j ⟶ k), IsAffineHom (Y.map v)]
    {j k : J} (v : j ⟶ k) : IsAffineHom ((fibers A q).map v) := by
  let p := PhilipponPullbackLimit.second (residueDiagram A) q
  have closed (l : J) : IsClosedImmersion (p.app l) := by
    let : IsClosedImmersion ((residueDiagram A).app l) := closedImmersion_residue A l
    exact inferInstanceAs (IsClosedImmersion (pullback.snd ((residueDiagram A).app l) (q.app l)))
  let : IsClosedImmersion (p.app j) := closed j
  let : IsClosedImmersion (p.app k) := closed k
  have : IsAffineHom ((fibers A q).map v ≫ p.app k) := by rw [p.naturality]; infer_instance
  exact IsAffineHom.of_comp ((fibers A q).map v) (p.app k)

omit [IsCofiltered J] in
private theorem fiberProper (j : J) : IsProper (pullback.fst ((residueDiagram A).app j) (q.app j)) := by
  let : IsProper (q.app j) := inferInstance
  infer_instance

omit [IsCofiltered J] in
private theorem fiber_compact (j : J) : CompactSpace ((fibers A q).obj j) := by
  let p := pullback.fst ((residueDiagram A).app j) (q.app j)
  let : UniversallyClosed p := (fiberProper A q j).toUniversallyClosed
  have hBase : CompactSpace (((κ A).rightOp ⋙ Scheme.Spec).obj j) := inferInstanceAs
    (CompactSpace (Spec (CommRingCat.of (IsLocalRing.ResidueField (A.obj (op j))))))
  refine ⟨?_⟩
  change IsCompact (Set.univ : Set ↥(pullback ((residueDiagram A).app j) (q.app j) : Scheme.{u}))
  simpa only [Set.preimage_univ] using p.isProperMap.isCompact_preimage hBase.isCompact_univ

omit [IsCofiltered J] in
private theorem fiber_quasiSeparated (j : J) : QuasiSeparatedSpace ((fibers A q).obj j) := by
  let p := pullback.fst ((residueDiagram A).app j) (q.app j)
  let : IsSeparated p := (fiberProper A q j).toIsSeparated
  have hBase : QuasiSeparatedSpace (((κ A).rightOp ⋙ Scheme.Spec).obj j) := inferInstanceAs
    (QuasiSeparatedSpace (Spec (CommRingCat.of (IsLocalRing.ResidueField (A.obj (op j))))))
  exact @quasiSeparatedSpace_of_quasiSeparated _ _ p hBase (inferInstanceAs (QuasiSeparated p))

variable (cY : Cone Y) (f : cY.pt ⟶ Spec cA.pt)
  (hf : ∀ j, cY.π.app j ≫ q.app j = f ≫ (baseCone A cA).π.app j)

private abbrev limitFiberCone :=
  PhilipponPullbackLimit.cone (residueDiagram A) q (cX := residueCone A cA) (cY := cY) (cS := baseCone A cA)
    (residueAtLimit A cA) f (residue_compat A cA) hf

/-- A proper affine-transition model of the ambient morphism over a filtered
colimit of Noetherian local rings supplies the required closed-fiber models. -/
def ofAmbientDiagram (hA : IsColimit cA) (hY : IsLimit cY)
    [∀ j, IsNoetherianRing (A.obj j)] [∀ {j k : J} (v : j ⟶ k), IsAffineHom (Y.map v)] :
    ClosedFiberModels (pullback.snd (residueAtLimit A cA) f) where
  index := J
  category := inferInstance
  cofiltered := inferInstance
  stages := fibers A q
  affine := fibers_affine A q
  compact := fiber_compact A q
  quasiSeparated := fiber_quasiSeparated A q
  projection := (limitFiberCone A cA q cY f hf).π
  limit := PhilipponPullbackLimit.isLimit (residueDiagram A) q (cX := residueCone A cA)
    (cY := cY) (cS := baseCone A cA) (residueAtLimit A cA) f (residue_compat A cA) hf
    (isLimitOfPreserves Scheme.Spec (isLimitConeRightOpOfCocone _ (PhilipponResidueFieldColimit.isColimit A cA hA)))
    hY (isLimitOfPreserves Scheme.Spec (isLimitConeRightOpOfCocone _ hA))
  model j :=
    { A := A.obj (op j)
      ring := inferInstance
      localRing := inferInstance
      noetherian := inferInstance
      Y := Y.obj j
      g := q.app j
      proper := inferInstance
      fiber := Iso.refl _
      ambient := cY.π.app j
      commutes := by
        change (limitFiberCone A cA q cY f hf).π.app j ≫ 𝟙 _ ≫
            (PhilipponPullbackLimit.second (residueDiagram A) q).app j = _
        rw [Category.id_comp]
        exact PhilipponPullbackLimit.cone_second _ _ _ _ (residue_compat A cA) hf j }

end PhilipponClosedFiberModelDiagram

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponProperClosedFiberApproximation (ClosedFiberModels)


namespace PhilipponProperAmbientModels

universe u

variable {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- An approximation of a morphism over a local affine base by proper morphisms over
Noetherian local rings, with affine transitions in the schemes above the base. -/
structure AmbientModels where
  index : Type u
  [category : Category.{u} index]
  [cofiltered : IsCofiltered index]
  rings : indexᵒᵖ ⥤ CommRingCat.{u}
  [localRing : ∀ j, IsLocalRing (rings.obj j)]
  [noetherian : ∀ j, IsNoetherianRing (rings.obj j)]
  [localMap : ∀ {j k : indexᵒᵖ} (v : j ⟶ k), IsLocalHom (rings.map v).hom]
  baseInclusion : rings ⟶ (Functor.const indexᵒᵖ).obj (CommRingCat.of A)
  [localInclusion : ∀ j, IsLocalHom (baseInclusion.app j).hom]
  baseColimit : IsColimit ⟨CommRingCat.of A, baseInclusion⟩
  ambient : index ⥤ Scheme.{u}
  [affine : ∀ {j k : index} (v : j ⟶ k), IsAffineHom (ambient.map v)]
  maps : ambient ⟶ rings.rightOp ⋙ Scheme.Spec
  [proper : ∀ j, IsProper (maps.app j)]
  projection : (Functor.const index).obj X ⟶ ambient
  ambientLimit : IsLimit ⟨X, projection⟩
  commutes : ∀ j, projection.app j ≫ maps.app j = f ≫ Spec.map (baseInclusion.app (op j))

/-- Taking the closed fibers of a proper ambient approximation yields the closed-fiber approximation. -/
def closedFiberModels (M : AmbientModels f) :
    ClosedFiberModels (pullback.snd (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) f) := by
  let : Category.{u} M.index := M.category
  let : IsCofiltered M.index := M.cofiltered
  let : ∀ j, IsLocalRing (M.rings.obj j) := M.localRing
  let : ∀ j, IsNoetherianRing (M.rings.obj j) := M.noetherian
  let : ∀ {j k : M.indexᵒᵖ} (v : j ⟶ k), IsLocalHom (M.rings.map v).hom := fun v => M.localMap v
  let : ∀ j, IsLocalHom (M.baseInclusion.app j).hom := M.localInclusion
  let : ∀ {j k : M.index} (v : j ⟶ k), IsAffineHom (M.ambient.map v) := fun v => M.affine v
  let : ∀ j, IsProper (M.maps.app j) := M.proper
  let cA : Cocone M.rings := ⟨CommRingCat.of A, M.baseInclusion⟩
  let cX : Cone M.ambient := ⟨X, M.projection⟩
  exact PhilipponClosedFiberModelDiagram.ofAmbientDiagram M.rings cA M.maps cX f M.commutes
    M.baseColimit M.ambientLimit

end PhilipponProperAmbientModels

end

end


