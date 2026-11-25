-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleAffineLimitGlobalSectionDetection
-- name    : AlgebraicGeometry_EtaleAffineLimitGlobalSectionDetection
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-25T06:46:28.392974+00:00
-- url     : https://prove2.me/theorems/66029197-858a-483e-8bda-5c670bff1ec3
-- title:
--   Finite-stage detection for global sections on affine inverse limits
-- statement:
--   The canonical stage maps give the filtered colimit of global sections. Vanishing and membership in the image of a system morphism can therefore be detected after refining the stage at which a section is represented.
-- source:
--   Stacks Project, Theorem 59.51.3, https://stacks.math.columbia.edu/tag/09YQ.

import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitSectionMaps
import Mathlib.Algebra.Category.Grp.FilteredColimits

noncomputable section

section

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace PhilipponFilteredColimitImage

universe u

/-- If the image of a stage element in a filtered colimit lies in the
image of a map of colimits, the element lies in the image of the stage
map after a refinement. -/
theorem exists_lift_at_stage {I : Type u} [Category.{u} I] [IsFiltered I]
    {F G : I ⥤ AddCommGrpCat.{u}} (η : F ⟶ G)
    {c : Cocone F} (hc : IsColimit c) {d : Cocone G} (hd : IsColimit d)
    (m : c.pt ⟶ d.pt) (hm : ∀ j, c.ι.app j ≫ m = η.app j ≫ d.ι.app j)
    {i : I} (x : G.obj i) (y : c.pt) (h : d.ι.app i x = m y) :
    ∃ (j : I) (a : i ⟶ j) (z : F.obj j), G.map a x = η.app j z := by
  let U := forget AddCommGrpCat.{u}
  have hc' : IsColimit (U.mapCocone c) := isColimitOfPreserves U hc
  have hd' : IsColimit (U.mapCocone d) := isColimitOfPreserves U hd
  obtain ⟨k, w, hw⟩ := Types.jointly_surjective_of_isColimit hc' y
  have he : d.ι.app i x = d.ι.app k (η.app k w) := by
    change c.ι.app k w = y at hw
    exact h.trans ((congrArg m hw).symm.trans (ConcreteCategory.congr_hom (hm k) w))
  obtain ⟨j, a, b, hab⟩ := (Types.FilteredColimit.isColimit_eq_iff (G ⋙ U) hd').mp he
  exact ⟨j, a, F.map b w, hab.trans (NatTrans.naturality_apply η b w).symm⟩

end PhilipponFilteredColimitImage

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleAcyclicCohomology (globalSections isTerminal)
open PhilipponEtaleLimitExactness (atStageSheaf)
open PhilipponEtaleLimitSheaf (limitSheaf)
open PhilipponEtaleLimitFunctor (limitFunctor)
open PhilipponEtaleLimitGlobalSections (sectionsDiagram evalIso colimIso)
open PhilipponEtaleGlobalSectionTransitions (eval_transition)
open PhilipponEtaleStageCohomology (transition sectionsEquiv_transition)
open PhilipponEtaleLimitCohomologyTransport (stageRestriction)
open PhilipponEtaleLimitSectionProjections (ι_colimIso)
open PhilipponEtaleLimitSectionsCohomology (sectionsEquiv_stageRestriction)
open PhilipponEtaleCohomologyRestrictionComp (sectionsEquiv)
open PhilipponEtaleStageCohomology (transitionMap)
open PhilipponEtaleAcyclicCohomology (globalSectionsIso)
open PhilipponEtaleLimitSectionProjections (stageSections)


namespace PhilipponEtaleLimitSectionDetection

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} [IsCofiltered I]
  [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c) (i : I)

private abbrev Sys := System (directImages D)
private abbrev T := sectionsDiagram c hc i

private def atStage (F : Sys (D := D)) (j : (Over i)ᵒᵖ) :
    (F.obj j.unop.left).H 0 ≃+ ((T c hc i).obj F).obj j :=
  (sectionsEquiv (F.obj j.unop.left)).trans
    (((evalIso c hc i j).app F).addCommGroupIsoToAddEquiv.symm)

private def atLimit (F : Sys (D := D)) :
    (limitSheaf c hc F).H 0 ≃+ ↥(colimit ((T c hc i).obj F)) :=
  (sectionsEquiv (limitSheaf c hc F)).trans
    (((colimIso c hc i).app F).addCommGroupIsoToAddEquiv.symm)

private theorem eval_atStage (F : Sys (D := D)) (j : (Over i)ᵒᵖ) (x : (F.obj j.unop.left).H 0) :
    ((evalIso c hc i j).app F).hom (atStage c hc i F j x) = sectionsEquiv (F.obj j.unop.left) x :=
  ((evalIso c hc i j).app F).addCommGroupIsoToAddEquiv.apply_symm_apply _

private theorem eval_atLimit (F : Sys (D := D)) (x : (limitSheaf c hc F).H 0) :
    ((colimIso c hc i).app F).hom (atLimit c hc i F x) = sectionsEquiv (limitSheaf c hc F) x :=
  ((colimIso c hc i).app F).addCommGroupIsoToAddEquiv.apply_symm_apply _

private theorem map_atStage (F : Sys (D := D)) {j k : (Over i)ᵒᵖ} (a : j ⟶ k)
    (x : (F.obj j.unop.left).H 0) :
    ((T c hc i).obj F).map a (atStage c hc i F j x) =
      atStage c hc i F k (transition a.unop.left F 0 x) := by
  let e := (evalIso c hc i k).app F
  let m := (globalSections (D.obj j.unop.left)).map (transitionMap a.unop.left F)
  let n := (globalSectionsIso (D.map a.unop.left)).hom.app (F.obj k.unop.left)
  apply e.addCommGroupIsoToAddEquiv.injective
  have h : e.hom (((T c hc i).obj F).map a (atStage c hc i F j x)) =
      n (m (((evalIso c hc i j).app F).hom (atStage c hc i F j x))) :=
    ConcreteCategory.congr_hom (eval_transition c hc i F a.unop) (atStage c hc i F j x)
  change e.hom (((T c hc i).obj F).map a (atStage c hc i F j x)) = e.hom (atStage c hc i F k _)
  dsimp only [e]
  rw [eval_atStage, sectionsEquiv_transition]
  exact h.trans (congrArg (fun t => n (m t)) (eval_atStage c hc i F j x))

private theorem ι_atStage (F : Sys (D := D)) (j : (Over i)ᵒᵖ)
    (x : (F.obj j.unop.left).H 0) :
    colimit.ι ((T c hc i).obj F) j (atStage c hc i F j x) =
      atLimit c hc i F (stageRestriction c hc F j.unop.left 0 x) := by
  let e := (colimIso c hc i).app F
  let s := stageSections c hc F j.unop.left
  apply e.addCommGroupIsoToAddEquiv.injective
  have h : e.hom (colimit.ι ((T c hc i).obj F) j (atStage c hc i F j x)) =
      s (((evalIso c hc i j).app F).hom (atStage c hc i F j x)) :=
    ConcreteCategory.congr_hom (ι_colimIso c hc i F j) (atStage c hc i F j x)
  change e.hom (colimit.ι ((T c hc i).obj F) j (atStage c hc i F j x)) = e.hom (atLimit c hc i F _)
  dsimp only [e]
  rw [eval_atLimit, sectionsEquiv_stageRestriction]
  exact h.trans (congrArg s (eval_atStage c hc i F j x))

private theorem atStage_naturality {F G : Sys (D := D)} (f : F ⟶ G) (j : (Over i)ᵒᵖ)
    (x : (F.obj j.unop.left).H 0) :
    ((T c hc i).map f).app j (atStage c hc i F j x) =
      atStage c hc i G j (Sheaf.H.map (f.app j.unop.left) 0 x) := by
  let e := (evalIso c hc i j).app G
  let t := (f.app j.unop.left).hom.app (op (Scheme.Etale.mk (𝟙 (D.obj j.unop.left))))
  apply e.addCommGroupIsoToAddEquiv.injective
  have h : e.hom (((T c hc i).map f).app j (atStage c hc i F j x)) =
      t (((evalIso c hc i j).app F).hom (atStage c hc i F j x)) :=
    ConcreteCategory.congr_hom ((evalIso c hc i j).hom.naturality f) (atStage c hc i F j x)
  change e.hom (((T c hc i).map f).app j (atStage c hc i F j x)) = e.hom (atStage c hc i G j _)
  dsimp only [e]
  rw [eval_atStage]
  have h' := Sheaf.H.equiv₀_naturality (isTerminal (D.obj j.unop.left)) (f.app j.unop.left) x
  exact h.trans ((congrArg t (eval_atStage c hc i F j x)).trans h')

private theorem atLimit_naturality {F G : Sys (D := D)} (f : F ⟶ G)
    (x : (limitSheaf c hc F).H 0) :
    colimMap ((T c hc i).map f) (atLimit c hc i F x) =
      atLimit c hc i G (Sheaf.H.map ((limitFunctor c hc).map f) 0 x) := by
  let e := (colimIso c hc i).app G
  let t := ((limitFunctor c hc).map f).hom.app (op (Scheme.Etale.mk (𝟙 c.pt)))
  apply e.addCommGroupIsoToAddEquiv.injective
  have h : e.hom (colimMap ((T c hc i).map f) (atLimit c hc i F x)) =
      t (((colimIso c hc i).app F).hom (atLimit c hc i F x)) :=
    ConcreteCategory.congr_hom ((colimIso c hc i).hom.naturality f) (atLimit c hc i F x)
  change e.hom (colimMap ((T c hc i).map f) (atLimit c hc i F x)) = e.hom (atLimit c hc i G _)
  dsimp only [e]
  rw [eval_atLimit]
  have h' := Sheaf.H.equiv₀_naturality (isTerminal c.pt) ((limitFunctor c hc).map f) x
  exact h.trans ((congrArg t (eval_atLimit c hc i F x)).trans h')

/-- A global section that vanishes on the affine limit vanishes at a
stage refining its original stage. -/
theorem exists_transition_eq_zero (F : Sys (D := D)) (x : (F.obj i).H 0)
    (h : stageRestriction c hc F i 0 x = 0) :
    ∃ (j : I) (a : j ⟶ i), transition a F 0 x = 0 := by
  let k : (Over i)ᵒᵖ := op (Over.mk (𝟙 i))
  let y := atStage c hc i F k x
  have hy : colimit.ι ((T c hc i).obj F) k y = 0 :=
    (ι_atStage c hc i F k x).trans ((congrArg (atLimit c hc i F) h).trans (map_zero _))
  obtain ⟨j, a, ha⟩ := PhilipponFilteredCohomologyDetection.exists_map_eq_zero
    ((T c hc i).obj F) (colimit.isColimit _) y hy
  refine ⟨j.unop.left, a.unop.left, (atStage c hc i F j).injective ?_⟩
  exact (map_atStage c hc i F a x).symm.trans (ha.trans (map_zero _).symm)

/-- A global section lying in the image of the limit map already lies
in the image at a sufficiently refined stage. -/
theorem exists_transition_mem_image {F G : Sys (D := D)} (f : F ⟶ G)
    (x : (G.obj i).H 0) (y : (limitSheaf c hc F).H 0)
    (h : stageRestriction c hc G i 0 x = Sheaf.H.map ((limitFunctor c hc).map f) 0 y) :
    ∃ (j : I) (a : j ⟶ i) (z : (F.obj j).H 0), transition a G 0 x = Sheaf.H.map (f.app j) 0 z := by
  let k : (Over i)ᵒᵖ := op (Over.mk (𝟙 i))
  let η := (T c hc i).map f
  let x' := atStage c hc i G k x
  let y' := atLimit c hc i F y
  have h' : colimit.ι ((T c hc i).obj G) k x' = colimMap η y' :=
    (ι_atStage c hc i G k x).trans
      ((congrArg (atLimit c hc i G) h).trans (atLimit_naturality c hc i f y).symm)
  obtain ⟨j, a, w, hw⟩ := PhilipponFilteredColimitImage.exists_lift_at_stage η
    (colimit.isColimit _) (colimit.isColimit _) (colimMap η) (ι_colimMap η) x' y' h'
  obtain ⟨z, rfl⟩ := (atStage c hc i F j).surjective w
  refine ⟨j.unop.left, a.unop.left, z, (atStage c hc i G j).injective ?_⟩
  exact (map_atStage c hc i G a x).symm.trans (hw.trans (atStage_naturality c hc i f j z))

end PhilipponEtaleLimitSectionDetection

end

end


