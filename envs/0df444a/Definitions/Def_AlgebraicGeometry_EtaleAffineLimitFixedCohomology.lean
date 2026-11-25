-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleAffineLimitFixedCohomology
-- name    : AlgebraicGeometry_EtaleAffineLimitFixedCohomology
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-25T06:35:47.956812+00:00
-- url     : https://prove2.me/theorems/0fdb92fa-4b80-5856-8ef8-6140ba2b5308
-- title:
--   Cohomology comparisons for pullbacks from a fixed scheme
-- statement:
--   For the compatible system of pullbacks from a fixed scheme, the stage and limit comparisons agree with ordinary cohomological restriction.
-- source:
--   Stacks Project, Theorem 59.51.3, https://stacks.math.columbia.edu/tag/09YQ.

import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitBoundaryMaps
import Definitions.Def_AlgebraicGeometry_EtalePullbackSystemComparisons

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleConeSystem (extended)
open PhilipponEtaleLimitBaseMaps (OverBase coneSystem)
open PhilipponEtaleLimitFixedCoefficient (limitIso)
open PhilipponEtaleLimitFixedComparison (fromStage_comp)
open PhilipponEtaleLimitCanonical (fromStage restrictCoefficients)
open PhilipponEtaleLimitCohomologyTransport (stageRestriction)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleCohomologyAlong (pullbackComposition restrict_comp_over)
open PhilipponEtalePullbackSystemComparison (adjoint_transition)
open PhilipponEtaleStageCohomology (transition transitionCoefficients)
open PhilipponEtalePrimeTorsionComparison (restrict)


namespace PhilipponEtaleFixedCohomologyComparison

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}
  {X : Scheme.{u}} (B : OverBase c X) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})

private def p : ∀ j : WithInitial I, (extended c).obj j ⟶ X
  | WithInitial.of i => B.stage i
  | WithInitial.star => B.point

private theorem hp (i j : WithInitial I) (a : i ⟶ j) :
    (extended c).map a ≫ p B j = p B i := by
  cases i <;> cases j
  · exact B.stage_w (WithInitial.down a)
  · exact (WithInitial.false_of_to_star a).elim
  · exact B.point_w _
  · exact Category.id_comp _

private abbrev S := PhilipponEtaleConeSystem.restrict c (coneSystem B F)

/-- For pullbacks of a fixed sheaf, a class restricted from the base to
one stage restricts to the same class at a refined stage. -/
theorem transition_restrict {i j : I} (a : i ⟶ j) (q : ℕ) (x : F.H q) :
    transition a (S B F) q (restrict (B.stage j) F q x) = restrict (B.stage i) F q x := by
  have h : transitionCoefficients a (S B F) =
      (pullbackComposition (B.stage j) (D.map a) (B.stage i) (B.stage_w a)).hom.app F :=
    adjoint_transition (extended c) (p B) (hp B) F (WithInitial.incl.map a)
  change Sheaf.H.map (transitionCoefficients a (S B F)) q
    (restrict (D.map a) ((pullbackSheaves (B.stage j)).obj F) q (restrict (B.stage j) F q x)) = _
  rw [h]
  exact restrict_comp_over (B.stage j) (D.map a) (B.stage i) (B.stage_w a) F q x

variable [IsCofiltered I] [∀ i, IsAffine (D.obj i)] (hc : IsLimit c)

private theorem coefficient_comparison (i : I) :
    restrictCoefficients c hc (S B F) i ≫ (limitIso hc B F).hom =
      (pullbackComposition (B.stage i) (c.π.app i) B.point (B.point_w i)).hom.app F := by
  let e := pullbackAdjunction (c.π.app i)
  have h := e.homEquiv_naturality_right_symm (fromStage c hc (S B F) i) (limitIso hc B F).hom
  change (e.homEquiv _ _).symm (fromStage c hc (S B F) i) ≫ (limitIso hc B F).hom = _
  rw [← h, fromStage_comp]
  exact adjoint_transition (extended c) (p B) (hp B) F (WithInitial.homTo i)

/-- The comparison from the stage to the limit carries a class
restricted from the fixed base to its restriction along the limit map. -/
theorem stageRestriction_restrict (i : I) (q : ℕ) (x : F.H q) :
    Sheaf.H.map (limitIso hc B F).hom q
      (stageRestriction c hc (S B F) i q (restrict (B.stage i) F q x)) =
    restrict B.point F q x := by
  let p : c.pt ⟶ D.obj i := c.π.app i
  let y := restrict p ((pullbackSheaves (B.stage i)).obj F) q (restrict (B.stage i) F q x)
  let m : (pullbackSheaves p).obj ((pullbackSheaves (B.stage i)).obj F) ⟶
      PhilipponEtaleLimitSheaf.limitSheaf c hc (S B F) := restrictCoefficients c hc (S B F) i
  let n := (limitIso hc B F).hom
  have hn : m ≫ n = (pullbackComposition (B.stage i) p B.point (B.point_w i)).hom.app F :=
    coefficient_comparison B F hc i
  change Sheaf.H.map n q (Sheaf.H.map m q y) = _
  rw [← Sheaf.H.map_comp_apply, hn]
  exact restrict_comp_over (B.stage i) (c.π.app i) B.point (B.point_w i) F q x

end PhilipponEtaleFixedCohomologyComparison

end

end


