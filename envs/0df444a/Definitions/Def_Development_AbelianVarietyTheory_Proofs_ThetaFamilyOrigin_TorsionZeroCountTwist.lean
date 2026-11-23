-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_TorsionZeroCountTwist
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_TorsionZeroCountTwist
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:42:01.842316+00:00
-- url     : https://prove2.me/theorems/a382fbae-5779-4da0-a801-4bd4a4ddbb3e
-- title:
--   Torsion Zero Count Twist
-- statement:
--   Definitions and structural lemmas for Torsion Zero Count Twist, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/TorsionZeroCountTwist.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
  ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TwistZero
section General
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
def Triv (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Prop :=
  ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen
end General
section Square
variable {k : Type} [Field k]
end Square
section Translate
variable {S : Scheme.{0}} (A : Over S) [GrpObj A]
def untransl (b : baseOver S ⟶ A) : A ⟶ baseOver S ⊗ A :=
  lift (Over.homMk A.hom (Category.comp_id _))
    (((Over.homMk A.hom (Category.comp_id _) : A ⟶ baseOver S) ≫ b)⁻¹ * 𝟙 A)
end Translate
end GlobalTheory.TwistZero
namespace GlobalTheory
open Complex Matrix Filter Topology
open scoped BigOperators Real
end GlobalTheory


