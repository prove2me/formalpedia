-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RosatiCubicalAdditive
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RosatiCubicalAdditive
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:25:06.651133+00:00
-- url     : https://prove2.me/theorems/89c6dfa4-eef6-41c8-925a-82ee2daee71d
-- title:
--   Rosati Cubical Additive
-- statement:
--   Definitions and structural lemmas for Rosati Cubical Additive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RosatiCubicalAdditive.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.RosatiCube
open ReciprocityTheory.ChartRestriction.G.DVR
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
def IsNormGen (L : LB A.left) (f g : A ⟶ A) (u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)) : Prop :=
  u.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L)
variable {L : LB A.left}
variable {Lr : RigLB A} (c : CubicalStr A Lr)
end GlobalTheory.RosatiCube


