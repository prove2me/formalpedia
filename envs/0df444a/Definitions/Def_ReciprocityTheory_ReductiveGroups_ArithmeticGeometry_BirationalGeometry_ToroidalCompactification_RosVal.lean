-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:41.631493+00:00
-- url     : https://prove2.me/theorems/e660c147-8dfc-4b50-965c-352461d0d167
-- title:
--   Ros Val
-- statement:
--   Definitions and structural lemmas for Ros Val, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RosVal.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable [IsCommMonObj A] {L : LB A.left}
def val₂ {K : Type} [Fintype K] {φ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb L φ ε)) {T : Over S}
    (z : T.left) (J : (T.left ⟶ A.left) → L.ι) (x y : T ⟶ A) : (T.left.presheaf.stalk z)ˣ := val u (lift x y).left z J
variable {Lr : RigLB A} (c : CubicalStr A Lr)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


