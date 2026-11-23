-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeFaceMiddleProjProd
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeFaceMiddleProjProd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:08.275225+00:00
-- url     : https://prove2.me/theorems/2b6719c2-f518-4cdb-8767-eb04286bb83a
-- title:
--   Cube Face Middle Proj Prod
-- statement:
--   Definitions and structural lemmas for Cube Face Middle Proj Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeFaceMiddleProjProd.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums
open Semi
section Prod
variable {S : Scheme.{0}} (H : Over S) [GrpObj H] [IsCommMonObj H]
end Prod
section Sums
variable {S : Scheme.{0}} (H : Over S) [GrpObj H] [IsCommMonObj H]
def faceA : Fin 3 → Fin 3 → Finset (Fin 2) := ![![∅, {0}, {1}], ![{0}, ∅, {1}], ![{0}, {1}, ∅]]
def swapFirstTwoSubsets : Fin 3 → Finset (Fin 3) := ![{1}, {0}, {2}]
def swapLastTwoSubsets : Fin 3 → Finset (Fin 3) := ![{0}, {2}, {1}]
def c1A : Fin 3 → Finset (Fin 4) := ![{0, 1}, {2}, {3}]
def c2A : Fin 3 → Finset (Fin 4) := ![{0}, {1}, {3}]
def c3A : Fin 3 → Finset (Fin 4) := ![{0}, {1, 2}, {3}]
def c4A : Fin 3 → Finset (Fin 4) := ![{1}, {2}, {3}]
end Sums
end ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums
namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf
open Semi CubeCoordinateSums
section Sums
variable {S : Scheme.{0}} (H : Over S) [GrpObj H] [IsCommMonObj H]
end Sums
end ReciprocityTheory.ChartRestriction.G.Out.CubePf


