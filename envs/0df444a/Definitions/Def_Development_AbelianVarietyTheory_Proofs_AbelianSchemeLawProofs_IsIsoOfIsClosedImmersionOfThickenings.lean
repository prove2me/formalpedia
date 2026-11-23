-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:32.662679+00:00
-- url     : https://prove2.me/theorems/469071d8-c465-4604-8f6c-fda99f31d6a8
-- title:
--   Is Iso Of Is Closed Immersion Of Thickenings
-- statement:
--   Definitions and structural lemmas for Is Iso Of Is Closed Immersion Of Thickenings, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoOfIsClosedImmersionOfThickenings.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace ThickeningClosed
def zeroLocusOpen {X : Scheme.{0}} (K : X.IdealSheafData) : Set X :=
  {x | ∃ V : X.affineOpens, x ∈ V.1 ∧ K.ideal V = ⊥}
end ThickeningClosed
end GlobalTheory


