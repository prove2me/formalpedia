-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteProjectiveOfLocalBasis
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteProjectiveOfLocalBasis
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T16:35:49.352223+00:00
-- url     : https://prove2.me/theorems/e5344b84-3d6a-45f3-abef-543f72175084
-- title:
--   Finite Projective Of Local Basis
-- statement:
--   Definitions and structural lemmas for Finite Projective Of Local Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteProjectiveOfLocalBasis.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnivChartOfStandardSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushRProdPtsResP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LieProj
end GlobalTheory.LieProj


