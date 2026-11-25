-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CurvatureSumWedgeWellDefinedAndDeRhamLiftStatement
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CurvatureSumWedgeWellDefinedAndDeRhamLiftStatement
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T15:14:30.744936+00:00
-- url     : https://prove2.me/theorems/7fcd645b-63b7-5ca2-b9c8-6e9b2a10a9aa
-- title:
--   Curvature Sum Wedge Well Defined And De Rham Lift Statement
-- statement:
--   Definitions and structural lemmas for Curvature Sum Wedge Well Defined And De Rham Lift Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CurvatureSumWedgeWellDefinedAndDeRhamLiftStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CurvatureSumWedgeWellDefinedAndDeRhamLift
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory


