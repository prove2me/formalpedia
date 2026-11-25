-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmEllipticCurveHomExistsPureTypeVectorStatement
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmEllipticCurveHomExistsPureTypeVectorStatement
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T15:25:20.530785+00:00
-- url     : https://prove2.me/theorems/5a516e2d-7902-5003-a369-43a5319cf012
-- title:
--   Cm Elliptic Curve Hom Exists Pure Type Vector Statement
-- statement:
--   Definitions and structural lemmas for Cm Elliptic Curve Hom Exists Pure Type Vector Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CmEllipticCurveHomExistsPureTypeVectorStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmEllipticCurveHomExistsPureTypeVector
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_PermutesRefl
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj


