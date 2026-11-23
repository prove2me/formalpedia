-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LbPowDescends
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_LbPowDescends
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:37:13.002255+00:00
-- url     : https://prove2.me/theorems/af92d6ea-f5ff-4cd2-b10b-66842f5bb390
-- title:
--   Lb Pow Descends
-- statement:
--   Definitions and structural lemmas for Lb Pow Descends, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LbPowDescends.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LbPowDescendsOfIsotropic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.LinDescent
end GlobalTheory.LinDescent


