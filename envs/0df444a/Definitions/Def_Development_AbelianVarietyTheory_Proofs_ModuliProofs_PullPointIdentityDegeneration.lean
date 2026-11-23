-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PullPointIdentityDegeneration
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_PullPointIdentityDegeneration
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:15.296298+00:00
-- url     : https://prove2.me/theorems/5e67b937-cdaf-4cdc-a2bf-33b730455bc8
-- title:
--   Pull Point Identity Degeneration
-- statement:
--   Definitions and structural lemmas for Pull Point Identity Degeneration, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PullPointIdentityDegeneration.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatIsoUnitGenerator
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatTorsionIsomorphism
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TorsionFormCompare
end GlobalTheory.TorsionFormCompare


