-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUniformizationIdentityPullback
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUniformizationIdentityPullback
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:21.224613+00:00
-- url     : https://prove2.me/theorems/9e88f410-9c39-4523-843e-b23f3fd2b683
-- title:
--   Same Uniformization Identity Pullback
-- statement:
--   Definitions and structural lemmas for Same Uniformization Identity Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SameUniformizationIdentityPullback.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GmMulEqOfResMulEq
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
namespace GlobalTheory.TorsionFormCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
end GlobalTheory.TorsionFormCompare


