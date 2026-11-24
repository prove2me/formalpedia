-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagRatioBasis
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagRatioBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:18.221152+00:00
-- url     : https://prove2.me/theorems/3ec208a6-1dd8-4e44-a666-f595dce84e64
-- title:
--   PDiag Ratio Basis
-- statement:
--   Definitions and structural lemmas for PDiag Ratio Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagRatioBasis.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StDiagRatioBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
def diagChart {ι ν κ : Type} (c : ∀ k, T.yyIdx ι ν κ k) : ∀ k, T.wwIdx ι ν κ k
  | .base => (c .base : ι)
  | .det => (c .det : ν)
  | .line0 => (c .line : κ)
  | .line1 => (c .line : κ)
end
end GroundTheory.Heights₂.Heights.Inter


