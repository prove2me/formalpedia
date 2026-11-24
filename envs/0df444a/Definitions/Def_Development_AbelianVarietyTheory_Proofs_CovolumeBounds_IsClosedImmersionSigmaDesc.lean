-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionSigmaDesc
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionSigmaDesc
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:28:01.17702+00:00
-- url     : https://prove2.me/theorems/72af0981-2bbf-48df-9f1d-fe11ef1e9592
-- title:
--   Is Closed Immersion Sigma Desc
-- statement:
--   Definitions and structural lemmas for Is Closed Immersion Sigma Desc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IsClosedImmersionSigmaDesc.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG IsProjOver)
namespace GlobalTheory.ProjSpace
end GlobalTheory.ProjSpace


