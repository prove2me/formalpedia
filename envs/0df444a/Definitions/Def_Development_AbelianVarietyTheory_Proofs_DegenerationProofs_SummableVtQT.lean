-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SummableVtQT
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SummableVtQT
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:34:49.115379+00:00
-- url     : https://prove2.me/theorems/e301b3c7-ad15-459b-8332-72f2077933b1
-- title:
--   Summable Vt QT
-- statement:
--   Definitions and structural lemmas for Summable Vt QT, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SummableVtQT.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
namespace GlobalTheory.Ex.NumD.Int
variable {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}
end GlobalTheory.Ex.NumD.Int
namespace GlobalTheory.Ex
end GlobalTheory.Ex


