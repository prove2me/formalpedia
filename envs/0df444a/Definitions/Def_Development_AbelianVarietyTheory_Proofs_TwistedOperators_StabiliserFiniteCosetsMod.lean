-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_StabiliserFiniteCosetsMod
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_StabiliserFiniteCosetsMod
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T10:27:38.642894+00:00
-- url     : https://prove2.me/theorems/6ef4196a-5ec0-4904-94e0-c86554adb5a2
-- title:
--   Stabiliser Finite Cosets Mod
-- statement:
--   Definitions and structural lemmas for Stabiliser Finite Cosets Mod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/StabiliserFiniteCosetsMod.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
namespace GlobalTheory.RootEx.UnfoldShape
end GlobalTheory.RootEx.UnfoldShape


