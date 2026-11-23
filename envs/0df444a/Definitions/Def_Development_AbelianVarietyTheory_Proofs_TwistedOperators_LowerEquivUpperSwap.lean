-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:41.593477+00:00
-- url     : https://prove2.me/theorems/75e3de94-98ba-4d91-8eb1-97985cbbf236
-- title:
--   Lower Equiv Upper Swap
-- statement:
--   Definitions and structural lemmas for Lower Equiv Upper Swap, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LowerEquivUpperSwap.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
namespace GlobalTheory.SmGL.SwapBlocks
section General
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
end General
section Blocks
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n]
end Blocks
section Local
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
end Local
end GlobalTheory.SmGL.SwapBlocks


