-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:58.881094+00:00
-- url     : https://prove2.me/theorems/1178be0e-29ac-4637-b027-7072bec4fc45
-- title:
--   Subsingleton Jacquet Of Perm
-- statement:
--   Definitions and structural lemmas for Subsingleton Jacquet Of Perm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SubsingletonJacquetOfPerm.lean

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
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
namespace GlobalTheory.SmGL.CuspMax
variable {R : Type} [CommRing R] {α β n : Type} {m : α → Type} {m' : β → Type}
  [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype β] [LinearOrder β] [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)]
  [Fintype n] [DecidableEq n]
end GlobalTheory.SmGL.CuspMax


