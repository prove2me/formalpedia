-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HalfAddSelf
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HalfAddSelf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:46.43539+00:00
-- url     : https://prove2.me/theorems/d88b76b5-aee6-4bf0-ad78-0c2fad5fbade
-- title:
--   Half Add Self
-- statement:
--   Definitions and structural lemmas for Half Add Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HalfAddSelf.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
namespace GlobalTheory.RealWeil.PosDet
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end GlobalTheory.RealWeil.PosDet


