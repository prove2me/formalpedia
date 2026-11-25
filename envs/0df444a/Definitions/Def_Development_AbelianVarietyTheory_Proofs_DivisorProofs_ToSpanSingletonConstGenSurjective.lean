-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ToSpanSingletonConstGenSurjective
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ToSpanSingletonConstGenSurjective
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:30:23.825161+00:00
-- url     : https://prove2.me/theorems/1575bffe-7597-480b-8fbf-0bd528d5fde3
-- title:
--   To Span Singleton Const Gen Surjective
-- statement:
--   Definitions and structural lemmas for To Span Singleton Const Gen Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ToSpanSingletonConstGenSurjective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace GlobalTheory
namespace PDivGroup
variable (p : ℕ) (O : Type) [CommRing O] [Fact p.Prime]
variable [Nontrivial O]
end PDivGroup
end GlobalTheory


