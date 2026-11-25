-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingInfinite
-- name    : GroundTheory_GlobalFields_KummerTheory_SplittingInfinite
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:46:05.651329+00:00
-- url     : https://prove2.me/theorems/ad779779-4268-4aa7-95b7-53fbaef483ca
-- title:
--   Splitting Infinite
-- statement:
--   Definitions and structural lemmas for Splitting Infinite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/SplittingInfinite.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Global
open NumberField Module
open scoped NumberField.LiesOver TensorProduct
namespace InfinitePlace
variable {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L]
def SplitsCompletely (v : NumberField.InfinitePlace K) : Prop :=
  ∀ w : NumberField.InfinitePlace L, w.LiesOver v → w.IsUnramified K
variable {L} (v : NumberField.InfinitePlace K)
variable [NumberField K] [NumberField L]
end InfinitePlace
end GroundTheory.Global


