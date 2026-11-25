-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CovolOneEqOne
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CovolOneEqOne
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T08:53:05.472714+00:00
-- url     : https://prove2.me/theorems/5651e5c9-f2dc-469b-aeee-1d13be8ddb54
-- title:
--   Covol One Eq One
-- statement:
--   Definitions and structural lemmas for Covol One Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CovolOneEqOne.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_EmbSInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding
namespace Formalism.L2.SG.NGCut.SplitEmbedding
def lawX {ι P : Type} (BX : P → (P → ℂ) → (P → ℂ) → ℂ) (γ x : ι → P → ℂ) : ι → P → ℂ :=
  fun v p => γ v p + x v p + BX p (γ v) (x v)
end Formalism.L2.SG.NGCut.SplitEmbedding


