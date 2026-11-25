-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_PhiMapAdd
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_PhiMapAdd
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T05:56:30.153501+00:00
-- url     : https://prove2.me/theorems/74e4d0b4-7ced-497e-9e05-37869b0af1ef
-- title:
--   Phi Map Add
-- statement:
--   Definitions and structural lemmas for Phi Map Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/PhiMapAdd.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MassSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open MeasureTheory NumberField NumberField.mixedEmbedding
namespace Formalism.L2.SG.NGCut.SplitEmbedding
section Covol
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  (σ : ι ≃ {w : InfinitePlace K // w.IsComplex}) (cj : ι → Prop) [DecidablePred cj]
def phiMap (x : mixedSpace K) : ι → ℂ := fun i => if cj i then (starRingEnd ℂ) (x.2 (σ i)) else x.2 (σ i)
end Covol
end Formalism.L2.SG.NGCut.SplitEmbedding


