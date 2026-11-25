-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_EmbSInjective
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_EmbSInjective
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T08:46:25.924408+00:00
-- url     : https://prove2.me/theorems/98db69c4-2c2c-5701-977e-e65908b1b4ee
-- title:
--   Emb SInjective
-- statement:
--   Definitions and structural lemmas for Emb SInjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/EmbSInjective.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_BoxFundT
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_SwapMp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MeasurablePhiInv
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
def embS {K : Type} [Field K] {ι : Type} (φ : ι → (K →+* ℂ)) (s : ℂ) : K →+ (ι → ℂ) where
  toFun a := fun i => s * φ i a
  map_zero' := by funext i; simp
  map_add' a b := by funext i; simp [mul_add]
end Formalism.L2.SG.NGCut.SplitEmbedding


