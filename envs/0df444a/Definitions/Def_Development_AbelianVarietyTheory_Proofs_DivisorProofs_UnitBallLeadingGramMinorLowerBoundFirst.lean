-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallLeadingGramMinorLowerBoundFirst
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallLeadingGramMinorLowerBoundFirst
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:38:11.717496+00:00
-- url     : https://prove2.me/theorems/c89133c4-58e4-49f5-8647-272177f5704f
-- title:
--   Unit Ball Leading Gram Minor Lower Bound First
-- statement:
--   Definitions and structural lemmas for Unit Ball Leading Gram Minor Lower Bound First, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitBallLeadingGramMinorLowerBoundFirst.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
namespace GlobalTheory.IntBallMinorOne
open Matrix
open scoped ComplexOrder
end GlobalTheory.IntBallMinorOne
namespace GlobalTheory.IntBallMinorOne
open Matrix
open scoped ComplexOrder
end GlobalTheory.IntBallMinorOne
namespace GlobalTheory.IntBallMinorOne
open Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end GlobalTheory.IntBallMinorOne
namespace GlobalTheory.IntBallMinorOne
open Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def eR (r : ℕ) (hr : 1 ≤ r) : Fin 1 ⊕ Fin (r - 1) ≃ Fin r :=
  finSumFinEquiv.trans (finCongr (by omega))
def eC (k : ℕ) : Fin 1 ⊕ Fin k ≃ Fin (k + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))
end GlobalTheory.IntBallMinorOne
namespace GlobalTheory.IntBallMinorOne
end GlobalTheory.IntBallMinorOne


