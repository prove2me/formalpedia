-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PsiEqSumCoupIdx
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PsiEqSumCoupIdx
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T10:36:18.460401+00:00
-- url     : https://prove2.me/theorems/e7bef26d-fd74-4ca5-80ed-adcbc3ba3faa
-- title:
--   Psi Eq Sum Coup Idx
-- statement:
--   Definitions and structural lemmas for Psi Eq Sum Coup Idx, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PsiEqSumCoupIdx.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
noncomputable section
namespace GlobalTheory.Couple
end GlobalTheory.Couple


