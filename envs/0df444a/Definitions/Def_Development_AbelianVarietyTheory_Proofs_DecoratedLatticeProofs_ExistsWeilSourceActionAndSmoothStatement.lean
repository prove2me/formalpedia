-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsWeilSourceActionAndSmoothStatement
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsWeilSourceActionAndSmoothStatement
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:20:57.442176+00:00
-- url     : https://prove2.me/theorems/aaf9ecb7-a6b2-400e-a62d-1ff461fc3d10
-- title:
--   Exists Weil Source Action And Smooth Statement
-- statement:
--   Definitions and structural lemmas for Exists Weil Source Action And Smooth Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsWeilSourceActionAndSmoothStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsWeilSourceActionAndSmooth
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


