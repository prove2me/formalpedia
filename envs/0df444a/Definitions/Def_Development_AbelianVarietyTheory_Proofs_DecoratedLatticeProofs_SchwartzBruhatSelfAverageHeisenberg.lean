-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatSelfAverageHeisenberg
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatSelfAverageHeisenberg
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:43:13.767064+00:00
-- url     : https://prove2.me/theorems/748b9015-a6b2-4a03-bc46-71b1c41d0255
-- title:
--   Schwartz Bruhat Self Average Heisenberg
-- statement:
--   Definitions and structural lemmas for Schwartz Bruhat Self Average Heisenberg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SchwartzBruhatSelfAverageHeisenberg.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralMulOfSupport
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_omR_mul
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_omR_smooth
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_omR_val
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_orbit_locallyConstant

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
open Filter Topology
open GlobalTheory.RootEx.Unfolding (omR omR_val omR_mul omR_smooth orbit_locallyConstant opL ev)
noncomputable section
namespace GlobalTheory.PosOne
end GlobalTheory.PosOne


