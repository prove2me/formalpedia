-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEvaluateEntryOfMulLaw
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEvaluateEntryOfMulLaw
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:27:07.849188+00:00
-- url     : https://prove2.me/theorems/c0a5b19b-e42f-4062-9b2d-1ceb7eeb123e
-- title:
--   Partial Reduction Evaluate Entry Of Mul Law
-- statement:
--   Definitions and structural lemmas for Partial Reduction Evaluate Entry Of Mul Law, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionEvaluateEntryOfMulLaw.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_neg_mem_cball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped Topology
noncomputable section
namespace GlobalTheory.PartRedEval
open GlobalTheory.PartRed
section Alg
variable {k : Type} [Field k] {R Q : Type} [DecidableEq R] [DecidableEq Q]
end Alg
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q]
def ballGrp (s : kˣ) : AddSubgroup k where
  carrier := cball s
  add_mem' := add_mem_cball
  zero_mem' := by simp [cball]
  neg_mem' := neg_mem_cball
variable [MeasurableSpace k] [BorelSpace k]
end GlobalTheory.PartRedEval


