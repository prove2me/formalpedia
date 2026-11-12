-- Prove2me | Definitions.Def_Q238L031
-- name    : Q238L031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:28:59.605425+00:00
-- url     : https://prove2.me/theorems/3946b37c-960d-4cd2-ad85-7fa9529760bb
-- title:
--   Definitions bundle Q238L031 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 16 definitions. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.ctxBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Draw.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.config`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingReference.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.optionBits`, `OAI.MetricKMedianRecovery.BitMachine.BinarySanitizedBest.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryScan.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryWeakSolve.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.pack`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Frame.Stopped`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Frame.Valid`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Frame.value`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.transition`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_CandidateSanitize`, `KMedianRecovery_Branching_ObservableCapacity`, `KMedianRecovery_Geometry_RoundingMatrix`, `KMedianRecovery_Machines_LoopInvariant`, `KMedianRecovery_Machines_RefineMachine`, `KMedianRecovery_Machines_ScanMachine`, `KMedianRecovery_Recovery_Pack8`, `KMedianRecovery_Recovery_RecoveryContext`, `KMedianRecovery_Sampling_SamplerContext`, `KMedianRecovery_Sampling_SamplerDraw`, `KMedianRecovery_Sampling_SamplingReference`, `KMedianRecovery_Sampling_SamplingStateMachine`, `KMedianRecovery_Strictness_SurplusPostprocess`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L024`, `Q238L025` and `Q238L026` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.pack_length_bound_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.recoveryContext_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.sampleContext_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_context_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_source_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atOption_none_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.run_source_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.cutOp_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.radii_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.fold_length_cap_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.atPrefix_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.ball_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.radius_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.remove_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.run_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Weights.weight_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingReference.entries_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryScan.nodes_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.integral_spec_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.localInput_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.check_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.completion_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.run_pack_s238r` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.transition_valid_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.produce_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.pack_length_bound_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.run_initial_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.select_bits_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.run_output_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.run_output_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.run_source_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.run_output_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.recoveryContext_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.sampleContext_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_context_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_source_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atOption_none_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.run_source_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.cutOp_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRegularChain.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.radii_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.fold_length_cap_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.atPrefix_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.ball_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.radius_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.remove_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.run_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Weights.weight_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.reference_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingReference.entries_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryScan.nodes_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.integral_spec_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.localInput_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.check_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.completion_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.run_pack_s238r` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.transition_valid_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L024
import Definitions.Def_Q238L025
import Definitions.Def_Q238L026

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open UnaryResources
namespace BinaryWeakSolve
open RationalMatrix

def pack (n p s R : ℕ) (rs : List (Row n)) : List Bool :=
  pairBits (List.replicate n true,pairBits (List.replicate p true,
    pairBits (List.replicate s true,pairBits (R.bits,BinaryRow.rowsEncode rs))))
end BinaryWeakSolve
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingReference
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
open BinaryRationalSort (entryBits)
attribute [local irreducible] WordList.mapWith
variable {n l : ℕ}
def pack (Δ : ℚ) (A : Finset (Fin n)) (v : Fin l→Fin n) (r : Fin l→ℚ) (row : Fin n→ℚ) : List Bool :=
  encode [n.bits,BinaryRational.encode Δ,BinaryFinSet.encode A,
    encode (List.ofFn (fun j=>leafBits (v j) (r j))),RationalMatrix.rowEncode row]
end MetricKMedianRecovery.BitMachine.BinarySamplingReference

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingStateMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingState
open WordOperations WordList BinaryArithmetic RationalSampling
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
def optionBits (s : Option (RationalSampling.State n)) : List Bool := WordList.encode (s.toList.map encode)
end MetricKMedianRecovery.BitMachine.BinarySamplingState

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
def config (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) : List Bool :=
  encode [n.bits,RationalMatrix.encode δ,BinaryFinSet.encode D,BinaryFinSet.encode F,BinaryFinSet.encode S,
    BinaryRational.encode Δ,BinaryRational.encode P,BinaryRational.encode κ,m.bits,BinaryMenu.weights M E J]
end MetricKMedianRecovery.BitMachine.BinarySampler

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_CandidateSanitize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySanitizedBest
open WordOperations WordList
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (k : ℕ) (xs : List (List Bool)) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.encode D,BinaryFinSet.encode F,BinaryFinSet.encode S,k.bits,encode xs]
end MetricKMedianRecovery.BitMachine.BinarySanitizedBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_ObservableCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryZeroBranch
open WordOperations WordList BinaryBranchContext BinaryBranchProgram BinaryArithmetic
attribute [local instance] Classical.propDecidable
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (q : ℕ) (extra : List Bool) : List Bool :=
  BinaryBranchContext.pack δ D F S Δ s colors (fun _=>0 : Fin n→Fin 1) q 0 extra
end MetricKMedianRecovery.BitMachine.BinaryZeroBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_RoundingMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (u : ℚ) (cap : ℕ) : List Bool :=
  encode [RationalMatrix.encode δ,List.replicate n true,BinaryRational.encode u,cap.bits]
end MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopInvariant
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves RationalHeight
variable {V : Type*} [LinearOrder V] {d : ℕ}

def transition (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision k : ℕ) (f : Frame V) : Frame V :=
  match f.out,f.n with
  | .inr s,n+1=>⟨f.q+1,n,step loc distance F v M N precision f.q n k s⟩
  | _,_=>f

def Frame.value (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision k : ℕ) (f : Frame V) : Output V :=
  match f.out with
  | .inl o=>o
  | .inr s=>run loc distance F v M N precision k f.q f.n s

def Frame.Stopped (f : Frame V) : Prop := match f.out with
  | .inl _=>True
  | .inr _=>f.n=0

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

def Frame.Valid (loc : Fin d→V) (F : Finset V) (v eta lo hi : ℝ) (total k h p : ℕ) (f : Frame V) : Prop :=
  f.q+f.n=total ∧ match f.out with
  | .inl o=>o.Correct loc F v eta lo hi total k ∧ o.Resources F f.q h p
  | .inr s=>Certified loc F v eta lo hi f.q f.n k s ∧ s.Resources F f.q h p ∧ s.correction.Keys f.q

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_RefineMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRefine
open WordOperations WordList RationalLeaves CanonicalMergeRefinement
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_encode)
def ctxBits {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key spare : ℕ) : List Bool :=
  encode [setBits F,labels R,key.bits,spare.bits]
end MetricKMedianRecovery.BitMachine.BinaryRefine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ScanMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryScan
open WordOperations WordList RationalLeaves CanonicalMergeCrossing
open BinaryCross (ctxBits nodeBits resultBits)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_encode)
def pack {m : ℕ} (base : List Bool) (F Q : Finset (Label (Fin m))) (k n q : ℕ)
    (U : List (List (Label (Fin m)))) (H : List (Label (Fin m))) (T S : List (List (Label (Fin m)))) : List Bool :=
  encode [base,List.replicate n true,List.replicate q true,ctxBits F Q k,historyBits U,nodeBits (H,T),historyBits S]
end MetricKMedianRecovery.BitMachine.BinaryScan

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RecoveryContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
def pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
    (s : RationalSampling.State n) (m : ℕ) (extra raw : List Bool) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.encode D,BinaryFinSet.encode F,BinaryFinSet.encode S,
    BinaryRational.encode Δ,BinarySamplingState.encode s,List.replicate n true,List.replicate m true,extra,raw]
attribute [local irreducible] BinaryEllipsoidInitial.indices
attribute [local irreducible] mapWith
attribute [local irreducible] src zeros qbits
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerDraw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Draw
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
def pack (cfg : List Bool) (s : Option (RationalSampling.State n)) (b : ℕ) (tape : List Bool) : List Bool :=
  encode [cfg,BinarySamplingState.optionBits s,List.replicate b true,tape]
end MetricKMedianRecovery.BitMachine.BinarySampler.Draw

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_SurplusPostprocess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field field_encode)
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
def pack (distance : Fin m→Fin d→ℚ) (F S : Finset (Fin m)) (k : ℕ) : List Bool :=
  encode [Rectangular.encode distance,List.replicate d true,BinaryFinSet.encode F,BinaryFinSet.encode S,k.bits]
end MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess

end OAI
end


