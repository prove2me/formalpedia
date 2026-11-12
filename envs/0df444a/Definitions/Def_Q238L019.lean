-- Prove2me | Definitions.Def_Q238L019
-- name    : Q238L019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:23:51.860201+00:00
-- url     : https://prove2.me/theorems/c250ba1b-4cb2-4fba-8570-dfcf0a958629
-- title:
--   Definitions bundle Q238L019 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 146 declarations of OpenAI's Lean: 142 definitions, 2 inductive types or structures, 1 instance and 1 theorem. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.advancePack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.choicesBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.drawPack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.optionBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.oracleBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.outputPack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.partBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.runPack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.scorePack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.seedBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.stateBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.stepContext`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.tableBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.contextBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.rowBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.weightedRowBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFill.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.same`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.flipped`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.leftData`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.leftNode`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.mixed`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.mixedCommon`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.rightData`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.rightNode`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.successNode`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.taggedPair`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.contextBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.count`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.scale`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.size`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.anchorInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.ranks`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.src`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.raw`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.count`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.countRange` and 104 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_IntegralRecoveryAll`, `KMedianRecovery_Algorithms_IntegralRecoveryGuesses`, `KMedianRecovery_Algorithms_IntegralRecoveryMachine`, `KMedianRecovery_Algorithms_IntegralRecoverySuccess`, `KMedianRecovery_Branching_CategoricalChoice`, `KMedianRecovery_Branching_CategoricalOutput`, `KMedianRecovery_Branching_CategoricalRawPrep`, `KMedianRecovery_Branching_CategoricalScore`, `KMedianRecovery_Branching_CategoricalSize`, `KMedianRecovery_Branching_CategoricalTable`, `KMedianRecovery_Branching_CopyComputes`, `KMedianRecovery_Branching_RationalSurrogate`, `KMedianRecovery_Encoding_CoupledEncode`, `KMedianRecovery_Encoding_LengthEncode`, `KMedianRecovery_Encoding_RationalCap`, `KMedianRecovery_Encoding_RationalLeaves`, `KMedianRecovery_Geometry_LocalBest`, `KMedianRecovery_Geometry_LocalSets`, `KMedianRecovery_Geometry_MetricAnchor`, `KMedianRecovery_Geometry_MetricArrays`, `KMedianRecovery_Machines_DeleteFold`, `KMedianRecovery_Machines_LengthQuery`, `KMedianRecovery_Machines_MatchFold`, `KMedianRecovery_Machines_MatchSize`, `KMedianRecovery_Machines_RecoveryOptionMachine`, `KMedianRecovery_Machines_RefineMachine`, `KMedianRecovery_Machines_ResolveMachine`, `KMedianRecovery_Machines_ScanMachine`, `KMedianRecovery_Machines_SensitiveMachine`, `KMedianRecovery_Machines_SuffixMachine`, `KMedianRecovery_Recovery_CoupledResolve`, `KMedianRecovery_Recovery_CrossEdge`, `KMedianRecovery_Recovery_FirstPresent`, `KMedianRecovery_Recovery_InitialAuto`, `KMedianRecovery_Recovery_InitialCorrect`, `KMedianRecovery_Recovery_LeafOrder`, `KMedianRecovery_Recovery_LengthCandidates`, `KMedianRecovery_Recovery_OrientedSearch`, `KMedianRecovery_Recovery_Pack7`, `KMedianRecovery_Recovery_PlanResult`, `KMedianRecovery_Recovery_RecoveryContext`, `KMedianRecovery_Recovery_RecoveryEnumeration`, `KMedianRecovery_Recovery_RegularChain`, `KMedianRecovery_Sampling_InverseCDF`, `KMedianRecovery_Sampling_SamplerContext`, `KMedianRecovery_Sampling_SamplerDraw`, `KMedianRecovery_Sampling_SamplerParameters`, `KMedianRecovery_Sampling_SamplerResources`, `KMedianRecovery_Sampling_SamplerWeights`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L006`, `Q238L008` and `Q238L009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L025` and `Q238L026`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_one_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_zero_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.bagWords_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginal_pack_s238r`, `OAI.MetricKMedianRecovery.RationalLeaves.prefix_leaf_s238r` and `OAI.MetricKMedianRecovery.RationalLeaves.zero_free_replay_s238r`; the proofs of `OAI.MetricKMedianRecovery.RationalLeaves.prefix_leaf_s238r` and `OAI.MetricKMedianRecovery.RationalLeaves.zero_free_replay_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L006
import Definitions.Def_Q238L008
import Definitions.Def_Q238L009

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyComputes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
lemma encode_append (ws vs : List (List Bool)) : encode (ws++vs)=encode ws++encode vs := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [List.cons_append,encode,cons,pairBits,ih,List.cons_append,List.append_assoc]
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryEllipsoidInitial
open RationalMatrix WordList

def pack (n : ℕ) (q : ℚ) : List Bool := pairBits (List.replicate n true,BinaryRational.encode q)
end BinaryEllipsoidInitial
end
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid RationalHeight
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [PseudoMetricSpace V]

attribute [local instance] metric

def leaf (key : ℕ) (i : V) (s : ℚ) : Label V := Sum.inr (key,i,s)

variable [DecidableEq V]

def shorten (key : ℕ) (i : V) (l u : ℚ) : Label V → Label V :=
  Equiv.swap (leaf key i u) (leaf key i l)

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LeafOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
instance labelLinearOrder {V : Type*} [LinearOrder V] : LinearOrder (Label V) :=
  inferInstanceAs (LinearOrder (V ⊕ₗ (ℕ ×ₗ (V ×ₗ ℚ))))
end MetricKMedianRecovery.RationalLeaves

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves
variable {V : Type*} [DecidableEq V] {d : ℕ}

def Correction.apply : Correction V → Label V → Label V
  | .identity => id
  | .shorten key i l u => RationalLeaves.shorten key i l u

structure State (V : Type*) where
  B : Finset (Label V)
  P : List (List (Label V))
  correction : Correction V
  lam : ℚ
  lam' : ℚ
  T : List (List (Label V))
  U : List (List (Label V))

def State.mapPrefix (s : State V) := s.P.map (List.map s.correction.apply)
def State.mapFree (s : State V) := s.B.image s.correction.apply

structure Output (V : Type*) where
  B : Finset (Label V)
  lam : ℚ
  P : List (List (Label V))

attribute [local instance] RationalLeaves.metric

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoupledResolve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge

section
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves CanonicalLengthView
variable {V : Type*} [LinearOrder V] {d : ℕ}

abbrev Outcome (V : Type*) := Output V ⊕ State V

attribute [local instance] RationalLeaves.metric

end

open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves
attribute [local instance] RationalLeaves.metric

end MetricKMedianRecovery.CanonicalCoupledMerge

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
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def c (i : ℕ) (x : List Bool) : List Bool := field i (extractPrefix x)
noncomputable def leaves (x : List Bool) : List Bool := discardPrefix (discardPrefix x)
end MetricKMedianRecovery.BitMachine.BinarySampler

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_InverseCDF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDyadic
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
noncomputable def scale (x : List Bool) : ℚ := (value (power x):ℚ)
noncomputable def count (x : List Bool) : List Bool :=
  (⌊BinaryRational.decode (discardPrefix x)*BinaryRational.decode (extractPrefix x)⌋₊).bits
end MetricKMedianRecovery.BitMachine.BinaryDyadic

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Weights
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def stateInput (x : List Bool) : List Bool := pairBits (extractPrefix x,head (discardPrefix x))
end MetricKMedianRecovery.BitMachine.BinarySampler.Weights

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {E : Type*} {a T : ℕ}
def optionBits (enc : E→List Bool) (o : Option E) : List Bool := encode (o.toList.map enc)
def tableBits (enc : E→List Bool) (r : Fin a→Fin T→Option E) : List Bool :=
  encode (List.ofFn (fun j=>encode (List.ofFn (fun t=>optionBits enc (r j t)))))
def choicesBits (enc : E→List Bool) (c : Fin a→E) : List Bool := encode (List.ofFn (fun j=>enc (c j)))
def seedBits (s : Fin a→Fin T) : List Bool := encode (List.ofFn (fun j=>(s j).val.bits))
def drawPack (enc : E→List Bool) (r : Fin a→Fin T→Option E) (s : Fin a→Fin T) (skip : ℕ) : List Bool :=
  encode [tableBits enc r,seedBits s,skip.bits]

def advancePack (enc : E→List Bool) (r : Fin a→Fin T→Option E) (t : Fin T) (c : Fin a→E) : List Bool :=
  encode [tableBits enc r,choicesBits enc c,t.val.bits]
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalScore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a T L : ℕ}
def partBits (part : Fin q→Fin a) : List Bool := encode (List.ofFn (fun e=>(part e).val.bits))
def oracleBits (seed : Categorical.OracleSeed (Fin q) a T L) : List Bool :=
  encode (List.ofFn (fun e=>encode (List.ofFn (fun l=>seedBits (seed e l)))))
def scorePack (ctx : List Bool) (part : Fin q→Fin a) (r : Fin a→Fin T→Option (Fin q))
    (seed : Categorical.OracleSeed (Fin q) a T L) : List Bool :=
  encode [ctx,tableBits elemBits r,oracleBits seed,partBits part]
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletion
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )

def rowBits {q : ℕ} (b : ℚ) (d : Fin q→ℚ) : List Bool :=
  encode [BinaryRational.encode b,encode (List.ofFn (fun e=>BinaryRational.encode (d e)))]
attribute [local irreducible] mapWith

def weightedRowBits {q : ℕ} (w b : ℚ) (d : Fin q→ℚ) : List Bool := pairBits (BinaryRational.encode w,rowBits b d)
end MetricKMedianRecovery.BitMachine.BinaryCompletion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricArrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricArrays
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n p q : ℕ}
noncomputable def row (x : List Bool) : List Bool := Lookup.run
  (pairBits (discardPrefix x,field 0 (extractPrefix x)))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryMetricArrays

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a T L : ℕ}
def stepContext (ctx : List Bool) (part : Fin q→Fin a) (T : ℕ) : List Bool :=
  encode [ctx,partBits part,List.replicate T true]
def stateBits (s : Categorical.GreedyState (Fin q) a T) : List Bool := encode [s.1.bits,tableBits elemBits s.2]
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a T L : ℕ}
def runPack (ctx : List Bool) (part : Fin q→Fin a) (T : ℕ)
    (seeds : List (Categorical.OracleSeed (Fin q) a T L)) : List Bool :=
  encode [ctx,partBits part,List.replicate a true,List.replicate T true,encode (seeds.map oracleBits)]
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a T L : ℕ}
def outputPack (ctx : List Bool) (part : Fin q→Fin a)
    (seed : (Fin T→Categorical.OracleSeed (Fin q) a T L)×(Fin a→Fin T)) : List Bool :=
  pairBits (runPack ctx part T (List.ofFn seed.1),seedBits seed.2)
end MetricKMedianRecovery.BitMachine.BinaryCategorical

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources
open WordOperations WordList BinaryArithmetic
open Categorical.Explicit

def pack (q a : ℕ) : List Bool := pairBits (List.replicate q true,List.replicate a true)
attribute [local irreducible] RawUnary.run
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalRawPrep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
open Categorical.Explicit
variable {q a : ℕ}
noncomputable def pack (ctx : List Bool) (part : Fin q→Fin a)
    (bits : Categorical.BinaryOracleIndex (Fin q) a (exponent a) (samples q a)→Bool) : List Bool :=
  pairBits (encode [ctx,partBits part,List.replicate a true],Tape.raw q a (exponent a) (samples q a) bits)
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionFill
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a : ℕ}
def pack (part : Fin q→Fin a) (o : Fin a→Fin q) (xs : List (Fin q)) :=
  encode [encode (List.ofFn (fun e=>(part e).val.bits)),encode (List.ofFn (fun j=>(o j).val.bits)),encode (xs.map elemBits)]
end MetricKMedianRecovery.BitMachine.BinaryCompletionFill

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RationalSurrogate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletion
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q p r : ℕ}
def contextBits (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ) : List Bool :=
  encode [k.bits,encode (List.ofFn (fun i=>rowBits (base i) (distance i))),
    encode (List.ofFn (fun i=>weightedRowBits (weight i) (redBase i) (redDistance i)))]
end MetricKMedianRecovery.BitMachine.BinaryCompletion

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
open BinaryOpeningPayment (field )
noncomputable def qbits : List Bool→List Bool := extractPrefix ∘ discardPrefix
noncomputable def cbits : List Bool→List Bool := extractPrefix ∘ discardPrefix ∘ discardPrefix
noncomputable def bbits : List Bool→List Bool := UnaryResources.inc ∘ discardPrefix ∘ discardPrefix ∘ discardPrefix
noncomputable def src (j : ℕ) : List Bool→List Bool := field j ∘ extractPrefix
attribute [local irreducible] BinaryEllipsoidInitial.indices
noncomputable def zeros (x : List Bool) : List Bool := mapWith (fun _=>[]) (pairBits ([],BinaryEllipsoidInitial.indices (src 6 x)))
attribute [local irreducible] mapWith
attribute [local irreducible] src zeros qbits
noncomputable def zeroContext (x : List Bool) : List Bool :=
  encode [src 0 x,src 1 x,src 2 x,src 3 x,src 4 x,src 5 x,zeros x,zeros x,encode [[]],qbits x,[],src 8 x]
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RecoveryEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList
open BinaryOpeningPayment (field )
attribute [local irreducible] zeroContext
noncomputable def promote (x : List Bool) : List Bool := pairBits (extractPrefix x,pairBits (discardPrefix x,pairBits ([],[])))
noncomputable def range (x : List Bool) : List Bool := BinaryEllipsoidInitial.indices (field 6 x++[true])
noncomputable def blueRange (x : List Bool) : List Bool := BinaryEllipsoidInitial.indices (field 7 x)
attribute [local irreducible] mapWith
noncomputable def metricContext (x : List Bool) : List Bool := encode [field 0 x,field 1 x]
attribute [local irreducible] metricContext
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_RecoveryOptionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
noncomputable def replaceState (x : List Bool) : List Bool :=
  encode [src 0 x,src 1 x,src 2 x,src 3 x,src 4 x,field 0 (discardPrefix x),src 6 x,src 7 x,src 8 x,src 9 x]
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Parameters
open WordOperations WordList BinaryArithmetic Polynomial RadiusMenus Sampling Sampling.Comparison
open BinaryOpeningPayment (field )
attribute [local irreducible] bound
noncomputable def nword (x : List Bool) : List Bool := Count.run (field 2 x)
end MetricKMedianRecovery.BitMachine.BinarySampler.Parameters

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
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def input (x : List Bool) : List Bool := pairBits (field 0 x,field 1 x)
end MetricKMedianRecovery.BitMachine.BinarySampler.Draw

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Loop
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
def initial : List Bool := encode [pairBits ([],[])]
noncomputable def fixedContext (x : List Bool) : List Bool := pairBits (field 0 x,field 2 x)
end MetricKMedianRecovery.BitMachine.BinarySampler.Loop

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery
open WordOperations WordList
open BinaryOpeningPayment (field )
noncomputable def src (j : ℕ) : List Bool→List Bool := field j ∘ extractPrefix
noncomputable def params : List Bool→List Bool := extractPrefix
noncomputable def sampleRaw : List Bool→List Bool := extractPrefix ∘ discardPrefix ∘ discardPrefix
noncomputable def completeRaw : List Bool→List Bool := discardPrefix ∘ discardPrefix ∘ discardPrefix
noncomputable def extra : List Bool→List Bool := extractPrefix ∘ discardPrefix
attribute [local irreducible] src extra completeRaw
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoverySuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
open WordOperations WordList Sampling.Comparison BinaryArithmetic
noncomputable def raw : List Bool→List Bool := discardPrefix ∘ discardPrefix
attribute [local irreducible] raw extra
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryGuesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses
open WordOperations WordList
open BinaryOpeningPayment (field )
attribute [local irreducible] Count.run src
noncomputable def countRange (x : List Bool) : List Bool := BinaryEllipsoidInitial.indices (src 1 x++[true])
noncomputable def source (j : ℕ) : List Bool→List Bool := src j ∘ extractPrefix
noncomputable def count (x : List Bool) : List Bool := discardPrefix (discardPrefix x)
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LengthEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLength
open WordOperations WordList RationalLeaves CanonicalLengthView BinaryArithmetic
open BinaryOpeningPayment (field )
def cf (n : ℕ) : List Bool → List Bool := field n ∘ extractPrefix
def pf (n : ℕ) : List Bool → List Bool := field n ∘ discardPrefix
noncomputable def isFree (x : List Bool) : Bool := decide (value (pf 0 x)=0)
noncomputable def source (x : List Bool) : List Bool :=
  if isFree x then cf 2 x else pf 3 x++cons (pf 1 x) (pf 4 x)
noncomputable def target (x : List Bool) : List Bool :=
  if isFree x then cf 2 x++cons (pf 2 x) [] else pf 3 x++pf 4 x
end MetricKMedianRecovery.BitMachine.BinaryLength

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SuffixMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySuffix
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field )
noncomputable def pruneOp (x : List Bool) : List Bool := extractPrefix x++field 2 (discardPrefix x)
noncomputable def growOp (x : List Bool) : List Bool :=
  extractPrefix (extractPrefix x)++cons (field 1 (discardPrefix x)) (field 2 (discardPrefix x))++
    cons (discardPrefix (extractPrefix x)) []
end MetricKMedianRecovery.BitMachine.BinarySuffix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_OrientedSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryOrientedSearch
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
noncomputable def reversedInput (x : List Bool) : List Bool := pairBits (extractPrefix (extractPrefix x),
  BinaryRational.encode (BinaryRational.decode (discardPrefix (extractPrefix x))-BinaryRational.decode (discardPrefix x)))
noncomputable def reversed (query : List Bool→List Bool) : List Bool→List Bool := query ∘ reversedInput
noncomputable def reverseContext (x : List Bool) : List Bool := pairBits (field 1 x,field 4 x)
noncomputable def reverseInput (x : List Bool) : List Bool := encode
  [field 0 x,reverseContext x,field 2 x,field 3 x,field 4 x]
noncomputable def reflect (x : List Bool) : List Bool := pairBits
  (BinaryRational.encode (BinaryRational.decode (extractPrefix x)-BinaryRational.decode (discardPrefix (discardPrefix x))),
   BinaryRational.encode (BinaryRational.decode (extractPrefix x)-BinaryRational.decode (extractPrefix (discardPrefix x))))
noncomputable def isReversed (query : List Bool→List Bool) (x : List Bool) : Bool :=
  decide (value (query (pairBits (field 1 x,BinaryRational.encode 0)))<value (field 2 x))
end MetricKMedianRecovery.BitMachine.BinaryOrientedSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LengthQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLengthQuery
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field )
def cf (n : ℕ) : List Bool→List Bool := field n ∘ extractPrefix
noncomputable def isZero (x : List Bool) : Bool := decide (BinaryRational.decode (discardPrefix x)=0)
noncomputable def isUpper (x : List Bool) : Bool := decide (BinaryRational.decode (discardPrefix x)=BinaryRational.decode (cf 5 x))
end MetricKMedianRecovery.BitMachine.BinaryLengthQuery

namespace MetricKMedianRecovery.BitMachine.BinaryLengthSearch
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field )
def lower : List Bool→List Bool := extractPrefix ∘ discardPrefix
def upper : List Bool→List Bool := discardPrefix ∘ discardPrefix
def context : List Bool→List Bool := field 1 ∘ extractPrefix
def boundK : List Bool→List Bool := field 2 ∘ extractPrefix
def leftInput (x : List Bool) : List Bool := pairBits (context x,lower x)
def rightInput (x : List Bool) : List Bool := pairBits (context x,upper x)
end MetricKMedianRecovery.BitMachine.BinaryLengthSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SensitiveMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySensitive
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalLengthView
open BinaryOpeningPayment (field )
def jf (n : ℕ) : List Bool→List Bool := field n ∘ field 10
noncomputable def isFree (x : List Bool) : Bool := decide (value (jf 0 x)=0)
noncomputable def common (x : List Bool) : List Bool := if isFree x then field 7 x else jf 3 x++jf 4 x
noncomputable def small (x : List Bool) : List Bool := if isFree x then field 9 x else field 8 x
noncomputable def large (x : List Bool) : List Bool := if isFree x then field 8 x else field 9 x
noncomputable def nextQ (x : List Bool) : List Bool := true::field 2 x
end MetricKMedianRecovery.BitMachine.BinarySensitive

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalSets
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field )
def swapWords (x : List Bool) : List Bool := pairBits (discardPrefix x,extractPrefix x)
end MetricKMedianRecovery.BitMachine.BinaryLocalSets

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalBest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalBest
open WordOperations WordList BinaryArithmetic
noncomputable def choose (rank : List Bool→List Bool) (x : List Bool) : List Bool :=
  if value (rank (pairBits (Find.context x,Find.item x))) < value (rank (pairBits (Find.context x,Fold.accum x)))
  then Find.item x else Fold.accum x
end MetricKMedianRecovery.BitMachine.BinaryLocalBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricAnchor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricAnchor
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def rectInput (x : List Bool) : List Bool := encode
  [field 0 x,BinaryEllipsoidInitial.indices (field 1 x),field 2 x]
end MetricKMedianRecovery.BitMachine.BinaryMetricAnchor

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def src (j : ℕ) : List Bool→List Bool := field j ∘ extractPrefix
noncomputable def anchorInput (x : List Bool) : List Bool :=
  encode [src 0 x,src 1 x,src 2 x,src 3 x,discardPrefix x]
noncomputable def ranks (x : List Bool) : List Bool := BinaryEllipsoidInitial.indices (Count.run (field 3 x)++[true])
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_CoupledEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )
noncomputable def same (x : List Bool) : List Bool := encode [field 0 x,field 2 x,[],field 1 x,field 1 x,field 3 x,field 4 x]
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_DeleteFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDelete
open WordOperations WordList RationalLeaves CanonicalDelete
open BinaryOpeningPayment (field )

def contextBits (base C ci : List Bool) := encode [base,C,ci]

end MetricKMedianRecovery.BitMachine.BinaryDelete

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMatch
open WordOperations WordList RationalLeaves CanonicalMatch
open BinaryOpeningPayment (field )

def cf (n : ℕ) (x : List Bool) : List Bool := field n (extractPrefix x)
def sf (n : ℕ) (x : List Bool) : List Bool := field n (discardPrefix (discardPrefix x))
def item (x : List Bool) : List Bool := extractPrefix (discardPrefix x)
noncomputable def front (x : List Bool) : List Bool := sf 0 x++WordList.cons (item x) []
end MetricKMedianRecovery.BitMachine.BinaryMatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PlanResult
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPlanResult
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge CanonicalLengthView
open BinaryOpeningPayment (field )

def sf (n : ℕ) : List Bool→List Bool := field n ∘ field 0
def rf (n : ℕ) : List Bool→List Bool := field n ∘ field 3
noncomputable def success (x : List Bool) : Bool := decide (value (rf 0 x)=0)
noncomputable def rightHeight (x : List Bool) : List Bool := if success x then rf 1 x else rf 2 x
noncomputable def price : List Bool→List Bool := field 7 ∘ sf 0
noncomputable def root : List Bool→List Bool := field 1 ∘ sf 10
noncomputable def common : List Bool→List Bool := BinarySensitive.common ∘ field 0
noncomputable def leafInput (x : List Bool) : List Bool := encode [field 1 x,field 2 x,price x,sf 3 x,root x,common x,rf 1 x,rightHeight x,rf 3 x,rf 4 x]
end MetricKMedianRecovery.BitMachine.BinaryPlanResult

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRegular
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryOpeningPayment (field )

noncomputable def poolInput (x : List Bool) : List Bool := pairBits (field 1 x,field 2 (field 0 x))
noncomputable def state0 (x : List Bool) : List Bool := encode [[],field 3 x,[]]
end MetricKMedianRecovery.BitMachine.BinaryRegular

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
open BinaryOpeningPayment (field )
noncomputable def source (x : List Bool) : List Bool := field 1 (discardPrefix x)
end MetricKMedianRecovery.BitMachine.BinaryRefine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CrossEdge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCross
open WordOperations WordList RationalLeaves BinaryArithmetic
open BinaryOpeningPayment (field )
noncomputable def leftNode : List Bool → List Bool := extractPrefix ∘ discardPrefix
noncomputable def rightNode : List Bool → List Bool := discardPrefix ∘ discardPrefix
noncomputable def leftData (x : List Bool) : List Bool := pairBits (extractPrefix x,leftNode x)
noncomputable def rightData (x : List Bool) : List Bool := pairBits (extractPrefix x,rightNode x)

noncomputable def mixed (x : List Bool) : List Bool := pairBits (extractPrefix (rightNode x),discardPrefix (leftNode x))
noncomputable def successNode (x : List Bool) : List Bool := encode [(0:ℕ).bits,x,[]]
noncomputable def taggedPair (tag : ℕ) (x : List Bool) : List Bool := encode [tag.bits,extractPrefix x,discardPrefix x]
noncomputable def mixedCommon (x : List Bool) : List Bool := taggedPair 1 (pairBits (mixed x,discardPrefix (rightNode x)))

noncomputable def flipped (x : List Bool) : List Bool := pairBits (extractPrefix x,pairBits (rightNode x,leftNode x))
end MetricKMedianRecovery.BitMachine.BinaryCross

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLength
open WordOperations WordList RationalLeaves CanonicalLengthView BinaryArithmetic CanonicalMergeRefinement
open BinaryOpeningPayment (field )
attribute [local irreducible] WordList.mapWith
noncomputable def freeOp (x : List Bool) : List Bool := encode [(0:ℕ).bits,extractPrefix x,discardPrefix x,[],[]]
noncomputable def paidOp (x : List Bool) : List Bool := encode [(1:ℕ).bits,pf 1 x,[],pf 0 x,pf 2 x]
end MetricKMedianRecovery.BitMachine.BinaryLength

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ResolveMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryResolve
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge CanonicalLengthView
open BinaryOpeningPayment (field )
def rf (n : ℕ) : List Bool→List Bool := field n ∘ field 9
def bf (n : ℕ) : List Bool→List Bool := field n ∘ field 0
def H : List Bool→List Bool := extractPrefix ∘ rf 1
def T : List Bool→List Bool := discardPrefix ∘ rf 1
def G : List Bool→List Bool := extractPrefix ∘ rf 2
def U : List Bool→List Bool := discardPrefix ∘ rf 2
noncomputable def prefixH (x : List Bool) : List Bool := field 8 x++cons (H x) []
noncomputable def finishInput (x : List Bool) : List Bool := encode [field 7 x,bf 7 x,prefixH x,T x]
noncomputable def sameInput (x : List Bool) : List Bool := encode [field 7 x,bf 7 x,prefixH x,T x,rf 2 x]
noncomputable def fallbackInput (x : List Bool) : List Bool := encode [field 7 x,bf 7 x,field 8 x,[]]
noncomputable def viewInput (x : List Bool) : List Bool := encode [bf 2 x,bf 2 x,H x,G x,pairBits (bf 0 x,bf 1 x)]
end MetricKMedianRecovery.BitMachine.BinaryResolve

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RegularChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRegularChain
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryOpeningPayment (field )
noncomputable def regularInput (x : List Bool) : List Bool := encode [field 0 x,field 1 x,field 5 x,field 4 x]
end MetricKMedianRecovery.BitMachine.BinaryRegularChain

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FirstPresent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.FirstPresent
open WordOperations
open CanonicalMergeCrossing
noncomputable def present (x : List Bool) : Bool := !decide (discardPrefix x=[])
end MetricKMedianRecovery.BitMachine.WordList.FirstPresent

namespace MetricKMedianRecovery.BitMachine.BinaryNodeScan
open WordOperations WordList RationalLeaves CanonicalMergeRefinement CanonicalMergeCrossing
open BinaryOpeningPayment (field )
noncomputable def suffix (x : List Bool) : List Bool := field 2 (discardPrefix x)
noncomputable def current (x : List Bool) : List Bool := field 1 (discardPrefix x)
noncomputable def transitionInput (x : List Bool) : List Bool :=
  pairBits (extractPrefix x,pairBits (current x,head (suffix x)))
noncomputable def lastNode : List Bool → List Bool := head ∘ WordList.reverse ∘ field 2
noncomputable def fallback (x : List Bool) : List Bool := encode [(1:ℕ).bits,lastNode x,field 1 x]
end MetricKMedianRecovery.BitMachine.BinaryNodeScan

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
open BinaryOpeningPayment (field )
noncomputable def cf (n : ℕ) : List Bool → List Bool := field n ∘ extractPrefix
noncomputable def mapCtx (x : List Bool) : List Bool := encode [field 0 x,field 1 x,field 2 x]
end MetricKMedianRecovery.BitMachine.BinaryScan

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFuel
open WordOperations BinaryArithmetic RationalHeight

def threshold (x : List Bool) : ℚ := BinaryRational.decode (extractPrefix x)
def power (x : List Bool) : ℚ := BinaryRational.decode (extractPrefix (discardPrefix x))
def count : List Bool → List Bool := discardPrefix ∘ discardPrefix

end MetricKMedianRecovery.BitMachine.BinaryPhaseFuel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialAuto
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitialAuto
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field )
variable {m d : ℕ}
noncomputable def size (x : List Bool) : List Bool := field 1 x++Count.run (field 2 x)
end MetricKMedianRecovery.BitMachine.BinaryInitialAuto

end OAI
end


