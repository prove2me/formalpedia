-- Prove2me | Definitions.Def_Q238K013
-- name    : Q238K013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:14:27.163439+00:00
-- url     : https://prove2.me/theorems/d1cbd39d-72ae-4485-b074-a59b7a7b4f58
-- title:
--   Definitions bundle Q238K013 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 148 declarations of OpenAI's Lean: 147 definitions and 1 theorem. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.advancePack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.choicesBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.drawPack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.optionBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.oracleBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.outputPack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.partBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.rationalMarginal`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.rationalScore`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.runPack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.scorePack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.seedBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.stateBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.stepContext`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.tableBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.rowD`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.contextBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.rowBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.weightedRowBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFill.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.contextBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.count`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.scale`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.matrix`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.normInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.callInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.start`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.boundK`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.count`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.lower`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGrid.upper`, `OAI.MetricKMedianRecovery.BitMachine.BinaryHistoryRun.historyBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.size`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.ctx`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.codes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.less`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.src` and 107 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_CandidateSanitize`, `KMedianRecovery_Algorithms_GlobalCall`, `KMedianRecovery_Algorithms_GlobalOuter`, `KMedianRecovery_Algorithms_IntegralAll`, `KMedianRecovery_Algorithms_IntegralRecoveryAll`, `KMedianRecovery_Algorithms_IntegralRecoveryGuesses`, `KMedianRecovery_Algorithms_IntegralRecoveryMachine`, `KMedianRecovery_Algorithms_IntegralRecoveryRepeat`, `KMedianRecovery_Algorithms_IntegralRecoverySuccess`, `KMedianRecovery_Branching_CategoricalChoice`, `KMedianRecovery_Branching_CategoricalOutput`, `KMedianRecovery_Branching_CategoricalRawPrep`, `KMedianRecovery_Branching_CategoricalScore`, `KMedianRecovery_Branching_CategoricalSize`, `KMedianRecovery_Branching_CategoricalTable`, `KMedianRecovery_Branching_CopyComputes`, `KMedianRecovery_Branching_PopulationMachine`, `KMedianRecovery_Branching_RationalSurrogate`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Encoding_Encode3`, `KMedianRecovery_Encoding_HistoryBits`, `KMedianRecovery_Encoding_RationalCap`, `KMedianRecovery_Encoding_RationalConstants`, `KMedianRecovery_Encoding_RationalMenus`, `KMedianRecovery_Encoding_RationalStream`, `KMedianRecovery_Encoding_UnaryParser`, `KMedianRecovery_Geometry_LocalBest`, `KMedianRecovery_Geometry_LocalFuel`, `KMedianRecovery_Geometry_LocalSets`, `KMedianRecovery_Geometry_MetricAnchor`, `KMedianRecovery_Geometry_MetricArrays`, `KMedianRecovery_Geometry_MetricCost2`, `KMedianRecovery_Geometry_NearestLeafMachine`, `KMedianRecovery_Geometry_RoundingArithmetic`, `KMedianRecovery_Geometry_RoundingMatrix`, `KMedianRecovery_Machines_DeleteFold`, `KMedianRecovery_Machines_GridMachine`, `KMedianRecovery_Machines_MenuMachine`, `KMedianRecovery_Machines_RecoveryOptionMachine`, `KMedianRecovery_Machines_SensitiveMachine`, `KMedianRecovery_Machines_StartResources`, `KMedianRecovery_Recovery_Basic`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_FinImages`, `KMedianRecovery_Recovery_FiniteCross`, `KMedianRecovery_Recovery_InitialAuto`, `KMedianRecovery_Recovery_InitialCorrect`, `KMedianRecovery_Recovery_LowCandidate`, `KMedianRecovery_Recovery_NormalizeInput`, `KMedianRecovery_Recovery_OrientedSearch`, `KMedianRecovery_Recovery_Pack7`, `KMedianRecovery_Recovery_RawSlices`, `KMedianRecovery_Recovery_RecoveryContext`, `KMedianRecovery_Recovery_RecoveryEnumeration`, `KMedianRecovery_Sampling_InverseCDF`, `KMedianRecovery_Sampling_SamplerContext`, `KMedianRecovery_Sampling_SamplerDraw`, `KMedianRecovery_Sampling_SamplerParameters`, `KMedianRecovery_Sampling_SamplerResources`, `KMedianRecovery_Sampling_SamplerUpdateParts`, `KMedianRecovery_Sampling_SamplerWeights`, `KMedianRecovery_Sampling_SamplingPotential`, `KMedianRecovery_Sampling_SamplingStateMachine`, `KMedianRecovery_Strictness_MetricSurplus`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K000`, `Q238K001`, `Q238K002` and `Q238K003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K021` and `Q238K022`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginal_pack_s238` and `OAI.MetricKMedianRecovery.IntegralAssembly.gamma_pos_s238`; the proof of `OAI.MetricKMedianRecovery.IntegralAssembly.gamma_pos_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K000
import Definitions.Def_Q238K001
import Definitions.Def_Q238K002
import Definitions.Def_Q238K003

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyComputes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
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
open BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryEllipsoidInitial
open WordList

def pack (n : ℕ) (q : ℚ) : List Bool := pairBits (List.replicate n true,BinaryRational.encode q)
end BinaryEllipsoidInitial
end
open BinaryArithmetic RationalLinearFeasibility Ellipsoid
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
namespace NaturalArray
open WordList
def encode (xs : List ℕ) : List Bool := WordList.encode (xs.map Nat.bits)
end NaturalArray
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundedDecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

namespace BinaryClearRow
open BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList

def rowD {n : ℕ} (r : Row n) : ℕ := r.bound.den*∏ i, (r.coeff i).den
end BinaryClearRow
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open BinaryArithmetic RationalLinearFeasibility
namespace BinaryOpeningActivity
open WordList

def indices {m : ℕ} (fs : List (Fin m)) : List Bool :=
  WordList.encode (fs.map (fun f=>f.val.bits))
end BinaryOpeningActivity
end
open BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_HistoryBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryHistoryRun
open BinaryArithmetic WordList EffectiveOpenability RationalPhase
def historyBits {m : ℕ} (hs : List (List (Fin m))) : List Bool :=
  encode (hs.map BinaryOpeningActivity.indices)
end MetricKMedianRecovery.BitMachine.BinaryHistoryRun

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FiniteCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalLengthView
open CanonicalMergeRefinement
variable {X : Type*} [DecidableEq X] {d : ℕ}

def Plan.root : Plan X → X
  | .free i _ => i
  | .paid _ _ i => i

end MetricKMedianRecovery.CanonicalLengthView

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RawSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.UnaryTake
def dropWords (x : List Bool) : List Bool := (discardPrefix x).drop (extractPrefix x).length
end MetricKMedianRecovery.BitMachine.UnaryTake

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_UnaryParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.UnaryParser
open UnaryTake

def step (x : List Bool) : List Bool :=
  if (data x).head?.getD false then pack true (true::counter x) (data x).tail []
  else pack false (counter x) (data x).tail []
def next := While.next step
def loop (x : List Bool) : List Bool := next^[x.length] x
noncomputable def run (x : List Bool) : List Bool :=
  let y:=loop (pack true [] x [])
  pairBits (counter y,data y)
end MetricKMedianRecovery.BitMachine.UnaryParser

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream
abbrev codes (rs : List ℚ) : List Bool := WordList.encode (rs.map BinaryRational.encode)
def pack (rs acc : List ℚ) : List Bool := pairBits (raw rs,codes acc)
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FinImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryTaggedSets
open WordList BinaryArithmetic
variable {n : ℕ}
noncomputable def plus (x : List Bool) : List Bool := (value (extractPrefix x)+value (discardPrefix x)).bits
noncomputable def minus (x : List Bool) : List Bool := (value (discardPrefix x)-value (extractPrefix x)).bits
end MetricKMedianRecovery.BitMachine.BinaryTaggedSets

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_PopulationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPopulation
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
attribute [local irreducible] WordList.mapWith
def near (x : List Bool) : Bool := decide (BinaryRational.decode (discardPrefix x)≤BinaryRational.decode (extractPrefix x))
end MetricKMedianRecovery.BitMachine.BinaryPopulation

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalMenus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
def leafValues (δ : Fin n→Fin n→ℚ) (s : State n) (w : Fin n) : List ℚ :=
  s.leaves.map (fun z=>δ w z.1+z.2)
def nearestLeaf (δ : Fin n→Fin n→ℚ) (s : State n) (w : Fin n) : Option ℚ :=
  if s.leaves=[] then none else some (RationalMin.minimum (leafValues δ s w))
section Metric
variable [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
include hδ
def menuRadius (D : Finset (Fin n)) (P κ : ℚ) (m M E J : ℕ) (s : State n) (w : Fin n) :
    Sampling.Entry M E J → Option ℚ
  | .inl j=>some ((j.val+1)*κ*BinaryPopulation.radiusQ P m (BinaryPopulation.distanceList δ D w))
  | .inr (.inl e)=>(nearestLeaf δ s w).map (fun r=>r/(1+κ)^e.val)
  | .inr (.inr j)=>some ((j.val+1)*κ*BinaryPopulation.radiusQ P m (BinaryPopulation.distanceList δ D w))
end Metric
end MetricKMedianRecovery.RationalSampling

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
noncomputable def clientWeight (δ : Fin n→Fin n→ℚ) (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) : ℚ :=
  max 0 (reference δ S Δ s w)
noncomputable def totalWeight (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : State n) : ℚ :=
  ∑ w∈D,clientWeight δ S Δ s w
noncomputable def transitionWeight (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (M E J : ℕ)
    (s : Option (State n)) (a : Sampling.Action D M E J) : ℚ :=
  match s with
  | none=>if a=Sum.inl () then 1 else 0
  | some s=>if 0<totalWeight δ D S Δ s then
      match a with
      | .inl _=>0
      | .inr (.inl w)=>clientWeight δ S Δ s w/(2*totalWeight δ D S Δ s)
      | .inr (.inr (w,e))=>clientWeight δ S Δ s w/(2*totalWeight δ D S Δ s)*menuWeight M E J e
    else if a=Sum.inl () then 1 else 0
def State.remove (s : State n) (v : Fin n) : State n := ⟨insert v s.deleted,s.leaves⟩
def State.add (s : State n) (w : Fin n) (R : ℚ) : State n := ⟨s.deleted,s.leaves++[(w,R)]⟩
def retain (m : ℕ) (s : State n) : Option (State n) :=
  if s.leaves.length ≤ m ∧ s.deleted.card ≤ m then some s else none
noncomputable def update (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ)
    (m M E J : ℕ) (s : Option (State n)) (a : Sampling.Action D M E J) : Option (State n) :=
  match s with
  | none=>none
  | some s=>if 0<totalWeight δ D S Δ s then
      match a with
      | .inl _=>none
      | .inr (.inl w)=>if h : chosenId δ S Δ s w<n then retain m (s.remove ⟨chosenId δ S Δ s w,h⟩) else none
      | .inr (.inr (w,e))=>match menuRadius δ D P κ m M E J s w e with
        | none=>none
        | some R=>if (F.filter (fun v=>δ w.val v≤R)).Nonempty then retain m (s.add w R) else none
    else none
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_ColorLabelMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalPower
open WordList
noncomputable def items (x : List Bool) : List Bool := repeatWords (pairBits (extractPrefix x,[]))
end MetricKMedianRecovery.BitMachine.BinaryRationalPower

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MenuMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMenu
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
noncomputable def kind (x : List Bool) : ℕ := value (extractPrefix (discardPrefix x))
noncomputable def exponent (x : List Bool) : List Bool := discardPrefix (discardPrefix x)
noncomputable def relative (x : List Bool) : Bool := decide (kind x=1)
noncomputable def first (x : List Bool) : Bool := decide (kind x=0)
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryMenu

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_NearestLeafMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNearestLeaf
open WordList BinaryArithmetic
variable {n : ℕ}
noncomputable def distance (x : List Bool) : ℚ :=
  BinaryRational.decode (Lookup.run (pairBits (extractPrefix (discardPrefix x),extractPrefix x)))+
    BinaryRational.decode (discardPrefix (discardPrefix x))
noncomputable def empty (x : List Bool) : Bool := decide (discardPrefix x=[])
end MetricKMedianRecovery.BitMachine.BinaryNearestLeaf

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
open WordList BinaryArithmetic RationalSampling
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def add (x : List Bool) : List Bool :=
  pairBits (extractPrefix (extractPrefix x),discardPrefix (extractPrefix x)++WordList.encode [discardPrefix x])
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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def c (i : ℕ) (x : List Bool) : List Bool := field i (extractPrefix x)
noncomputable def deleted (x : List Bool) : List Bool := extractPrefix (discardPrefix x)
noncomputable def leaves (x : List Bool) : List Bool := discardPrefix (discardPrefix x)
end MetricKMedianRecovery.BitMachine.BinarySampler

namespace MetricKMedianRecovery.Dyadic.Canonical
open FiniteSampling
variable {A : Type*}
variable [Fintype A] [DecidableEq A]
noncomputable def draw (p : A→ℝ) (b : ℕ) (default : A) (as : List A) (bits : Fin b→Bool) : A :=
  select default (list p b as) (Categorical.uniformBits b bits).val
end MetricKMedianRecovery.Dyadic.Canonical

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
open WordList BinaryArithmetic
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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def stateInput (x : List Bool) : List Bool := pairBits (extractPrefix x,head (discardPrefix x))
noncomputable def actionField (i : ℕ) (x : List Bool) : List Bool := field i (discardPrefix x)
noncomputable def kind (k : ℕ) (x : List Bool) : Bool := decide (value (actionField 0 x)=k)
noncomputable def active (x : List Bool) : Bool :=
  !(decide (c 3 x=[])) && decide (0<BinaryRational.decode (c 1 x))
end MetricKMedianRecovery.BitMachine.BinarySampler.Weights

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerUpdateParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Update
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
open Weights (actionField )
variable {n : ℕ}
noncomputable def input (x : List Bool) : List Bool := Weights.stateInput (extractPrefix x)
noncomputable def clientInput (x : List Bool) : List Bool := pairBits (input x,actionField 1 x)
end MetricKMedianRecovery.BitMachine.BinarySampler.Update

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
open WordList BinaryArithmetic
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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a T L : ℕ}
def partBits (part : Fin q→Fin a) : List Bool := encode (List.ofFn (fun e=>(part e).val.bits))
def oracleBits (seed : Categorical.OracleSeed (Fin q) a T L) : List Bool :=
  encode (List.ofFn (fun e=>encode (List.ofFn (fun l=>seedBits (seed e l)))))
def scorePack (ctx : List Bool) (part : Fin q→Fin a) (r : Fin a→Fin T→Option (Fin q))
    (seed : Categorical.OracleSeed (Fin q) a T L) : List Bool :=
  encode [ctx,tableBits elemBits r,oracleBits seed,partBits part]
attribute [local irreducible] mapWith
def rationalMarginal (G : Finset (Fin q)→ℚ) (part : Fin q→Fin a)
    (r : Fin a→Fin T→Option (Fin q)) (e : Fin q) (s : Fin a→Fin T) : ℚ :=
  let S:=Categorical.draw a (Function.update r (part e) (fun _=>none)) s ∅
  G (insert e S)-G S
def rationalScore (G : Finset (Fin q)→ℚ) (part : Fin q→Fin a)
    (r : Fin a→Fin T→Option (Fin q)) (seed : Categorical.OracleSeed (Fin q) a T L) (e : Fin q) : ℚ :=
  (∑ l,rationalMarginal G part r e (seed e l)) / L
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
open WordList BinaryArithmetic
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
open WordList
open BinaryOpeningPayment (field )
variable {n p q : ℕ}
noncomputable def row (x : List Bool) : List Bool := Lookup.run
  (pairBits (discardPrefix x,field 0 (extractPrefix x)))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryMetricArrays

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricCost2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricCost
open WordList
variable {n : ℕ}
def connection (δ : Fin n→Fin n→ℚ) (S : Finset (Fin n)) (x : Fin n) : ℚ :=
  RationalMin.minimum (List.ofFn (fun j:Fin S.card=>δ x (SortedIndex.enum S j)))
def cost (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) : ℚ :=
  ∑ i:Fin D.card,connection δ S (SortedIndex.enum D i)
end MetricKMedianRecovery.BitMachine.BinaryMetricCost

namespace MetricKMedianRecovery.BitMachine.BinaryMetricBest
open WordList
open BinaryOpeningPayment (field )
variable {n : ℕ}
def best (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n))) : Finset (Fin n) :=
  OrderedMaximum.run (fun U=> -BinaryMetricCost.cost δ D U) S xs
end MetricKMedianRecovery.BitMachine.BinaryMetricBest

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
open WordList
open BinaryOpeningPayment (field )
noncomputable def metricContext (x : List Bool) : List Bool := encode [field 0 x,field 1 x]
noncomputable def sanitizeContext (x : List Bool) : List Bool := encode [field 2 x,field 3 x,field 4 x]
noncomputable def atRawInput (x : List Bool) : List Bool := encode [field 0 (extractPrefix x),field 1 (extractPrefix x),
  field 2 (extractPrefix x),discardPrefix x]
end MetricKMedianRecovery.BitMachine.BinarySanitizedBest

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
open WordList BinaryArithmetic
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
open WordList BinaryArithmetic
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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a T L : ℕ}
def outputPack (ctx : List Bool) (part : Fin q→Fin a)
    (seed : (Fin T→Categorical.OracleSeed (Fin q) a T L)×(Fin a→Fin T)) : List Bool :=
  pairBits (runPack ctx part T (List.ofFn seed.1),seedBits seed.2)
end MetricKMedianRecovery.BitMachine.BinaryCategorical

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources
open WordList BinaryArithmetic
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

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionFill
open WordList BinaryArithmetic
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
open WordList BinaryArithmetic
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
-- module Solutions.Q238_KM.KMedianRecovery_Machines_GridMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGrid
open WordList BinaryArithmetic DyadicGrid
open BinaryOpeningPayment (field )
def count (query : List Bool→List Bool) (ctx : List Bool) (s : ℚ) : ℕ :=
  value (query (pairBits (field 0 ctx,BinaryRational.encode s)))
def boundK (ctx : List Bool) : ℕ := value (field 1 ctx)
def lower (ctx : List Bool) : ℚ := BinaryRational.decode (field 2 ctx)
def upper (ctx : List Bool) : ℚ := BinaryRational.decode (field 3 ctx)
end MetricKMedianRecovery.BitMachine.BinaryGrid

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
open WordList BinaryArithmetic
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
open WordList
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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
noncomputable def replaceState (x : List Bool) : List Bool :=
  encode [src 0 x,src 1 x,src 2 x,src 3 x,src 4 x,field 0 (discardPrefix x),src 6 x,src 7 x,src 8 x,src 9 x]
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LowCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IntegralAssembly
open LocalSearch Anchoring Completion Sampling FiniteSampling

noncomputable def gamma : ℝ := min (3/100) (strictnessGap (200*countConstant (1/100))/100)

end MetricKMedianRecovery.IntegralAssembly

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
open WordList BinaryArithmetic Polynomial RadiusMenus Sampling Sampling.Comparison
open BinaryOpeningPayment (field )
noncomputable def bound : Polynomial ℕ := X+C (⌈20/(IntegralAssembly.gamma/16)⌉₊+2)*(X+2)^2
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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def input (x : List Bool) : List Bool := pairBits (field 0 x,field 1 x)
end MetricKMedianRecovery.BitMachine.BinarySampler.Draw

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open BitMachine
variable {n : ℕ}
def State.initial : State n := ⟨∅,[]⟩
end MetricKMedianRecovery.RationalSampling
namespace MetricKMedianRecovery.BitMachine.BinarySampler.Loop
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}

noncomputable def input (x : List Bool) : List Bool := pairBits (extractPrefix (extractPrefix x),discardPrefix (discardPrefix x))
noncomputable def drawInput (x : List Bool) : List Bool := encode [extractPrefix (extractPrefix x),discardPrefix (discardPrefix x),
  discardPrefix (extractPrefix x),extractPrefix (discardPrefix x)]
end MetricKMedianRecovery.BitMachine.BinarySampler.Loop

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
open WordList BinaryArithmetic
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
open WordList
open BinaryOpeningPayment (field )
noncomputable def src (j : ℕ) : List Bool→List Bool := field j ∘ extractPrefix
noncomputable def params : List Bool→List Bool := extractPrefix
noncomputable def sampleRaw : List Bool→List Bool := extractPrefix ∘ discardPrefix ∘ discardPrefix
noncomputable def completeRaw : List Bool→List Bool := discardPrefix ∘ discardPrefix ∘ discardPrefix
noncomputable def extra : List Bool→List Bool := extractPrefix ∘ discardPrefix
attribute [local irreducible] src extra completeRaw
attribute [local irreducible] mapWith
noncomputable def metricContext (x : List Bool) : List Bool := encode [src 0 x,src 2 x]
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
open WordList Sampling.Comparison BinaryArithmetic
noncomputable def raw : List Bool→List Bool := discardPrefix ∘ discardPrefix
attribute [local irreducible] raw extra
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryRepeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat
open WordList Sampling.Comparison
attribute [local irreducible] extra Fair.raw RawUnary.run BinaryMetricBest.best List.ofFn BinarySeed.raw
noncomputable def context (x : List Bool) : List Bool := pairBits (extractPrefix x,extra x)
noncomputable def atSeedInput (x : List Bool) : List Bool := pairBits (extractPrefix (extractPrefix x),
  pairBits (discardPrefix (extractPrefix x),discardPrefix x))
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat

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
open WordList
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_OrientedSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryOrientedSearch
open WordList BinaryArithmetic
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
end MetricKMedianRecovery.BitMachine.BinaryOrientedSearch

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
open WordList BinaryArithmetic RationalLeaves CanonicalLengthView
open BinaryOpeningPayment (field )
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
open WordList BinaryArithmetic RationalLeaves
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
open WordList BinaryArithmetic
noncomputable def choose (rank : List Bool→List Bool) (x : List Bool) : List Bool :=
  if value (rank (pairBits (Find.context x,Find.item x))) < value (rank (pairBits (Find.context x,Fold.accum x)))
  then Find.item x else Fold.accum x
end MetricKMedianRecovery.BitMachine.BinaryLocalBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalFuel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalAnchor
open WordList BinaryArithmetic RationalLeaves Polynomial
open BinaryOpeningPayment (field )
noncomputable def fuelPoly : Polynomial ℕ :=
  C (⌈20/(IntegralAssembly.gamma/16)⌉₊+2)*(X+2)^3
end MetricKMedianRecovery.BitMachine.BinaryLocalAnchor

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
open WordList RationalLeaves
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
open WordList
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
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_RoundingArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
namespace BinaryRound
open WordList BinaryOpeningPayment

noncomputable def ceil (x : List Bool) : List Bool :=
  (⌈BinaryRational.decode (field 0 x)/BinaryRational.decode (field 1 x)⌉₊).bits
noncomputable def positive (x : List Bool) : List Bool := (min (value (field 2 x)) (max 1 (value (ceil x)))).bits
noncomputable def rational (x : List Bool) : List Bool := BinaryRational.encode (value (positive x):ℚ)
end BinaryRound
end MetricKMedianRecovery.BitMachine

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
open WordList RationalLeaves CanonicalDelete
open BinaryOpeningPayment (field )

def contextBits (base C ci : List Bool) := encode [base,C,ci]

end MetricKMedianRecovery.BitMachine.BinaryDelete

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_StartResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitialQuery
open WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field )

def ctx (base : List Bool) (total : ℕ) : List Bool := pairBits (List.replicate total true,base)
end MetricKMedianRecovery.BitMachine.BinaryInitialQuery

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
open BinaryArithmetic

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
open WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field )
variable {m d : ℕ}
noncomputable def size (x : List Bool) : List Bool := field 1 x++Count.run (field 2 x)
end MetricKMedianRecovery.BitMachine.BinaryInitialAuto

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_MetricSurplus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricSurplus
open WordList
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def anchorInput (x : List Bool) : List Bool := encode [field 0 x,field 1 x,field 2 x,field 3 x,field 5 x]
noncomputable def total (x : List Bool) : List Bool := (BinaryArithmetic.value (field 5 x)+BinaryArithmetic.value (field 6 x)).bits
end MetricKMedianRecovery.BitMachine.BinaryMetricSurplus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralAll
open WordList
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def src (j : ℕ) : List Bool→ List Bool := field j ∘ extractPrefix
noncomputable def less (x : List Bool) : List Bool := (BinaryArithmetic.value (src 5 x)-BinaryArithmetic.value (discardPrefix x)).bits
noncomputable def surplusInput (x : List Bool) : List Bool :=
  encode [src 0 x,src 1 x,src 2 x,src 3 x,src 4 x,less x,discardPrefix x]
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IntegralAssembly
noncomputable def countRat : ℚ := 10+(600/(1/100:ℚ))*2^(Anchoring.rounds (1/100)-1)
noncomputable def gapRat : ℚ := (1/(200*(200*countRat+2)))^2/100
noncomputable def gammaRat : ℚ := min (3/100) (gapRat/100)
end MetricKMedianRecovery.IntegralAssembly

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
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
def ctx : List Bool→List Bool := extractPrefix ∘ extractPrefix
def rowIndex : List Bool→List Bool := discardPrefix ∘ extractPrefix
def colIndex : List Bool→List Bool := discardPrefix
end MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NormalizeInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNormalizeInput
open WordList
open BinaryOpeningPayment (field )
noncomputable def raw (x : List Bool) : List Bool := extractPrefix x
end MetricKMedianRecovery.BitMachine.BinaryNormalizeInput

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalCall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalCall
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
noncomputable def normInput (x : List Bool) : List Bool := pairBits (field 0 x,field 1 x)
noncomputable abbrev matrix (I : RationalMetricInput) (M : ℚ) :=
  BinaryRoundingMatrix.round (BinaryDuplicateMatrix.duplicate I.distance)
    ((IntegralAssembly.gammaRat/16)*M/I.clients.card) (Rounding.cap I.clients.card (IntegralAssembly.gamma/16))
end MetricKMedianRecovery.BitMachine.BinaryGlobalCall

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalOuter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open WordList
open BinaryOpeningPayment (field )
noncomputable def callInput (x : List Bool) : List Bool :=
  encode [extractPrefix (extractPrefix x),discardPrefix x,discardPrefix (extractPrefix x)]
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open WordList LocalSearch Completion
open BinaryOpeningPayment (field )
noncomputable def start (I : RationalMetricInput) : Finset (Fin I.pointCount) := Canonical.pad I.facilities ∅ 1
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end


