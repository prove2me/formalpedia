-- Prove2me | Definitions.Def_Q238L035
-- name    : Q238L035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:31:10.216074+00:00
-- url     : https://prove2.me/theorems/4a61a67e-d3ba-4152-86ad-e5a5dae8aaa2
-- title:
--   Definitions bundle Q238L035 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 64 declarations of OpenAI's Lean: 62 definitions and 2 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.integralPack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.P.clients`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.P.facilities`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.fallbackInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.maskCount`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.clients`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.facilities`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.step_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.denominator_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.nat_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.numerator_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.rational_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.Dsp.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMaskOutput.member`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMaskOutput.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.denominatorPower`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.radius`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.weight`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.count_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.clients`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.facilities`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.points`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.clientCount`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.clients`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.facilities`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.facilitiesInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.plainFacilities`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.points`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.twice`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.bword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.context`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.cword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.labels`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.distances`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.near`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.population`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.radii`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.row` and 22 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_GlobalCall`, `KMedianRecovery_Algorithms_GlobalOuter`, `KMedianRecovery_Algorithms_IntegralAll`, `KMedianRecovery_Branching_ObservableCapacity`, `KMedianRecovery_Encoding_MaskOutput`, `KMedianRecovery_Encoding_RationalStream`, `KMedianRecovery_Encoding_UnaryParser`, `KMedianRecovery_Geometry_MetricParser`, `KMedianRecovery_Geometry_RoundingArithmetic`, `KMedianRecovery_Machines_InitialLoop`, `KMedianRecovery_Machines_MenuMachine`, `KMedianRecovery_Machines_NormalizationMachine`, `KMedianRecovery_Machines_SensitiveMachine`, `KMedianRecovery_Recovery_NormalizeInput`, `KMedianRecovery_Recovery_PlanResult`, `KMedianRecovery_Recovery_RawSlices`, `KMedianRecovery_Recovery_RecoveryContext`, `KMedianRecovery_Sampling_SamplerContext`, `KMedianRecovery_Sampling_SamplerDraw`, `KMedianRecovery_Sampling_SamplerUpdate`, `KMedianRecovery_Sampling_SamplerUpdateParts`, `KMedianRecovery_Sampling_SamplerWeights`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L027`, `Q238L028`, `Q238L029` and `Q238L030` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L037` and `Q238L038`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.clients_bits_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.facilities_bits_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.facilities_bits_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.radii_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.ball_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.radius_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.remove_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.run_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Weights.weight_pair_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.check_pack_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.clients_bits_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.facilities_bits_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.facilities_bits_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.radii_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.ball_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.radius_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.remove_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.run_pair_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Weights.weight_pair_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.check_pack_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L027
import Definitions.Def_Q238L028
import Definitions.Def_Q238L029
import Definitions.Def_Q238L030

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RawSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.UnaryTake
open WordOperations
noncomputable def dropWords_computes : PolyComputes dropWords := by
  have hi := pack_computes true extractPrefix_computes discardPrefix_computes (const_computes [])
  have hh := (hi.comp loop_computes).comp data_computes
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Function.comp_apply,rank,pack,List.head?_cons,ite_true, if_true,counter,List.tail_cons,
    extractPrefix_pairBits]
  change dropWords x=data (next^[(extractPrefix x).length+1]
    (pack true (extractPrefix x) (discardPrefix x) []))
  rw [loop_spec,data_pack]
  rfl
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
open WordOperations UnaryTake

noncomputable def loop_computes : PolyComputes loop := by
  have h:=BoundedIteration.polynomialRun_computes next_computes Polynomial.X (7*Polynomial.X+3)
  have he (x : List Bool) : BoundedIteration.polynomialRun next Polynomial.X (7*Polynomial.X+3) x=loop x := by
    have ht:=BoundedIteration.polynomialRun_eq next Polynomial.X (7*Polynomial.X+3) x (by
      intro j _
      have hb:=(iterate_bounds x j).2
      obtain ⟨hc,hd,ho⟩:=projection_bounds x
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
      unfold mass at hb
      omega)
    simpa only [Polynomial.eval_X,loop] using ht
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  exact (he x).symm
noncomputable def run_computes : PolyComputes run :=
  ((pack_computes true (const_computes []) id_computes (const_computes [])).comp loop_computes).comp
    (counter_computes.pair data_computes)
end MetricKMedianRecovery.BitMachine.UnaryParser

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser
open WordOperations
attribute [local irreducible] UnaryParser.run UnaryTake.takeWords UnaryTake.dropWords
noncomputable def nat_computes : PolyComputes nat :=
  UnaryParser.run_computes.comp (UnaryTake.takeWords_computes.pair UnaryTake.dropWords_computes)
attribute [local irreducible] nat
noncomputable def numerator_computes : PolyComputes numerator :=
  head_computes.append ((tail_computes.comp nat_computes).comp extractPrefix_computes)
noncomputable def denominator_computes : PolyComputes denominator :=
  ((tail_computes.comp nat_computes).comp discardPrefix_computes).comp nat_computes
attribute [local irreducible] numerator denominator
noncomputable def rational_computes : PolyComputes rational :=
  (numerator_computes.pair (denominator_computes.comp extractPrefix_computes)).pair
    (denominator_computes.comp discardPrefix_computes)
end MetricKMedianRecovery.BitMachine.BinaryInputParser

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
open WordOperations
attribute [local irreducible] rational
noncomputable def step_computes : PolyComputes step := by
  have hp:=extractPrefix_computes.comp rational_computes
  have hc:=WordList.cons_computes (hp.comp extractPrefix_computes) discardPrefix_computes
  have hh:=(extractPrefix_computes.comp isEmpty_computes).cond id_computes ((hp.comp discardPrefix_computes).pair hc)
  unfold step
  simpa only [Function.comp_def,decide_eq_true_eq,id_eq] using hh
noncomputable def run_computes : PolyComputes run :=
  ((id_computes.pair (const_computes [])).comp
    (BoundedIteration.polynomialRun_computes step_computes Polynomial.X (3*Polynomial.X+1))).comp
    (discardPrefix_computes.comp WordList.reverse_computes)
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric
open WordOperations WordList
attribute [local irreducible] nat RawTake.run RawDrop.run Stream.run RawUnary.run
noncomputable def clients (x : List Bool) : List Bool := RawTake.run (pairBits (count x,masks x))
noncomputable def facilities (x : List Bool) : List Bool := RawTake.run (pairBits (count x,afterClients x))
attribute [local irreducible] header count tailHeader budget masks clients afterClients facilities rawMatrix
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric

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
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] UnaryResources.lengthBits
noncomputable def weight (x : List Bool) : ℚ :=
  if first x then 1/(3*(value (denominator 0 x):ℚ))
  else if relative x then 1/(3*((value (denominator 1 x):ℚ)+1))
  else (1/3)*(BinaryRational.decode (halfNumerator x)/(1-BinaryRational.decode (halfNormalizer x)))
noncomputable def denominatorPower (x : List Bool) : List Bool := BinaryRationalPower.run (pairBits (exponent x,
  BinaryRational.encode (1+BinaryRational.decode (field 0 (extractPrefix x)))))
noncomputable def radius (x : List Bool) : List Bool :=
  if relative x then mapWith divide (pairBits (denominatorPower x,field 2 (extractPrefix x)))
  else encode [BinaryRational.encode (uniformRadius x)]
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryMenu

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
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def undeleted (x : List Bool) : List Bool := BinaryNatSet.diff (pairBits (c 4 x,deleted x))
noncomputable def reference (x : List Bool) : List Bool := encode [c 0 x,c 5 x,undeleted x,leaves x]
noncomputable def oracle (x : List Bool) : List Bool := encode [c 1 x,c 2 x,reference x]
end MetricKMedianRecovery.BitMachine.BinarySampler

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
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def context (x : List Bool) : List Bool := encode [oracle (stateInput x),
  BinaryRational.encode (BinarySamplingOracle.total (oracle (stateInput x))),c 9 x,discardPrefix x]
noncomputable def base (x : List Bool) : ℚ :=
  BinarySamplingOracle.weight (pairBits (c 0 x,actionField 1 x))/(2*BinaryRational.decode (c 1 x))
noncomputable def weight (x : List Bool) : ℚ :=
  if active x then if kind 0 x then 0 else if kind 1 x then base x
    else base x*BinaryMenu.weight (pairBits (c 2 x,actionField 2 x))
  else if kind 0 x then 1 else 0
end MetricKMedianRecovery.BitMachine.BinarySampler.Weights

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Client
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinarySamplingOracle.row BinaryIndexMap.run
variable {n : ℕ}
noncomputable def row (x : List Bool) : List Bool := BinarySamplingOracle.row (pairBits (oracle (extractPrefix x),discardPrefix x))
noncomputable def distances (x : List Bool) : List Bool := BinaryIndexMap.run (pairBits (row x,c 2 (extractPrefix x)))
noncomputable def population (x : List Bool) : List Bool := BinaryPopulation.run (encode [c 6 (extractPrefix x),c 8 (extractPrefix x),distances x])
noncomputable def near (x : List Bool) : List Bool := BinaryNearestLeaf.run (pairBits (row x,leaves (extractPrefix x)))
noncomputable def radii (x : List Bool) : List Bool := encode [c 7 (extractPrefix x),population x,near x]
end MetricKMedianRecovery.BitMachine.BinarySampler.Client

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
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Weights (actionField )
attribute [local irreducible] BinaryMenu.radius WordList.filterWith Client.row
variable {n : ℕ}
noncomputable def chosen (x : List Bool) : List Bool := discardPrefix
  (BinarySamplingOracle.reference (pairBits (oracle (input x),actionField 1 x)))
noncomputable def radius (x : List Bool) : List Bool := BinaryMenu.radius (pairBits (Client.radii (clientInput x),actionField 2 x))
noncomputable def ball (x : List Bool) : List Bool := filterWith within (pairBits
  (pairBits (Client.row (clientInput x),head (radius x)),c 3 (input x)))
end MetricKMedianRecovery.BitMachine.BinarySampler.Update

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
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def rhs (x : List Bool) : List Bool :=
  (value (lengthBits (extractPrefix (field 5 x)))+value (field 9 x)).bits
noncomputable def check (x : List Bool) : Bool :=
  decide (BinaryBranchCheck.outside x=[] ∧ BinaryBranchCheck.badBalls x=[] ∧ BinaryBranchCheck.badRadii x=[] ∧
    value (field 9 x)≤value (lengthBits (classOf 1 x)) ∧ value (BinaryBranchCheck.lhs x)≤value (rhs x))
end MetricKMedianRecovery.BitMachine.BinaryZeroBranch

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
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def cword (x : List Bool) : List Bool := RawTake.run (pairBits (cbits x,src 6 x))
noncomputable def bword (x : List Bool) : List Bool := RawTake.run (pairBits (bbits x,src 7 x))
attribute [local irreducible] RawTake.run BinaryEllipsoidInitial.indices
attribute [local irreducible] mapWith
noncomputable def labels (x : List Bool) : List Bool := BinaryEllipsoidInitial.indices (bword x)
noncomputable def context (x : List Bool) : List Bool :=
  encode [src 0 x,src 1 x,src 2 x,src 3 x,src 4 x,src 5 x,zeros x,zeros x,labels x,qbits x,cword x,src 8 x]
attribute [local irreducible] src zeros labels qbits cword bword
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
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def actions (x : List Bool) : List Bool := BinaryActions.run (pairBits (c 2 (input x),c 9 (input x)))
noncomputable def weights (x : List Bool) : List Bool := mapWith (fun y=>BinaryRational.encode (Weights.weight y))
  (pairBits (Weights.context (input x),actions x))
end MetricKMedianRecovery.BitMachine.BinarySampler.Draw

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Update
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Weights (actionField )
attribute [local irreducible] radius
variable {n : ℕ}
noncomputable def active (x : List Bool) : Bool := Weights.active (pairBits (Weights.context (extractPrefix x),[]))
noncomputable def old (x : List Bool) : Bool := decide (value (chosen x)<value (c 0 (input x)))
noncomputable def remove (x : List Bool) : List Bool := BinarySamplingState.retain (pairBits
  (c 8 (input x),BinarySamplingState.remove (pairBits (discardPrefix (input x),chosen x))))
noncomputable def add (x : List Bool) : List Bool := BinarySamplingState.retain (pairBits
  (c 8 (input x),BinarySamplingState.add (pairBits (discardPrefix (input x),pairBits (actionField 1 x,WordList.head (radius x))))))
noncomputable def run (x : List Bool) : List Bool :=
  if active x then if Weights.kind 0 x then [] else if Weights.kind 1 x then
    if old x then remove x else []
  else if radius x=[] then [] else if ball x=[] then [] else add x
  else []

end MetricKMedianRecovery.BitMachine.BinarySampler.Update

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
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
lemma views_pack {m : ℕ} (base : List Bool) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (H : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) (J : Plan (Label (Fin m))) :
    common (pack base n q key b k N H T U J)=labels (J.common H) ∧
    small (pack base n q key b k N H T U J)=historyBits (J.small T U) ∧
    large (pack base n q key b k N H T U J)=historyBits (J.large T U) ∧
    jf 1 (pack base n q key b k N H T U J)=BinaryLabel.encode J.root := by
  cases J <;> simp [common,small,large,isFree,jf,pack,BinaryLength.planBits,
    field_encode,value,Plan.common,Plan.small,Plan.large,Plan.root,BinaryFiniteContext.labels_append]

end MetricKMedianRecovery.BitMachine.BinarySensitive

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_RoundingArithmetic
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace NatOps
noncomputable def min {f g : List Bool→List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(Min.min (value (f x)) (value (g x))).bits) := by
  have hh:=(le hf hg).cond (hf.comp normalize_computes) (hg.comp normalize_computes)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [decide_eq_true_eq,Function.comp_def,normalize_eq_bits]
  split_ifs with h
  · rw [min_eq_left h]
  · rw [min_eq_right (le_of_not_ge h)]
end NatOps
end MetricKMedianRecovery.BitMachine

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
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

lemma leafInput_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q B : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (H : List (Label (Fin m))) (T U P : List (List (Label (Fin m)))) (J : Plan (Label (Fin m)))
    (R : CanonicalLengthSearch.Result (Label (Fin m))) :
    leafInput (pack (BinarySensitive.pack (BinaryFiniteContext.pack distance loc F Q v z lam) n q key b k N H T U J) B P R)=
      match R with
      | .success s W=>BinaryCoupled.leafPack B P lam key J.root (J.common H) s s W []
      | .bracket l u A Z=>BinaryCoupled.leafPack B P lam key J.root (J.common H) l u A Z := by
  have hc:=(BinarySensitive.views_pack (BinaryFiniteContext.pack distance loc F Q v z lam) n q key b k N H T U J).1
  have hr:=(BinarySensitive.views_pack (BinaryFiniteContext.pack distance loc F Q v z lam) n q key b k N H T U J).2.2.2
  simp only [BinarySensitive.jf,Function.comp_apply] at hr
  unfold leafInput common
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Function.comp_apply]
  rw [hc]
  simp only [root,sf,Function.comp_apply,field_encode,List.getElem?_cons_zero,Option.getD_some]
  rw [hr]
  cases R <;> simp only [price,sf,rf,rightHeight,success,Function.comp_apply,BinarySensitive.pack,BinaryFiniteContext.pack,
    BinaryLengthSearch.resultBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    value_bits,decide_true,one_ne_zero,decide_false,ite_true, if_true,Bool.false_eq_true,ite_false, if_false,BinaryCoupled.leafPack]
  all_goals rfl
end MetricKMedianRecovery.BitMachine.BinaryPlanResult

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_InitialLoop
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitial
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outputBits)
attribute [local irreducible] BinaryBisection.run
def pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (F : Finset (Fin m)) (v lo M : ℚ) (N precision total k : ℕ) : List Bool :=
  encode [BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) ∅ v 0 0,
    List.replicate N true,List.replicate precision true,List.replicate total true,k.bits,
    BinaryRational.encode lo,BinaryRational.encode M]

end MetricKMedianRecovery.BitMachine.BinaryInitial

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
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
namespace Dsp
abbrev pack := @BinaryIntegralDispatch.pack
end Dsp
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_NormalizationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNormalization
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open IntegralAssembly (gammaRat)
noncomputable def count_computes : PolyComputes count := (field_computes 2).comp UnaryResources.lengthBits_computes
end MetricKMedianRecovery.BitMachine.BinaryNormalization

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
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
namespace P
noncomputable def clients : List Bool→List Bool := BinaryMaskParser.run ∘ BinaryInputParser.Metric.clients
noncomputable def facilities : List Bool→List Bool := BinaryMaskParser.run ∘ BinaryInputParser.Metric.facilities
noncomputable def points : List Bool→List Bool := RawUnary.run ∘ BinaryInputParser.Metric.clients
end P
attribute [local irreducible] P.points P.clients P.facilities
  BinaryInputParser.Metric.count BinaryInputParser.Metric.budget
  BinaryNormalization.run BinaryNormalization.cap BinaryNormalization.mesh
noncomputable def points (x : List Bool) : List Bool := P.points (raw x)
noncomputable def clients (x : List Bool) : List Bool := P.clients (raw x)
noncomputable def clientCount (x : List Bool) : List Bool := Count.run (clients x)
noncomputable def plainFacilities (x : List Bool) : List Bool := P.facilities (raw x)
noncomputable def facilitiesInput (x : List Bool) : List Bool := pairBits (count x,plainFacilities x)
noncomputable def facilities (x : List Bool) : List Bool := BinaryTaggedSets.shift (facilitiesInput x)
noncomputable def twice (x : List Bool) : List Bool := BinaryDuplicateMatrix.twice (points x)
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
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] RawTake.run UnaryResources.lengthBits
attribute [local irreducible] BinaryInputParser.Metric.count
noncomputable abbrev integralPack (I : RationalMetricInput) (M : ℚ) (raw : List Bool) :=
  A.pack (matrix I M) (I.clients.image BinaryTaggedSets.left) (I.facilities.image BinaryTaggedSets.right)
    (Rounding.cap I.clients.card (IntegralAssembly.gamma/16)) (min I.budget I.facilities.card) I.bits raw
end MetricKMedianRecovery.BitMachine.BinaryGlobalCall

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_MaskOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMaskOutput
open WordOperations WordList
variable {n : ℕ}
noncomputable def member (x : List Bool) : List Bool :=
  [BinaryNatSet.contains (pairBits (discardPrefix x,extractPrefix x))]
noncomputable def run (x : List Bool) : List Bool :=
  Flatten.run (mapWith member (pairBits (discardPrefix x,BinaryEllipsoidInitial.indices (extractPrefix x))))
end MetricKMedianRecovery.BitMachine.BinaryMaskOutput

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
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
namespace P
noncomputable abbrev clients := BinaryNormalizeInput.P.clients
noncomputable abbrev facilities := BinaryNormalizeInput.P.facilities
end P
noncomputable def fallbackInput (x : List Bool) : List Bool := encode [P.facilities x,[],(1:ℕ).bits]
attribute [local irreducible] BinaryNormalizeInput.P.clients
  BinaryNormalizeInput.P.facilities BinaryInputParser.Metric.budget
noncomputable def maskCount : List Bool→List Bool := RawUnary.run ∘ BinaryInputParser.Metric.clients ∘ extractPrefix
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end


