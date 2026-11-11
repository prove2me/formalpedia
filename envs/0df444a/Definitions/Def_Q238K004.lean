-- Prove2me | Definitions.Def_Q238K004
-- name    : Q238K004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:10:48.339219+00:00
-- url     : https://prove2.me/theorems/384722f0-d3e9-460e-a1a1-cbc74f01515e
-- title:
--   Definitions bundle Q238K004 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 194 declarations of OpenAI's Lean: 164 definitions, 9 inductive types or structures, 1 instance and 20 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingReference.values`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.mu`, `OAI.MetricKMedianRecovery.BitMachine.WordList.Find.optionEncode`, `OAI.MetricKMedianRecovery.BitMachine.WordList.FirstPresent.marker`, `OAI.MetricKMedianRecovery.BitMachine.WordList.Subsets.update`, `OAI.MetricKMedianRecovery.CanonicalLengthSearch.chosen`, `OAI.MetricKMedianRecovery.CanonicalLengthSearch.count`, `OAI.MetricKMedianRecovery.CanonicalLengthSearch.heightBudget`, `OAI.MetricKMedianRecovery.CanonicalLengthSearch.range`, `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.finalCount`, `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.finalNode`, `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.firstPresent`, `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.forward`, `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.paid`, `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.slots`, `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.walk`, `OAI.MetricKMedianRecovery.CanonicalMergePath.advancePrefix`, `OAI.MetricKMedianRecovery.CanonicalMergePath.deleteSuffix`, `OAI.MetricKMedianRecovery.CanonicalMergePath.matchPrefix`, `OAI.MetricKMedianRecovery.CanonicalMergePath.pruneSuffix`, `OAI.MetricKMedianRecovery.CanonicalMergePath.regularPath`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.adjacent`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.cuts`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.growSuffix`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.removeVertices`, `OAI.MetricKMedianRecovery.CanonicalSlices.Acc`, `OAI.MetricKMedianRecovery.CanonicalSlices.addFront`, `OAI.MetricKMedianRecovery.CanonicalSlices.step`, `OAI.MetricKMedianRecovery.CanonicalSort.insert`, `OAI.MetricKMedianRecovery.Categorical.Batch`, `OAI.MetricKMedianRecovery.Categorical.HasRoom`, `OAI.MetricKMedianRecovery.Categorical.IsWeight`, `OAI.MetricKMedianRecovery.Categorical.PartitionFeasible`, `OAI.MetricKMedianRecovery.Categorical.SameWeights`, `OAI.MetricKMedianRecovery.Categorical.addMass`, `OAI.MetricKMedianRecovery.Categorical.choices`, `OAI.MetricKMedianRecovery.Categorical.update`, `OAI.MetricKMedianRecovery.ColorLabel.distinctMass`, `OAI.MetricKMedianRecovery.Completion.Destination`, `OAI.MetricKMedianRecovery.Completion.Destination.isBlue` and 133 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_Blue`, `KMedianRecovery_Encoding_CutMatrix`, `KMedianRecovery_Encoding_ExchangeIndex`, `KMedianRecovery_Encoding_LabelRange`, `KMedianRecovery_Encoding_Matrix`, `KMedianRecovery_Encoding_OptionEncode`, `KMedianRecovery_Encoding_RationalInflatedShape`, `KMedianRecovery_Encoding_WordSubsets`, `KMedianRecovery_Geometry_LocalSets`, `KMedianRecovery_Geometry_RealCost`, `KMedianRecovery_Machines_SliceFold`, `KMedianRecovery_Recovery_Average`, `KMedianRecovery_Recovery_Ball`, `KMedianRecovery_Recovery_BallSet`, `KMedianRecovery_Recovery_BestFallback`, `KMedianRecovery_Recovery_BoundRow`, `KMedianRecovery_Recovery_BoundedMinimizingExtreme`, `KMedianRecovery_Recovery_Cap`, `KMedianRecovery_Recovery_CenterUpdate`, `KMedianRecovery_Recovery_Cluster`, `KMedianRecovery_Recovery_CommonL`, `KMedianRecovery_Recovery_CoordinateRow`, `KMedianRecovery_Recovery_CountedTrace`, `KMedianRecovery_Recovery_DataHeight`, `KMedianRecovery_Recovery_Destination`, `KMedianRecovery_Recovery_DestinationFacility`, `KMedianRecovery_Recovery_DisjointPool`, `KMedianRecovery_Recovery_DyadicGrid`, `KMedianRecovery_Recovery_Entry`, `KMedianRecovery_Recovery_EnumeratedBest`, `KMedianRecovery_Recovery_Failure`, `KMedianRecovery_Recovery_FiniteContinuation`, `KMedianRecovery_Recovery_FirstPresent`, `KMedianRecovery_Recovery_GetRow2`, `KMedianRecovery_Recovery_GreedyOutputExpected`, `KMedianRecovery_Recovery_Grid`, `KMedianRecovery_Recovery_GridFloor`, `KMedianRecovery_Recovery_Height`, `KMedianRecovery_Recovery_ImageClass`, `KMedianRecovery_Recovery_IterationBlocks`, `KMedianRecovery_Recovery_LengthHeight`, `KMedianRecovery_Recovery_LengthSearch`, `KMedianRecovery_Recovery_Live`, `KMedianRecovery_Recovery_MergeCross`, `KMedianRecovery_Recovery_MergePath`, `KMedianRecovery_Recovery_MergeRefine`, `KMedianRecovery_Recovery_NatConnection`, `KMedianRecovery_Recovery_NearMass`, `KMedianRecovery_Recovery_Order`, `KMedianRecovery_Recovery_Pool`, `KMedianRecovery_Recovery_Produce`, `KMedianRecovery_Recovery_RealVector`, `KMedianRecovery_Recovery_RefineMath`, `KMedianRecovery_Recovery_Region`, `KMedianRecovery_Recovery_RegularChain`, `KMedianRecovery_Recovery_SetFunction`, `KMedianRecovery_Recovery_SmallSubsets`, `KMedianRecovery_Recovery_SortMath`, `KMedianRecovery_Recovery_SqNorm`, `KMedianRecovery_Recovery_StoredForms`, `KMedianRecovery_Recovery_VectorHeight`, `KMedianRecovery_Recovery_Virtual`, `KMedianRecovery_Recovery_VirtualCast`, `KMedianRecovery_Sampling_Kernel`, `KMedianRecovery_Sampling_SamplerContext`, `KMedianRecovery_Sampling_SamplerDraw`, `KMedianRecovery_Sampling_SamplingRate`, `KMedianRecovery_Sampling_SamplingReference`, `KMedianRecovery_Strictness_ClientCharge`, `KMedianRecovery_Strictness_NormalizedDual`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `Q238K014`, `Q238K015` and `Q238K016`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.realize_le_surrogate_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.cutShape_pos_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.inflatedShape_inverse_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.inflatedShape_lower_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.robust_cut_det_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.robust_spectral_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.shape_center_contains_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.stepShape_pos_bounds_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.stepShape_pos_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.upperRound_inverse_bounds_s238` and `OAI.MetricKMedianRecovery.PolytopeCertificate.approximate_implies_feasible_s238`; the proofs of `OAI.MetricKMedianRecovery.Ellipsoid.cutShape_pos_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.inflatedShape_inverse_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.inflatedShape_lower_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.robust_cut_det_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.robust_spectral_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.shape_center_contains_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.stepShape_pos_bounds_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.stepShape_pos_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.upperRound_inverse_bounds_s238` and `OAI.MetricKMedianRecovery.PolytopeCertificate.approximate_implies_feasible_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.ColorLabel

noncomputable def distinctMass (b : ℕ) (μ : Fin b → ℝ) : ℝ := by
  classical
  exact ∑ f : Fin b → Fin b, if Function.Injective f then ∏ i, μ (f i) else 0

end MetricKMedianRecovery.ColorLabel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Virtual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion

variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

inductive Virtual (V : Type*) (a : ℕ)
  | real : V → Virtual V a
  | ball : Fin a → Virtual V a
  | permanent : Virtual V a
  deriving DecidableEq

noncomputable def virtualDistance {a : ℕ} (w : Fin a → V) (radius : Fin a → ℝ)
    (M : ℝ) (x : V) : Virtual V a → ℝ
  | .real s => dist x s
  | .ball i => dist x (w i) + radius i
  | .permanent => M

noncomputable def withGhosts {a : ℕ} (S : Finset V) : Finset (Virtual V a) :=
  S.image Virtual.real ∪ Finset.univ.image Virtual.ball ∪ {Virtual.permanent}

omit [PseudoMetricSpace V] in
lemma withGhosts_nonempty {a : ℕ} (S : Finset V) : (@withGhosts V _ a S).Nonempty := by
  exact ⟨Virtual.permanent,by simp [withGhosts]⟩

omit [PseudoMetricSpace V] in
@[simp] lemma real_mem_withGhosts {a : ℕ} {S : Finset V} {s : V} :
    Virtual.real s ∈ @withGhosts V _ a S ↔ s ∈ S := by simp [withGhosts]

omit [PseudoMetricSpace V] in
@[simp] lemma ball_mem_withGhosts {a : ℕ} (S : Finset V) (i : Fin a) :
    Virtual.ball i ∈ withGhosts S := by simp [withGhosts]

omit [PseudoMetricSpace V] in
@[simp] lemma permanent_mem_withGhosts {a : ℕ} (S : Finset V) :
    (Virtual.permanent : Virtual V a) ∈ withGhosts S := by simp [withGhosts]

noncomputable def virtualNearest {a : ℕ} (S : Finset V) (w : Fin a → V)
    (radius : Fin a → ℝ) (M : ℝ) (x : V) : ℝ :=
  (withGhosts S).inf' (withGhosts_nonempty S) (virtualDistance w radius M x)

noncomputable def distanceTo (S : Finset V) (hS : S.Nonempty) (x : V) : ℝ :=
  S.inf' hS (dist x)

noncomputable def assignmentWeight {a : ℕ} (D : Finset V)
    (assignment : V → Virtual V a) (s : V) : ℝ :=
  ((D.filter (fun p => assignment p = Virtual.real s)).card : ℝ)

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Destination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion

variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

inductive Destination (V : Type*) (a : ℕ)
  | proxy : V → Destination V a
  | covered : Fin a → Destination V a
  | uncovered : V → Destination V a
  deriving DecidableEq

noncomputable def mixedDistance {a : ℕ} (theta : ℝ)
    (center w : Fin a → V) (radius : Fin a → ℝ) (s : V) : Destination V a → ℝ
  | .proxy φ => dist s φ
  | .covered i => theta * (dist s (w i) + radius i) + (1-theta)*dist s (center i)
  | .uncovered o => dist s o

omit [PseudoMetricSpace V] in
noncomputable def assignedClients {a : ℕ} (D T : Finset V) (assignment : V → Virtual V a) :
    Finset V := D.filter (fun p => ∃ s ∈ T, assignment p = Virtual.real s)

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_Blue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion
namespace Destination
variable {V : Type*} {a : ℕ}
def isBlue : Destination V a → Bool
  | .uncovered _ => true
  | _ => false
end Destination

variable {V : Type*} [DecidableEq V] {a : ℕ}

def designatedRed (R : Finset V) (dest : V → Destination V a) : Finset V :=
  R.filter (fun s => (dest s).isBlue = false)
def designatedBlue (R : Finset V) (dest : V → Destination V a) : Finset V :=
  R.filter (fun s => (dest s).isBlue = true)
def designatedProxies (R : Finset V) (dest : V → Destination V a) : Finset V :=
  R.biUnion (fun s => match dest s with | .proxy v => {v} | _ => ∅)

def requiredColors (R : Finset V) (dest : V → Destination V a) (s : V) : Fin 3 :=
  if s ∈ R then if (dest s).isBlue then 2 else 1 else 0

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_CutMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def cutMatrix (d : ℝ) (M : Matrix V V ℝ) (u : V → ℝ) : Matrix V V ℝ :=
  ((d^2-1)/d^2) • M + (2*(d+1)/d^2) • vecMulVec (M *ᵥ u) (M *ᵥ u)

def quad (M : Matrix V V ℝ) (x : V → ℝ) : ℝ := x ⬝ᵥ (M *ᵥ x)

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ImageClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch

variable {B U : Type*} [Fintype B] [Fintype U]

noncomputable def imageClass [DecidableEq U] (psi : B → U) (u : U) : Finset B :=
  Finset.univ.filter (fun b => psi b = u)

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_ExchangeIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {B U : Type*} [Fintype B] [Fintype U] [DecidableEq B] [DecidableEq U]

abbrev ExchangeIndex (B U : Type*) := U ⊕ (B × U)

noncomputable def classSlots (psi : B → U) (slot : B ↪ U) (u : U) : Finset U :=
  (imageClass psi u).map slot
noncomputable def auxiliarySlots (psi : B → U) (slot : B ↪ U) (u : U) : Finset U :=
  (classSlots psi slot u).erase u
noncomputable def exchangeWeight (psi : B → U) (slot : B ↪ U) : ExchangeIndex B U → ℝ
  | .inl u => if 0 < (imageClass psi u).card ∧ (imageClass psi u).card ≤ 5 then 1 else 0
  | .inr (b,s) => if 5 < (imageClass psi (psi b)).card ∧ s ∈ auxiliarySlots psi slot (psi b)
      then 1 / ((imageClass psi (psi b)).card - (1:ℝ)) else 0
noncomputable def exchangeRemove (psi : B → U) (slot : B ↪ U) : ExchangeIndex B U → Finset U
  | .inl u => classSlots psi slot u
  | .inr (_,s) => {s}
noncomputable def exchangeAdd (psi : B → U) : ExchangeIndex B U → Finset B
  | .inl u => imageClass psi u
  | .inr (b,_) => {b}

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Height
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalHeight
open scoped BigOperators

def Height (q : ℚ) (b : ℕ) : Prop := q.num.natAbs≤2^b ∧ q.den≤2^b

end MetricKMedianRecovery.RationalHeight

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Region
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PolytopeCertificate
open Matrix
open scoped Topology BigOperators

variable {R V : Type*} [Fintype R] [Fintype V]

def region (A : Matrix R V ℝ) (b : R → ℝ) : Set (V → ℝ) :=
  {x | ∀ r, ∑ j, A r j * x j ≤ b r}

end MetricKMedianRecovery.PolytopeCertificate

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundedMinimizingExtreme
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PolytopeCertificate

open Matrix
open scoped BigOperators
variable {R V : Type*} [Fintype R] [Fintype V] [DecidableEq V]

abbrev SlackRow (R V : Type*) := R ⊕ (Bool × Option V)

def slackMatrix (A : Matrix R V ℤ) : Matrix (SlackRow R V) (Option V) ℤ
  | .inl _r,none => -1
  | .inl r,some j => A r j
  | .inr (s,j),k => if k=j then if s then 1 else -1 else 0

def slackBounds (b : R → ℤ) (B H : ℤ) : SlackRow R V → ℤ
  | .inl r => b r
  | .inr (s,none) => if s then H else 0
  | .inr (_,some _) => B

end MetricKMedianRecovery.PolytopeCertificate

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_GridFloor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

section
open Matrix
open scoped Matrix
variable {V : Type*}

def gridFloor (D : ℕ) (q : ℚ) : ℚ := (⌊(D:ℚ)*q⌋:ℚ)/(D:ℚ)

def realMatrix (A : Matrix V V ℚ) : Matrix V V ℝ := fun i j => (A i j:ℝ)

def gridMatrix (D : ℕ) (A : Matrix V V ℚ) : Matrix V V ℚ := fun i j => gridFloor D (A i j)

end

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SqNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

section
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

def sqNorm (x : V → ℝ) : ℝ := ∑ i, (x i)^2

end

open Matrix
open scoped Matrix

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_NormalizedDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def normalizedDual (H : Matrix V V ℝ) (a : V → ℝ) : V → ℝ :=
  (1/Real.sqrt (quad H a)) • (H *ᵥ a)

noncomputable def cutShape (d : ℝ) (H : Matrix V V ℝ) (a : V → ℝ) : Matrix V V ℝ :=
  (d^2/(d^2-1)) • (H-(2/((d+1)*quad H a)) • vecMulVec (H *ᵥ a) (H *ᵥ a))

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RealVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

section
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

def realVector (x : V → ℚ) : V → ℝ := fun i => (x i:ℝ)

def rationalQuad (H : Matrix V V ℚ) (a : V → ℚ) : ℚ := a ⬝ᵥ (H *ᵥ a)

def rationalCutShape (d : ℚ) (H : Matrix V V ℚ) (a : V → ℚ) : Matrix V V ℚ :=
  (d^2/(d^2-1)) • (H-(2/((d+1)*rationalQuad H a)) • vecMulVec (H *ᵥ a) (H *ᵥ a))

end

open Matrix
open scoped Matrix

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CenterUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def centerUpdate (d : ℝ) (H : Matrix V V ℝ) (a c : V → ℝ) (t : ℝ) : V → ℝ :=
  c-(1/((d+1)*t)) • (H *ᵥ a)

def upperRound (Q : Matrix V V ℝ) (e : ℝ) : Matrix V V ℝ :=
  Q+((Fintype.card V:ℝ)*e) • (1 : Matrix V V ℝ)

def gridShape (D : ℕ) (A : Matrix V V ℚ) : Matrix V V ℚ :=
  gridMatrix D A+((Fintype.card V:ℚ)/(D:ℚ)) • (1 : Matrix V V ℚ)

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalInflatedShape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

def rationalInflatedShape (H : Matrix V V ℚ) (a : V → ℚ) : Matrix V V ℚ :=
  (1/(1-1/(8*(Fintype.card V:ℚ)^2))) • rationalCutShape (Fintype.card V) H a

def rationalStepShape (D : ℕ) (H : Matrix V V ℚ) (a : V → ℚ) : Matrix V V ℚ :=
  gridShape D (rationalInflatedShape H a)

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_IterationBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix

def iterationBlocks (n p s : ℕ) : ℕ := n*n+2*n*(p+s)+1

def iterationBudget (n p s : ℕ) : ℕ := 2*n*iterationBlocks n p s

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix PolytopeCertificate
open scoped BigOperators

abbrev BoundRow (m n : ℕ) := Fin m ⊕ (Bool × Fin n)

def boundedMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Matrix (BoundRow m n) (Fin n) ℤ
  | .inl r,j => A r j
  | .inr (s,i),j => if j=i then if s then 1 else -1 else 0

def boundedBounds {m n : ℕ} (b : Fin m → ℤ) (B : ℕ) : BoundRow m n → ℤ
  | .inl r => b r
  | .inr _ => B

def gapDenominator (m n H : ℕ) : ℕ :=
  (n+1).factorial*((m+2*n+2*(n+1))*H^2)^(n+1)

def gapEpsilon (m n H : ℕ) : ℚ := 1/(2*(gapDenominator m n H:ℚ))

def precisionLog (m n H : ℕ) : ℕ := Nat.log2 (2*gapDenominator m n H*H)+1

def radiusLog (n B : ℕ) : ℕ := Nat.log2 (n*(B+1))+1

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DataHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix PolytopeCertificate
open scoped BigOperators

def dataHeight {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) : ℕ :=
  B+1+∑ r, ((b r).natAbs+∑ j, (A r j).natAbs)

def padMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Matrix (Fin m) (Fin (n+2)) ℤ :=
  fun r => Fin.append (A r) (fun _ : Fin 2 => 0)

end MetricKMedianRecovery.Ellipsoid

namespace MetricKMedianRecovery.PolytopeCertificate
open Matrix
open scoped BigOperators
variable {J R V : Type*} [Fintype J] [DecidableEq J] [Fintype R] [Fintype V] [DecidableEq V]

def rowDenominator (q : J → ℚ) : ℤ := ∏ i, ((q i).den:ℤ)
def rowNumerator (q : J → ℚ) (i : J) : ℤ :=
  (q i).num * ∏ j ∈ Finset.univ.erase i, ((q j).den:ℤ)

end MetricKMedianRecovery.PolytopeCertificate

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoordinateRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PositiveSolve
open Matrix
open scoped BigOperators

def freezeVec {n : ℕ} (v : Fin n → ℚ) : Fin n → ℚ :=
  let a := Vector.ofFn v
  fun i => a[i]

def freezeMat {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  let a := Vector.ofFn (fun i => Vector.ofFn (M i))
  fun i j => a[i][j]

@[simp] lemma freezeVec_eq {n : ℕ} (v : Fin n → ℚ) : freezeVec v=v := by
  funext i
  simp [freezeVec]
@[simp] lemma freezeMat_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : freezeMat M=M := by
  funext i j
  simp [freezeMat]

def schur {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => M i.succ j.succ-M i.succ 0*M 0 j.succ/M 0 0

def rhs {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (b : Fin (n+1) → ℚ) : Fin n → ℚ :=
  fun i => b i.succ-M i.succ 0*b 0/M 0 0

def solve : (n : ℕ) → Matrix (Fin n) (Fin n) ℚ → (Fin n → ℚ) → (Fin n → ℚ)
  | 0,_,_ => Fin.elim0
  | n+1,M,b =>
    let S := freezeMat (schur M)
    let d := freezeVec (rhs M b)
    let x := freezeVec (solve n S d)
    freezeVec (Fin.cons ((b 0-∑ j, M 0 j.succ*x j)/M 0 0) x)

end MetricKMedianRecovery.PositiveSolve

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid.Stored
open Matrix
open scoped BigOperators

def matrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : Matrix (Fin m) (Fin n) ℚ :=
  let ar := Vector.ofFn (fun i => Vector.ofFn (A i))
  fun i j => ar[i][j]
def vector {n : ℕ} (v : Fin n → ℚ) : Fin n → ℚ :=
  let ar := Vector.ofFn v
  fun i => ar[i]
@[simp] lemma matrix_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : matrix A=A := by
  funext i j
  simp [matrix]
@[simp] lemma vector_eq {n : ℕ} (v : Fin n → ℚ) : vector v=v := by
  funext i
  simp [vector]

end MetricKMedianRecovery.Ellipsoid.Stored

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_GetRow2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
namespace RationalMatrix

def mu {n : ℕ} (F : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j=>if i<j then F i j else if i=j then -(∑ k∈Finset.Ioi i,F k k) else 0

end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_OptionEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
namespace WordList.Find

def optionEncode : Option (List Bool) → List Bool
  | none => []
  | some w => true::w

end WordList.Find
end
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix

def OnGrid (D : ℕ) (q : ℚ) : Prop := ∃ z : ℤ, q=(z:ℚ)/(D:ℚ)

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_VectorHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalHeight
open scoped Matrix BigOperators

def vectorHeight (n h a : ℕ) : ℕ := n*(h+a+1)
def quadHeight (n h a : ℕ) : ℕ := n*(a+vectorHeight n h a+1)
def rootHeight (n h a : ℕ) : ℕ := 2*quadHeight n h a+2*(5+n)+1
def incrementHeight (n h a : ℕ) : ℕ := n+1+rootHeight n h a+vectorHeight n h a

def storedShapeHeight (n T r : ℕ) : ℕ := T+2*r+(4+3*n+2*(T+1))

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordSubsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Subsets
variable {A : Type*}
def update (ss : List (List A)) (a : A) : List (List A) := ss++ss.map (fun s=>s++[a])
end MetricKMedianRecovery.BitMachine.WordList.Subsets

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CountedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

inductive CountedTrace {A : Type*} (R : A → A → Prop) : ℕ → A → A → Prop
  | nil (s : A) : CountedTrace R 0 s s
  | cons {s u e : A} {n : ℕ} (step : R s u) (tail : CountedTrace R n u e) :
      CountedTrace R (n+1) s e

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_StoredForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalPhase

structure Event (m d : ℕ) where
  facility : Fin m
  bid : Vector ℚ d

end MetricKMedianRecovery.RationalPhase

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Entry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def after (Q : Finset X) : List (List X) → Finset X
  | [] => Q
  | H::T => after (Q ∪ H.toFinset) T

end MetricKMedianRecovery.PhaseHistoryTransfer
namespace MetricKMedianRecovery.PhaseMergeCompletion
open PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Regular (F : Finset X) (T : List (List X)) : Prop := ∀ H ∈ T, ∀ i ∈ H, i ∈ F

end MetricKMedianRecovery.PhaseMergeCompletion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pool
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergePath
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def pool (F B : Finset X) (copy : X → X) : Finset X := B ∪ F.image copy

end MetricKMedianRecovery.PhaseMergePath

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergePath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergePath
open PhaseMergePath
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def deleteSuffix (complete : Finset X → List X) (Q : Finset X) (copy : X → X)
    (C : List X) (i : X) : List X → List X → List X × List (List X)
  | [],E => (E,[])
  | _u::U,E =>
    let A := complete (Q ∪ (C++U++copy i::E).toFinset)
    let r := deleteSuffix complete Q copy C i U (E++A)
    (r.1,(C++U++copy i::(E++A))::r.2)

def advancePrefix (complete : Finset X → List X) (Q : Finset X) (copy : X → X)
    (C U : List X) (i : X) : List X × List (List X) :=
  let r := deleteSuffix complete Q copy C i U []
  (r.1,(C++U++[copy i])::(r.2++[C++i::r.1]))

def matchPrefix (complete : Finset X → List X) (Q : Finset X) (copy : X → X)
    : List X → List X → List X → List X × List (List X)
  | _C,U,[] => (U,[])
  | C,U,i::T =>
    let a := advancePrefix complete Q copy C U i
    let b := matchPrefix complete Q copy (C++[i]) a.1 T
    (b.1,a.2++b.2)

def pruneSuffix (C : List X) : List X → List (List X)
  | [] => []
  | _::U => (C++U)::pruneSuffix C U

def regularPath (complete : Finset X → List X) (Q : Finset X) (copy : X → X)
    (H J : List X) : List (List X) :=
  let r := matchPrefix complete Q copy [] J H
  r.2 ++ pruneSuffix H r.1

end MetricKMedianRecovery.CanonicalMergePath

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergeRefine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeRefinement

section
open PhaseMergePath
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Coincident (loc : D → X) (F Q : Finset X) (H G : List X) : Prop :=
  ∃ i f : X, ∃ R : Finset X, i ∈ F ∧ f ∉ F ∧ i ∉ R ∧ f ∉ R ∧
    Q ∪ H.toFinset = insert i R ∧ Q ∪ G.toFinset = insert f R ∧
    ∀ j, dist (loc j) i = dist (loc j) f

inductive Edit (loc : D → X) (F B Q : Finset X) : List X → List X → Prop
  | freeAppend (H : List X) (i f : X) (hi : i ∈ F) (hf : f ∈ B)
      (hco : ∀ j, dist (loc j) i = dist (loc j) f) : Edit loc F B Q H (H++[f])
  | paidDelete (C T : List X) (i : X) (hi : i ∈ F) :
      Edit loc F B Q (C++i::T) (C++T)
  | coincident {H G : List X} (hc : Coincident loc F Q H G) : Edit loc F B Q H G

def Adjacent (loc : D → X) (F B Q : Finset X) (H G : List X) : Prop :=
  Edit loc F B Q H G ∨ Edit loc F B Q G H

end

open PhaseMergePath

end MetricKMedianRecovery.PhaseMergeRefinement

namespace MetricKMedianRecovery.CanonicalMergeRefinement
open PhaseMergePath PhaseMergeRefinement
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def cuts : List X → List (List X × X × List X)
  | [] => []
  | i::T => ([],i,T)::(cuts T).map (fun p => (i::p.1,p.2.1,p.2.2))

def growSuffix (C : List X) (f : X) : List X → List (List X)
  | [] => []
  | i::A => growSuffix C f A ++ [(C++i::A)++[f]]

def removeVertices (C T A : List X) (f : X) : List (List X) :=
  ((C++T)++[f]) :: (growSuffix (C++T) f A ++ [(C++T)++A])

end MetricKMedianRecovery.CanonicalMergeRefinement

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergeCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseCountCrossing
open PhaseMergeRefinement PhaseMergeCompletion PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Sandwich (k a b : ℕ) : Prop := (a < k ∧ k < b) ∨ (b < k ∧ k < a)

inductive LengthEdit (loc : D → X) (F B : Finset X) : List X → List X → Prop
  | freeAppend (H : List X) (i f : X) (hi : i ∈ F) (hf : f ∈ B)
      (hco : ∀ j, dist (loc j) i = dist (loc j) f) : LengthEdit loc F B H (H++[f])
  | paidDelete (C T : List X) (i : X) (hi : i ∈ F) :
      LengthEdit loc F B (C++i::T) (C++T)

end MetricKMedianRecovery.PhaseCountCrossing

namespace MetricKMedianRecovery.CanonicalMergeCrossing
open PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def paid (F Q : Finset X) (H : List X) : ℕ := ((Q ∪ H.toFinset) ∩ F).card

def finalCount (F Q : Finset X) (H : List X) (T : List (List X)) : ℕ :=
  ((after (Q ∪ H.toFinset) T) ∩ F).card

def forward (F Q : Finset X) (H G : List X) : Bool :=
  if paid F Q H = paid F Q G then decide (H.length < G.length)
  else decide (paid F Q G < paid F Q H)

instance instDecidableSandwich (k a b : ℕ) : Decidable (Sandwich k a b) := inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

end MetricKMedianRecovery.CanonicalMergeCrossing

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Live
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.HistoryPhaseBound
open PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

noncomputable def limit (v Z : ℝ) : ℕ := ⌈Real.log Z / Real.log (1+v^2)⌉₊+1

end MetricKMedianRecovery.HistoryPhaseBound

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DisjointPool
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PriceBisection

def refine (count : ℚ → ℕ) (h : ℕ) (I : ℚ × ℚ) : ℚ × ℚ :=
  let mid := (I.1+I.2)/2
  if h ≤ count mid then (mid,I.2) else (I.1,mid)

def search (count : ℚ → ℕ) (h : ℕ) : ℕ → ℚ × ℚ → ℚ × ℚ
  | 0,I => I
  | n+1,I => search count h n (refine count h I)

def iterations (a b : ℚ) (N : ℕ) : ℕ := N + Nat.clog 2 (Nat.ceil (b-a))

end MetricKMedianRecovery.PriceBisection

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FiniteContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteLabelContinuation
open PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing
variable {X : Type*} [LinearOrder X] {d : ℕ}

def alphabet (loc : Fin d → X) (F Q : Finset X) : List X :=
  (F ∪ Q ∪ Finset.univ.image loc).sort (·≤·)

lemma mem_alphabet (loc : Fin d → X) (F Q : Finset X) (x : X) :
    x∈alphabet loc F Q ↔ x∈F ∨ x∈Q ∨ ∃ j,loc j=x := by
  simp only [alphabet,Finset.mem_sort,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and]
  tauto

lemma alphabet_nodup (loc : Fin d → X) (F Q : Finset X) : (alphabet loc F Q).Nodup :=
  Finset.sort_nodup _ _

def embed (loc : Fin d → X) (F Q : Finset X) : Fin (alphabet loc F Q).length ↪ X where
  toFun := (alphabet loc F Q).get
  inj' := by
    intro i j h
    apply Fin.ext
    have hh := congrArg (fun x=>List.idxOf x (alphabet loc F Q)) h
    simpa only [List.get_idxOf (alphabet_nodup loc F Q)] using hh

def index (loc : Fin d → X) (F Q : Finset X) (x : X) (h : x∈alphabet loc F Q) :
    Fin (alphabet loc F Q).length := ⟨List.idxOf x _,List.idxOf_lt_length_iff.mpr h⟩

@[simp] lemma embed_index (loc : Fin d → X) (F Q : Finset X) (x : X) (h) :
    embed loc F Q (index loc F Q x h)=x := List.getElem_idxOf _

def located (loc : Fin d → X) (F Q : Finset X) (j : Fin d) : Fin (alphabet loc F Q).length :=
  index loc F Q (loc j) ((mem_alphabet loc F Q _).mpr (Or.inr (Or.inr ⟨j,rfl⟩)))

@[simp] lemma embed_located (loc : Fin d → X) (F Q : Finset X) (j : Fin d) :
    embed loc F Q (located loc F Q j)=loc j := embed_index ..

def select (loc : Fin d → X) (F Q S : Finset X) : Finset (Fin (alphabet loc F Q).length) :=
  Finset.univ.filter (fun i=>embed loc F Q i∈S)

@[simp] lemma mem_select (loc : Fin d → X) (F Q S : Finset X) (i) :
    i∈select loc F Q S ↔ embed loc F Q i∈S := by simp [select]

@[instance_reducible] noncomputable def metric [PseudoMetricSpace X]
    (loc : Fin d → X) (F Q : Finset X) : PseudoMetricSpace (Fin (alphabet loc F Q).length) :=
  PseudoMetricSpace.induced (embed loc F Q) inferInstance

def rows (loc : Fin d → X) (F Q : Finset X) (distance : X → Fin d → ℚ) :
    Fin (alphabet loc F Q).length → Fin d → ℚ := fun i j=>distance (embed loc F Q i) j

end MetricKMedianRecovery.FiniteLabelContinuation

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalLengthSearch
open PhaseHistoryTransfer PhaseMergeCompletion PhaseCountCrossing CanonicalMergeCrossing
variable {X : Type*} [DecidableEq X]

def chosen (complete : ℚ  →  List (List X)) (T U : List (List X)) (b s : ℚ) : List (List X) :=
  if s=0 then T else if s=b then U else complete s

def count (F Q : Finset X) (leaf : ℚ  →  X) (complete : ℚ  →  List (List X))
    (T U : List (List X)) (b s : ℚ) : ℕ :=
  ((after (insert (leaf s) Q) (chosen complete T U b s)) ∩ F).card

def range (f : ℚ  →  ℕ) (k N : ℕ) (b : ℚ) : ℚ × ℚ :=
  if f 0<k then
    let J := PriceBisection.search (fun s=>f (b-s)) k (PriceBisection.iterations 0 b N) (0,b)
    (b-J.2,b-J.1)
  else PriceBisection.search f k (PriceBisection.iterations 0 b N) (0,b)

end MetricKMedianRecovery.CanonicalLengthSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SortMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalSort
variable {α : Type*} [LinearOrder α]

def insert (a : α) (xs : List α) : List α :=
  xs.filter (·<a) ++ a::xs.filter (a<·)

end MetricKMedianRecovery.CanonicalSort

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SmallSubsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [DecidableEq V]

def smallSubsets (S : Finset V) (w : ℕ) : Finset (Finset V) :=
  (Finset.range (w+1)).biUnion (fun r => S.powersetCard r)

def exchangeCandidates (F S : Finset V) (w : ℕ) : Finset (Finset V) :=
  (((smallSubsets S w).product (smallSubsets F w)).image (fun RA => (S \ RA.1) ∪ RA.2)).filter
    (fun T => T.card = S.card)

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NatConnection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [DecidableEq V]

def natConnection (δ : V → V → ℕ) (S : Finset V) (p : V) : ℕ :=
  if h : S.Nonempty then S.inf' h (δ p) else 0

def natCost (δ : V → V → ℕ) (D S : Finset V) : ℕ := ∑ p ∈ D, natConnection δ S p

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [DecidableEq V]

def widthLists (fs : List V) : ℕ → List (Finset V)
  | 0 => [∅]
  | w+1 => widthLists fs w ++ fs.flatMap (fun i => (widthLists fs w).map (insert i))

def listBest (rank : V → ℕ) (seed : V) : List V → V
  | [] => seed
  | a::as => listBest rank (if rank a < rank seed then a else seed) as

def exchangeList (fs : List V) (S : Finset V) (w : ℕ) : List (Finset V) :=
  ((widthLists fs w).flatMap (fun R => (widthLists fs w).map (fun A => (S \ R) ∪ A))).filter
    (fun T => T.card = S.card)

def executableStep (fs : List V) (rank : Finset V → ℕ) (w : ℕ) (S : Finset V) : Finset V :=
  listBest rank S (exchangeList fs S w)

def executableDescent (fs : List V) (rank : Finset V → ℕ) (w : ℕ) : ℕ → Finset V → Finset V
  | 0, S => S
  | n+1, S => executableDescent fs rank w n (executableStep fs rank w S)

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Average
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace FiniteSampling

open scoped BigOperators

def adaptiveBad {S Ω : Type*} (f : S → Ω → S) (bad : S → Ω → Prop) :
    (n : ℕ) → S → (Fin n → Ω) → Prop
  | 0, _, _ => False
  | n+1, s, seed => bad s (seed 0) ∨ adaptiveBad f bad n (f s (seed 0)) (Fin.tail seed)

end FiniteSampling
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SetFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace Categorical

variable {E : Type*} [Fintype E] [DecidableEq E]

def IsWeight (w : E → ℝ) : Prop := (∀ e, 0 ≤ w e) ∧ ∑ e, w e ≤ 1

abbrev Batch (E : Type*) := List ((E → ℝ) × E)

noncomputable def addMass (w : E → ℝ) (e : E) (d : ℝ) : E → ℝ :=
  fun f => w f + if f = e then d else 0

noncomputable def update (d : ℝ) (b : Batch E) : Batch E :=
  b.map (fun p => (addMass p.1 p.2 d, p.2))

def HasRoom (d : ℝ) (b : Batch E) : Prop :=
  ∀ p ∈ b, IsWeight p.1 ∧ ∑ e, p.1 e + d ≤ 1

def choices : Batch E → Finset E
  | [] => ∅
  | (_, e) :: tail => insert e (choices tail)

def SameWeights (b c : Batch E) : Prop := List.Forall₂ (fun p q => p.1 = q.1) b c

end Categorical
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_GreedyOutputExpected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

section Feasible
variable {E : Type*} [Fintype E] [DecidableEq E] {a : ℕ}

def PartitionFeasible (part : E → Fin a) (S : Finset E) : Prop :=
  ∀ j, (S.filter (fun e => part e = j)).card ≤ 1

end Feasible
end MetricKMedianRecovery.Categorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_RealCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion
open Categorical FiniteSampling
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

noncomputable def realCost (D U : Finset V) : ℝ :=
  if h : U.Nonempty then ∑ p ∈ D, distanceTo U h p else 0

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SliceFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalSlices
open CanonicalMergeRefinement
variable {X : Type*}
structure Acc (X : Type*) where
  front : List X
  rest : List X
  out : List (List X × X × List X)

def addFront (C : List X) (p : List X × X × List X) := (C++p.1,p.2.1,p.2.2)
def step (s : Acc X) (a : X) : Acc X :=
  ⟨s.front++[a],s.rest.tail,s.out++[(s.front,a,s.rest.tail)]⟩
end MetricKMedianRecovery.CanonicalSlices

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Population
variable {V : Type*} [PseudoMetricSpace V]

noncomputable def ball (D : Finset V) (w : V) (q : ℝ) : Finset V :=
  D.filter (fun p => dist w p ≤ q)

lemma ball_mono (D : Finset V) (w : V) {q r : ℝ} (h : q ≤ r) :
    ball D w q ⊆ ball D w r := by
  intro p hp
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.trans h⟩

lemma ball_nonempty_at (D : Finset V) (w : V) {p : V} (hp : p ∈ D) :
    (ball D w (dist w p)).Nonempty := ⟨p, Finset.mem_filter.mpr ⟨hp, le_rfl⟩⟩

noncomputable def candidate (D : Finset V) (P : ℝ) (m : ℕ) (w p : V) : ℝ :=
  max (dist w p) (P / ((m : ℝ) * (ball D w (dist w p)).card))

end MetricKMedianRecovery.Population

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BallSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion
variable {V : Type*} [PseudoMetricSpace V] {a : ℕ}
noncomputable def ballSet (F : Finset V) (w : Fin a → V) (radius : Fin a → ℝ)
    (i : Fin a) : Finset V := by
  classical
  exact F.filter (fun x => dist (w i) x ≤ radius i)
end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BestFallback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
variable {Ω Y : Type*} [Fintype Ω] [Nonempty Ω]

noncomputable def bestWithFallback [DecidableEq Y] (cost : Y → ℝ)
    (fallback : Y) (trial : Ω → Y) (n : ℕ) (s : Fin n → Ω) : Y :=
  Classical.choose (Finset.exists_min_image (insert fallback (Finset.univ.image (fun i => trial (s i))))
    cost (Finset.insert_nonempty _ _))

end MetricKMedianRecovery.FiniteSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Produce
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

def feasibleSets (F : Finset V) (r : ℕ) : Finset (Finset V) :=
  F.powerset.filter (fun S => S.Nonempty ∧ S.card ≤ r)

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_Kernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Guided

variable {S A : Type*} [Fintype A]

structure Kernel (S A : Type*) [Fintype A] where
  weight : S → A → ℝ
  nonneg : ∀ s a, 0 ≤ weight s a
  total : ∀ s, ∑ a, weight s a = 1

noncomputable def pathWeight (f : S → A → S) (p : S → A → ℝ) :
    (n : ℕ) → S → (Fin n → A) → ℝ
  | 0, _, _ => 1
  | n+1, s, seed => p s (seed 0) * pathWeight f p n (f s (seed 0)) (Fin.tail seed)

def Hits (f : S → A → S) (stop : S → Prop) :
    (n : ℕ) → S → (Fin n → A) → Prop
  | 0, s, _ => stop s
  | n+1, s, seed => stop s ∨ Hits f stop n (f s (seed 0)) (Fin.tail seed)

noncomputable def eventMass (f : S → A → S) (p : S → A → ℝ)
    (n : ℕ) (s : S) (E : (Fin n → A) → Prop) : ℝ := by
  classical
  exact ∑ seed, if E seed then pathWeight f p n s seed else 0

end MetricKMedianRecovery.Guided

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NearMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.NearClients
variable {V : Type*}

noncomputable def nearMass [PseudoMetricSpace V] (C : Finset V)
    (o : V) (mean a : ℝ) (H : V → ℝ) : ℝ := by
  classical
  exact ∑ p ∈ C.filter (fun p => dist p o ≤ a*mean), H p

variable [PseudoMetricSpace V]

noncomputable def progressConstant (kappa : ℝ) : ℝ := kappa/(2*(171/50+61*kappa))

end MetricKMedianRecovery.NearClients

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Cluster
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable def cluster (D : Finset V) (c : V → V) (o : V) : Finset V :=
  D.filter (fun p => c p = o)

noncomputable def clusterCost (D : Finset V) (c : V → V) (o : V) : ℝ :=
  ∑ p ∈ cluster D c o, dist p o

noncomputable def comparisonCost (D : Finset V) (c : V → V) : ℝ :=
  ∑ p ∈ D, dist p (c p)

structure Comparison (D S O : Finset V) where
  assign : V → V
  assigned : ∀ p ∈ D, assign p ∈ O
  nearest : ∀ p ∈ D, ∀ o ∈ O, dist p (assign p) ≤ dist p o
  good : Finset V
  good_subset : good ⊆ O
  proxy : V → V
  proxy_mem : ∀ o ∈ good, proxy o ∈ S
  proxy_inj : Set.InjOn proxy (↑good)
  same_card : S.card = O.card
  proxy_cost : (∑ o ∈ good, ∑ p ∈ cluster D assign o, dist p (proxy o)) ≤
    (∑ o ∈ good, clusterCost D assign o) + (1/100 : ℝ)*comparisonCost D assign

end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_ClientCharge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

noncomputable def clientCharge {a : ℕ} (theta : ℝ) (center w : Fin a → V)
    (radius : Fin a → ℝ) (p : V) : Destination V a → ℝ
  | .proxy φ => dist p φ
  | .covered i => dist p (center i) + theta * (dist (w i) (center i) + radius i)
  | .uncovered i => dist p i

noncomputable def minimumMixed {a : ℕ} (theta : ℝ) (center w : Fin a → V)
    (radius : Fin a → ℝ) (Ω : Finset (Destination V a)) (hΩ : Ω.Nonempty) (s : V) : ℝ :=
  Ω.inf' hΩ (mixedDistance theta center w radius s)

noncomputable def selectedDestination {a : ℕ} (theta : ℝ) (center w : Fin a → V)
    (radius : Fin a → ℝ) (Ω : Finset (Destination V a)) (hΩ : Ω.Nonempty) (s : V) : Destination V a :=
  Classical.choose (Finset.exists_min_image Ω (mixedDistance theta center w radius s) hΩ)

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DestinationFacility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion
variable {V : Type*} [DecidableEq V] {a : ℕ}

def destinationFacility (center : Fin a → V) : Destination V a → V
  | .proxy v => v | .covered i => center i | .uncovered v => v

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_EnumeratedBest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Guided
variable {S A : Type*} [Fintype A]
open scoped Classical

noncomputable def pure (a₀ : A) : Kernel S A := by
  classical
  exact ⟨fun _ a => if a = a₀ then 1 else 0, by intros; split_ifs <;> norm_num, by intros; simp⟩

noncomputable def stoppedKernel (p : Kernel S A) (stop : S → Prop) (a₀ : A) : Kernel S A := by
  classical
  exact ⟨fun s a => if stop s then (pure a₀).weight s a else p.weight s a,
    by intro s a; split_ifs; exact (pure a₀).nonneg s a; exact p.nonneg s a,
    by
      intro state
      by_cases halted : stop state <;> simp only [halted, ite_true, if_true, ite_false, if_false]
      · exact (pure a₀).total state
      · exact p.total state⟩

noncomputable def stoppedUpdate (f : S → A → S) (stop : S → Prop) (s : S) (a : A) : S :=
  if stop s then s else f s a

noncomputable def hitMass (f : S → A → S) (p : Kernel S A) (stop : S → Prop)
    (n : ℕ) (s : S) : ℝ := eventMass f p.weight n s (Hits f stop n s)

variable {I : Type*} [Fintype I]

noncomputable def routed (q : Kernel S I) (route : S → I → A) : Kernel S A := by
  classical
  refine ⟨fun s a => ∑ i : I, if route s i = a then q.weight s i else 0, ?_, ?_⟩
  · intro s a
    exact Finset.sum_nonneg (fun i _ => by split_ifs; exact q.nonneg s i; exact le_rfl)
  · intro s
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
    exact q.total s

def states (f : S → A → S) : (n : ℕ) → S → (Fin n → A) → Fin (n+1) → S
  | 0, s, _ => fun _ => s
  | n+1, s, seed => Fin.cases s (states f n (f s (seed 0)) (Fin.tail seed))

end MetricKMedianRecovery.Guided

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Guided.FixedDyadic
open FiniteSampling
variable {S A : Type*} [Fintype A] [DecidableEq A]

def Precise (f : S → A → S) (p : Kernel S A) (b : ℕ) : ℕ → S → Prop
  | 0, _ => True
  | n+1, s => (∀ a, 0 < p.weight s a → 2 ≤ (2:ℝ)^b * p.weight s a) ∧
      ∀ a, Precise f p b n (f s a)

end MetricKMedianRecovery.Guided.FixedDyadic

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CommonL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IntegralAssembly
open LocalSearch Completion Sampling FiniteSampling

noncomputable def commonL (v : ℝ) (Nstar n M : ℕ) : ℕ :=
  max Nstar (3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(n:ℝ)*(M:ℝ))+1))

end MetricKMedianRecovery.IntegralAssembly

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Cap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IndexedCopies
open LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

@[instance_reducible]
def metric : PseudoMetricSpace (V × Bool) := PseudoMetricSpace.induced Prod.fst inferInstance

end MetricKMedianRecovery.IndexedCopies

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DyadicGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.DyadicGrid
def point (a b : ℚ) (i d : ℕ) : ℚ := a+(b-a)*(i:ℚ)/(d:ℚ)
end MetricKMedianRecovery.DyadicGrid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Failure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FailureBudget

noncomputable def failure (g : ℝ) (e N : ℕ) : ℝ :=
  g / (24*((N:ℝ)+2)^e)

end MetricKMedianRecovery.FailureBudget

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RefineMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergeRefinement
variable {X Y : Type*}
def adjacent (f : X → X → List Y) : List X → List Y
  | []=>[]
  | a::T=>match T with | []=>[] | b::_=>f a b++adjacent f T
end MetricKMedianRecovery.CanonicalMergeRefinement

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RegularChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergeCrossing
variable {A B : Type*}
def walk (step : A → A → Option B) (finish : A → B) : A → List A → B
  | a,[]=>finish a
  | a,b::T=>match step a b with | some r=>r | none=>walk step finish b T

def slots (step : A → A → Option B) : A → List A → List (Option B)
  | _,[]=>[]
  | a,b::T=>step a b :: slots step b T

def firstPresent : List (Option B) → Option B
  | []=>none
  | none::T=>firstPresent T
  | some r::_=>some r

def finalNode : A → List A → A
  | a,[]=>a
  | _,b::T=>finalNode b T

end MetricKMedianRecovery.CanonicalMergeCrossing

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
open CanonicalMergeCrossing
def marker {A : Type*} (enc : A → List Bool) (o : Option A) : List Bool := Find.optionEncode (o.map enc)
end MetricKMedianRecovery.BitMachine.WordList.FirstPresent

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalLengthSearch
open RationalHeight
variable {X : Type*} [DecidableEq X]

def heightBudget (b : ℚ) (precision h : ℕ) : ℕ :=
  4*h+2*PriceBisection.iterations 0 b precision+3

end MetricKMedianRecovery.CanonicalLengthSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Order
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IndexedCopies
@[instance_reducible]
def order (V : Type*) [LinearOrder V] : LinearOrder (V × Bool) :=
  LinearOrder.lift' (fun p : V × Bool => toLex p) (by intro a b h; exact h)
end MetricKMedianRecovery.IndexedCopies

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
open WordList
variable {n l : ℕ}
def values (Δ : ℚ) (A : Finset (Fin n)) (v : Fin l→Fin n) (r : Fin l→ℚ) (row : Fin n→ℚ) : List (ℚ ×ₗ ℕ) :=
  (A.sort (·≤·)).map (fun i=>toLex (row i,i.val))++
    toLex (Δ,n)::List.ofFn (fun j=>toLex (row (v j)+r j,n+j.val+1))
lemma values_nonempty (Δ : ℚ) (A : Finset (Fin n)) (v : Fin l→Fin n) (r : Fin l→ℚ) (row : Fin n→ℚ) :
    (values Δ A v r row).toFinset.Nonempty := by
  refine ⟨toLex (Δ,n),?_⟩
  simp only [List.mem_toFinset,values,List.mem_append,List.mem_cons,List.mem_ofFn]
  exact Or.inr (Or.inl trivial)
end MetricKMedianRecovery.BitMachine.BinarySamplingReference

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_VirtualCast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion
variable {V : Type*} {a b : ℕ}
def Virtual.cast (h : a=b) : Virtual V a→Virtual V b := h ▸ id
@[simp] lemma Virtual.cast_real (h : a=b) (v : V) : Virtual.cast h (.real v)=.real v := by subst b;rfl
@[simp] lemma Virtual.cast_ball (h : a=b) (i : Fin a) : Virtual.cast (V:=V) h (.ball i)=.ball (Fin.cast h i) := by subst b;rfl
@[simp] lemma Virtual.cast_permanent (h : a=b) : Virtual.cast h (.permanent : Virtual V a)=.permanent := by subst b;rfl
@[simp] lemma Virtual.cast_real_iff (h : a=b) (t : Virtual V a) (v : V) : Virtual.cast h t=.real v ↔ t=.real v := by subst b;rfl
end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Dyadic.Canonical

def rank : List ℕ→ℕ→Option ℕ
  | [],_=>none
  | w::ws,v=>if v<w then some 0 else (rank ws (v-w)).map Nat.succ
def findRank (ws : List ℕ) (v : ℕ) : Option ℕ :=
  (List.range ws.length).find? (fun j=>decide (v<(ws.take (j+1)).sum))
end MetricKMedianRecovery.Dyadic.Canonical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerDraw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open BitMachine RationalHeight
variable {n : ℕ}
def heightIncrement (H : ℕ) : ℕ := 10*(H+1)^2
end MetricKMedianRecovery.RationalSampling

end OAI
end


