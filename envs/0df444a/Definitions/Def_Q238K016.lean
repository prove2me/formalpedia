-- Prove2me | Definitions.Def_Q238K016
-- name    : Q238K016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:14:08.439527+00:00
-- url     : https://prove2.me/theorems/35982ece-478d-422b-8d11-dbd8eec51c8f
-- title:
--   Definitions bundle Q238K016 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 78 declarations of OpenAI's Lean: 41 definitions, 3 inductive types or structures and 34 theorems. The definitions and types are `OAI.MetricKMedianRecovery.RegularDualWitness`, `OAI.MetricKMedianRecovery.RemovalReplay`, `OAI.MetricKMedianRecovery.RemovalReplay.boundaryBid`, `OAI.MetricKMedianRecovery.Rounding.metric`, `OAI.MetricKMedianRecovery.Sampling.Comparison.IntegralBits`, `OAI.MetricKMedianRecovery.Sampling.Comparison.IsBall`, `OAI.MetricKMedianRecovery.Sampling.Comparison.IsThird`, `OAI.MetricKMedianRecovery.Sampling.Comparison.MainAction`, `OAI.MetricKMedianRecovery.Sampling.Comparison.MainEntry`, `OAI.MetricKMedianRecovery.Sampling.Comparison.actionMenuWeight`, `OAI.MetricKMedianRecovery.Sampling.Comparison.ballLeader`, `OAI.MetricKMedianRecovery.Sampling.Comparison.ballSteps`, `OAI.MetricKMedianRecovery.Sampling.Comparison.covered`, `OAI.MetricKMedianRecovery.Sampling.Comparison.coveredCenter`, `OAI.MetricKMedianRecovery.Sampling.Comparison.coveredIndex`, `OAI.MetricKMedianRecovery.Sampling.Comparison.entryIndex`, `OAI.MetricKMedianRecovery.Sampling.Comparison.instDecidableEqAction_2`, `OAI.MetricKMedianRecovery.Sampling.Comparison.leaderPair`, `OAI.MetricKMedianRecovery.Sampling.Comparison.near`, `OAI.MetricKMedianRecovery.Sampling.Comparison.ownDestination`, `OAI.MetricKMedianRecovery.Sampling.Comparison.thirdSteps`, `OAI.MetricKMedianRecovery.Sampling.State.add`, `OAI.MetricKMedianRecovery.Sampling.State.remove`, `OAI.MetricKMedianRecovery.Sampling.clusterMean`, `OAI.MetricKMedianRecovery.Sampling.leafCenter`, `OAI.MetricKMedianRecovery.Sampling.leafDistances`, `OAI.MetricKMedianRecovery.Sampling.leafRadius`, `OAI.MetricKMedianRecovery.Sampling.nearestLeaf`, `OAI.MetricKMedianRecovery.Sampling.retain`, `OAI.MetricKMedianRecovery.SortedIndex.equiv`, `OAI.MetricKMedianRecovery.SortedIndex.representative`, `OAI.MetricKMedianRecovery.Surplus.clusterCost`, `OAI.MetricKMedianRecovery.Surplus.partCharge`, `OAI.MetricKMedianRecovery.Surplus.partCost`, `OAI.MetricKMedianRecovery.ValidExecution`, `OAI.MetricKMedianRecovery.ValidExecution.Contributor`, `OAI.MetricKMedianRecovery.ValidExecution.RegularFreezesAt`, `OAI.MetricKMedianRecovery.ValidExecution.finalBudget`, `OAI.MetricKMedianRecovery.ValidExecution.precedes`, `OAI.MetricKMedianRecovery.ValidExecution.removal` and 4 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_IntegralPrecision`, `KMedianRecovery_Branching_RationalBranch`, `KMedianRecovery_Encoding_EntryIndex`, `KMedianRecovery_Encoding_SortedRepresentative`, `KMedianRecovery_Geometry_ClusterCost`, `KMedianRecovery_Geometry_LeafDistances`, `KMedianRecovery_Geometry_MetricArrays`, `KMedianRecovery_Model`, `KMedianRecovery_Recovery_Cluster`, `KMedianRecovery_Recovery_CommonL`, `KMedianRecovery_Recovery_CoveredCenter`, `KMedianRecovery_Recovery_Destinations`, `KMedianRecovery_Recovery_ExecutionState`, `KMedianRecovery_Recovery_Guide`, `KMedianRecovery_Recovery_NearEligible`, `KMedianRecovery_Recovery_Removal`, `KMedianRecovery_Recovery_RemovalReplay`, `KMedianRecovery_Recovery_SingleRadiusRatio`, `KMedianRecovery_Recovery_State2`, `KMedianRecovery_Strictness_RegularDualWitness`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K000`, `Q238K001`, `Q238K002`, `Q238K003`, `Q238K004` and `Q238K005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K022` and `Q238K023`; the statements `OAI_MetricKMedianRecovery_BitMachine_WordList_CappedFold_run_typed_s238`, `OAI.MetricKMedianRecovery.Surplus.protected_partition_cost_s238` and `OAI.MetricKMedianRecovery.valid_execution_bounded_price_strictness_s238`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.realize_le_surrogate_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.amplified_s238`, `OAI.MetricKMedianRecovery.PhaseSurplusProducer.normal_cost_s238` and `OAI.MetricKMedianRecovery.Surplus.protected_partition_cost_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K000
import Definitions.Def_Q238K001
import Definitions.Def_Q238K002
import Definitions.Def_Q238K003
import Definitions.Def_Q238K004
import Definitions.Def_Q238K005

section
-- module Solutions.Q238_KM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

def globalApplicationClaim : Prop :=
  ∃ σ : ℝ, 0 < σ ∧ ∀ a : ℝ, 0 < a → ∃ A : BinaryRandomizedAlgorithm,
    (∀ (I : RationalMetricInput) (s : A.Seed I), I.Feasible (A.output I s)) ∧
    (∀ I : RationalMetricInput,
      1 - Real.rpow ((I.size : ℝ) + 2) (-a) ≤
        A.successProbability I ((2 - σ) * (I.optimum : ℝ))) ∧
    (∀ I : RationalMetricInput, A.expectedCost I ≤ (2 - σ) * (I.optimum : ℝ))

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ExecutionState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

noncomputable def initialState (D X : Type*) : ExecutionState D X :=
  ⟨∅, 1, fun _ => 1⟩

structure ValidExecution (D X : Type*) [Fintype D] [PseudoMetricSpace X]
    [DecidableEq X] (steps : ℕ) (v lam eta : ℝ) where
  location : D → X
  regular : Finset X
  far_initially : ∀ j i, i ∈ regular → 1 ≤ dist i (location j)
  state : ℕ → ExecutionState D X
  initial : state 0 = initialState D X
  transition : ∀ n, n < steps → AtomicStep location regular v lam eta (state n) (state (n + 1))
  terminated : ∀ j, ¬activeAt location (1 - 3 * v) (state steps).phase (state steps).opened j

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_State2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling

namespace State
variable {V : Type*}
noncomputable def remove (s : State V) (v : V) : State V := by
  classical
  exact ⟨insert v s.deleted, s.leaves⟩
def add (s : State V) (w : V) (R : ℝ) : State V :=
  ⟨s.deleted, s.leaves ++ [(w,R)]⟩
end State

end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LeafDistances
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
open RadiusMenus
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable def leafDistances (s : State V) (w : V) : Finset ℝ :=
  s.leaves.toFinset.image (fun z => dist w z.1+z.2)

noncomputable def nearestLeaf (s : State V) (w : V) : Option ℝ :=
  if h : (leafDistances s w).Nonempty then some ((leafDistances s w).inf' h id) else none

lemma nearestLeaf_of_mem (s : State V) (w : V) (z : V × ℝ) (hz : z ∈ s.leaves) :
    ∃ r, nearestLeaf s w = some r ∧ r ≤ dist w z.1+z.2 := by
  classical
  have hm : dist w z.1+z.2 ∈ leafDistances s w :=
    Finset.mem_image.mpr ⟨z,List.mem_toFinset.mpr hz,rfl⟩
  have hn : (leafDistances s w).Nonempty := ⟨_,hm⟩
  refine ⟨_,?_,Finset.inf'_le id hm⟩
  simp only [nearestLeaf, dite_eq_left hn]

lemma nearestLeaf_lower (s : State V) (w : V) (r a : ℝ)
    (hr : nearestLeaf s w = some r) (ha : ∀ z ∈ s.leaves, a ≤ dist w z.1+z.2) : a ≤ r := by
  classical
  unfold nearestLeaf at hr
  split_ifs at hr with hn
  · cases Option.some.inj hr
    apply Finset.le_inf'
    intro d hd
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hd
    exact ha z (List.mem_toFinset.mp hz)

lemma menuWeight_nonneg (M E J : ℕ) (a : Entry M E J) : 0 ≤ menuWeight M E J a := by
  rcases a with i | (i | i)
  · simp only [menuWeight] <;> positivity
  · simp only [menuWeight] <;> positivity
  · simp only [menuWeight]
    apply mul_nonneg (by norm_num)
    apply div_nonneg (by positivity)
    exact Finset.sum_nonneg (fun _ _ => by positivity)

noncomputable def retain (m : ℕ) (s : State V) : Option (State V) :=
  if s.leaves.length ≤ m ∧ s.deleted.card ≤ m then some s else none

end MetricKMedianRecovery.Sampling

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

noncomputable def clusterMean (D : Finset V) (c : V → V) (o : V) : ℝ :=
  clusterCost D c o / (cluster D c o).card

namespace Comparison
variable {D S O : Finset V}
noncomputable def covered (C : Comparison D S O) (s : State V) : Finset V :=
  (s.leaves.map (fun z => C.assign z.1)).toFinset
noncomputable def near (C : Comparison D S O) (o : V) : Finset V :=
  (cluster D C.assign o).filter (fun p => dist p o ≤ (6/5 : ℝ)*clusterMean D C.assign o)

lemma covered_witness (C : Comparison D S O) (s : State V) (o : V)
    (ho : o ∈ C.covered s) : ∃ z ∈ s.leaves, C.assign z.1 = o := by
  exact List.mem_map.mp (List.mem_toFinset.mp ho)

lemma comparison_triangle (C : Comparison D S O) (w p : V) (hw : w ∈ D) (hp : p ∈ D) :
    dist w (C.assign w) ≤ dist w p + dist p (C.assign p) :=
  (C.nearest w hw (C.assign p) (C.assigned p hp)).trans (dist_triangle w p (C.assign p))

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SingleRadiusRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

noncomputable def leaderPair (C : Comparison D S O) (s : State V) (o : V) : V × ℝ :=
  if h : o ∈ C.covered s then Classical.choose (C.covered_witness s o h) else (o,0)

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoveredCenter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}
noncomputable def coveredCenter (C : Comparison D S O) (s : State V)
    (i : Fin s.leaves.length) : V := C.assign s.leaves[i.val].1
lemma exists_coveredCenter (C : Comparison D S O) (s : State V) (o : V)
    (ho : o ∈ C.covered s) : ∃ i, C.coveredCenter s i = o := by
  obtain ⟨z,hz,hzo⟩ := List.mem_map.mp (List.mem_toFinset.mp ho)
  obtain ⟨j,hj,hjz⟩ := List.mem_iff_getElem.mp hz
  refine ⟨⟨j,hj⟩,?_⟩
  simp only [coveredCenter,hjz,hzo]

noncomputable def coveredIndex (C : Comparison D S O) (s : State V) (o : V)
    (ho : o ∈ C.covered s) : Fin s.leaves.length :=
  Classical.choose (C.exists_coveredCenter s o ho)
end MetricKMedianRecovery.Sampling.Comparison
namespace MetricKMedianRecovery.Sampling
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

def leafCenter (s : State V) (i : Fin s.leaves.length) : V := s.leaves[i.val].1
def leafRadius (s : State V) (i : Fin s.leaves.length) : ℝ := s.leaves[i.val].2

end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Destinations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

noncomputable def ownDestination (C : Comparison D S O) (s : State V) (p : V) :
    Destination V s.leaves.length :=
  if C.assign p ∈ C.good then .proxy (C.proxy (C.assign p))
  else if h : C.assign p ∈ C.covered s then .covered (C.coveredIndex s (C.assign p) h)
  else .uncovered (C.assign p)

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NearEligible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}
open RadiusMenus

open scoped Classical

abbrev MainEntry (m : ℕ) := Entry (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos)
  (thirdSize mainKappa m)
abbrev MainAction (D : Finset V) (m : ℕ) :=
  Action D (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa m)

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Guide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}
open RadiusMenus
open scoped Classical

noncomputable def actionMenuWeight (m : ℕ) : MainAction D m → ℝ
  | .inr (.inr (_,e)) => menuWeight (firstSize mainKappa)
      (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa m) e
  | _ => 1

def IsBall {m : ℕ} (a : MainAction D m) : Prop := ∃ w e, a = .inr (.inr (w,e))
def IsThird {m : ℕ} (a : MainAction D m) : Prop := ∃ w j, a = .inr (.inr (w,.inr (.inr j)))

noncomputable def ballLeader (hD : D.Nonempty) {m : ℕ} : MainAction D m → D
  | .inr (.inr (w,_)) => w
  | _ => ⟨hD.choose,hD.choose_spec⟩

noncomputable def ballSteps {m n : ℕ} (seed : Fin n → MainAction D m) : Finset (Fin n) :=
  Finset.univ.filter (fun i => IsBall (seed i))

noncomputable def thirdSteps {m n : ℕ} (seed : Fin n → MainAction D m) : Finset (Fin n) :=
  Finset.univ.filter (fun i => IsThird (seed i))

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_EntryIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}
open RadiusMenus
open scoped Classical

def entryIndex {m : ℕ} : MainAction D m → ℕ
  | .inr (.inr (_,.inr (.inr j))) => j.val+1
  | _ => 0

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralPrecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open MetricKMedianRecovery RadiusMenus Guided FixedDyadic FiniteSampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable local instance instDecidableEqAction_2 (D : Finset V) (M E J : ℕ) : DecidableEq (Action D M E J) := Classical.decEq _

noncomputable abbrev IntegralBits (D : Finset V) (Δ : ℝ) (m : ℕ) :=
  Fin (2*m) → Fin (integralPrecision D Δ m) → Bool

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricArrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.SortedIndex
variable {α : Type*} [LinearOrder α]
lemma enum_mem (S : Finset α) (i : Fin S.card) : enum S i∈S := S.orderEmbOfFin_mem rfl i
lemma enum_injective (S : Finset α) : Function.Injective (enum S) := (S.orderEmbOfFin rfl).injective
lemma enum_list (S : Finset α) : List.ofFn (enum S)=S.sort (·≤·) := by
  rw [List.ofFn_eq_map]
  exact S.listMap_orderEmbOfFin_finRange rfl
end MetricKMedianRecovery.SortedIndex

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RationalBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.SortedIndex
variable {α : Type*} [LinearOrder α]
noncomputable def equiv (S : Finset α) : Fin S.card≃S :=
  Equiv.ofBijective (fun i=>⟨enum S i,enum_mem S i⟩) (by
    constructor
    · intro i j h
      exact enum_injective S (congrArg Subtype.val h)
    · rintro ⟨x,hx⟩
      have hh : x∈List.ofFn (enum S) := by rw [enum_list];simpa only [Finset.mem_sort] using hx
      obtain ⟨i,hi⟩:=List.mem_ofFn.mp hh
      exact ⟨i,Subtype.ext hi⟩)
end MetricKMedianRecovery.SortedIndex

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_SortedRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.SortedIndex
variable {V : Type*} [LinearOrder V]
noncomputable def representative (S T : Finset V) : Finset (Fin S.card) :=
  Finset.univ.filter (fun i=>enum S i∈T)
end MetricKMedianRecovery.SortedIndex

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_ClusterCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Surplus
open MetricKMedianRecovery.LocalSearch MetricKMedianRecovery.Anchoring
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

noncomputable def clusterCost (D : Finset V) (assign : V → V) (i : V) : ℝ :=
  ∑ p ∈ cluster D assign i, dist p i
noncomputable def partCost (D I : Finset V) (assign : V → V) : ℝ :=
  ∑ i ∈ I, clusterCost D assign i
noncomputable def partCharge (D I : Finset V) (assign proxy : V → V) : ℝ :=
  ∑ i ∈ I, ∑ p ∈ cluster D assign i, dist p (proxy i)

end MetricKMedianRecovery.Surplus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Removal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

namespace ValidExecution

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {steps : ℕ} {v lam eta : ℝ} (E : ValidExecution D X steps v lam eta)

lemma phase_pos (n : ℕ) (hn : n ≤ steps) : 0 < (E.state n).phase := by
  induction n with
  | zero => simp only [E.initial, initialState] <;> norm_num
  | succ n ih =>
    exact (E.transition n (by omega)).positive_phase (ih (by omega))

lemma opened_mono {a b : ℕ} (hab : a ≤ b) (hb : b ≤ steps) :
    (E.state a).opened ⊆ (E.state b).opened := by
  induction b, hab using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ b hab ih =>
    exact (ih (by omega)).trans ((E.transition b (by omega)).opened_subset)

lemma phase_mono {a b : ℕ} (hab : a ≤ b) (hb : b ≤ steps) :
    (E.state a).phase ≤ (E.state b).phase := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    exact (ih (by omega)).trans ((E.transition b (by omega)).phase_le (E.phase_pos b (by omega)).le)

lemma active_antitone {a b : ℕ} (hab : a ≤ b) (hb : b ≤ steps) (j : D)
    (hj : activeAt E.location (1 - 3 * v) (E.state b).phase (E.state b).opened j) :
    activeAt E.location (1 - 3 * v) (E.state a).phase (E.state a).opened j := by
  intro f hf
  exact lt_of_le_of_lt (E.phase_mono hab hb) (hj f (E.opened_mono hab hb hf))

lemma inactive_persists {a b : ℕ} (hab : a ≤ b) (hb : b ≤ steps) (j : D)
    (hj : ¬activeAt E.location (1 - 3 * v) (E.state a).phase (E.state a).opened j) :
    ¬activeAt E.location (1 - 3 * v) (E.state b).phase (E.state b).opened j :=
  fun h => hj (E.active_antitone hab hb j h)

lemma budget_frozen {a b : ℕ} (hab : a ≤ b) (hb : b ≤ steps) (j : D)
    (hj : ¬activeAt E.location (1 - 3 * v) (E.state a).phase (E.state a).opened j) :
    (E.state b).budget j = (E.state a).budget j := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    exact ((E.transition b (by omega)).inactive_frozen j
      (E.inactive_persists hab (by omega) j hj)).trans (ih (by omega))

lemma initial_active (j : D) :
    activeAt E.location (1 - 3 * v) (E.state 0).phase (E.state 0).opened j := by
  rw [E.initial]
  intro f hf
  simp [initialState] at hf

lemma exists_removal (j : D) : ∃ n : ℕ, n < steps ∧
    activeAt E.location (1 - 3 * v) (E.state n).phase (E.state n).opened j ∧
    ¬activeAt E.location (1 - 3 * v) (E.state (n + 1)).phase (E.state (n + 1)).opened j := by
  classical
  have hex : ∃ n : ℕ, n ≤ steps ∧
      ¬activeAt E.location (1 - 3 * v) (E.state n).phase (E.state n).opened j :=
    ⟨steps, le_rfl, E.terminated j⟩
  let b := Nat.find hex
  have hb : b ≤ steps ∧
      ¬activeAt E.location (1 - 3 * v) (E.state b).phase (E.state b).opened j := Nat.find_spec hex
  have hbpos : 0 < b := by
    by_contra h
    have heq : b = 0 := by omega
    exact hb.2 (heq ▸ E.initial_active j)
  refine ⟨b - 1, by omega, ?_, ?_⟩
  · by_contra hnot
    exact Nat.find_min hex (show b - 1 < b by omega) ⟨by omega, hnot⟩
  · simpa only [Nat.sub_add_cancel (show 1 ≤ b by omega)] using hb.2

noncomputable def removal (j : D) : Fin steps :=
  ⟨Classical.choose (E.exists_removal j), (Classical.choose_spec (E.exists_removal j)).1⟩

lemma removal_active (j : D) :
    activeAt E.location (1 - 3 * v) (E.state (E.removal j)).phase
      (E.state (E.removal j)).opened j :=
  (Classical.choose_spec (E.exists_removal j)).2.1

lemma removal_inactive (j : D) :
    ¬activeAt E.location (1 - 3 * v) (E.state ((E.removal j).val + 1)).phase
      (E.state ((E.removal j).val + 1)).opened j :=
  (Classical.choose_spec (E.exists_removal j)).2.2

lemma active_iff_before_removal (n : ℕ) (hn : n ≤ steps) (j : D) :
    activeAt E.location (1 - 3 * v) (E.state n).phase (E.state n).opened j ↔
      n ≤ (E.removal j).val := by
  constructor
  · intro ha
    by_contra h
    exact E.removal_inactive j
      (E.active_antitone (show (E.removal j).val + 1 ≤ n by omega) hn j ha)
  · intro h
    exact E.active_antitone h (Nat.le_of_lt (E.removal j).isLt) j (E.removal_active j)

lemma final_cap (j : D) :
    (E.state steps).budget j ≤ (1 + v ^ 2) * (E.state (E.removal j)).phase := by
  rw [E.budget_frozen (Nat.succ_le_of_lt (E.removal j).isLt) le_rfl j (E.removal_inactive j)]
  exact (E.transition _ (E.removal j).isLt).active_budget_cap
    (E.phase_pos _ (E.removal j).isLt.le).le j (E.removal_active j)

end ValidExecution

noncomputable def clientSlack {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t : ℝ) (s : ExecutionState D X) (j : D) : ℝ :=
  s.budget j - clippedAt loc t s.phase s.opened j

noncomputable def totalSlack {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (loc : D → X) (t : ℝ) (s : ExecutionState D X) : ℝ :=
  ∑ j, clientSlack loc t s j

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_RegularDualWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

structure RegularDualWitness {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    (loc : D → X) (F : Finset X) (v lam : ℝ) (s s' : ExecutionState D X) where
  facility : X
  witness : Finset X
  bid : D → ℝ
  contains : s.opened ⊆ witness
  admissible : admissibleBids loc (1 - 3 * v) (1 + v ^ 2) v s.phase witness facility bid
  dual : ∀ i ∈ F, ∀ a, activeAt loc (1 - 3 * v) s.phase witness a →
    openingDual loc (1 - 3 * v) s.phase witness i bid a ≤ lam
  updated : s' = regularUpdate loc (1 - 3 * v) s facility witness bid

namespace ValidExecution

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {steps : ℕ} {v lam eta : ℝ} (E : ValidExecution D X steps v lam eta)

noncomputable def finalBudget (j : D) : ℝ := (E.state steps).budget j

def Contributor (i : X) (j : D) : Prop := 2 * dist i (E.location j) < E.finalBudget j

def precedes (j k : D) : Prop :=
  (E.removal j).val < (E.removal k).val ∨
    ((E.removal j).val = (E.removal k).val ∧ E.finalBudget j < E.finalBudget k)

def RegularFreezesAt (i : X) (n : ℕ) : Prop :=
  ∃ W : RegularDualWitness E.location E.regular v lam (E.state n) (E.state (n + 1)),
    dist i W.facility ≤ (1 + 3 * v) * (E.state n).phase / 2

end ValidExecution

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RemovalReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

structure RemovalReplay (D X : Type*) [Fintype D] [PseudoMetricSpace X]
    (steps : ℕ) (t K lam : ℝ) where
  location : D → X
  regular : Finset X
  before : Fin steps → Finset X
  after : Fin steps → Finset X
  phase : Fin steps → ℝ
  removal : D → Fin steps
  budget : D → ℝ
  phase_nonneg : ∀ n, 0 ≤ phase n
  before_mono : Monotone before
  after_in_later : ∀ n m, n < m → after n ⊆ before m
  active_threshold : ∀ j f, f ∈ before (removal j) →
    phase (removal j) ≤ t * dist (location j) f
  post_removal : ∀ j, ∃ f ∈ after (removal j),
    t * dist (location j) f ≤ K * phase (removal j)
  final_cap : ∀ j, budget j ≤ K * phase (removal j)
  no_overbid : ∀ n i, i ∈ regular →
    (∑ j, max ((if removal j < n then t * nearestDistance (location j) (before n)
      else phase n) - dist i (location j)) 0) ≤ lam

namespace RemovalReplay

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X]
  {steps : ℕ} {t K lam : ℝ} (R : RemovalReplay D X steps t K lam)

noncomputable def boundaryBid (n : Fin steps) (j : D) : ℝ :=
  if R.removal j < n then t * nearestDistance (R.location j) (R.before n)
  else R.phase n

end RemovalReplay

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CommonL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Rounding
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

lemma edge_pos (u : ℝ) {C : ℕ} (hC : 0 < C) {x y : V} (hxy : x ≠ y) :
    0 < edge u C x y := by
  rw [edge,ite_eq_right hxy]
  exact lt_min hC (lt_of_lt_of_le (by omega : 0 < (1:ℕ)) (le_max_left _ _))

lemma edge_triangle (u : ℝ) (hu : 0 < u) (C : ℕ) (x y z : V) :
    edge u C x z ≤ edge u C x y+edge u C y z := by
  by_cases hxz : x = z
  · subst z; rw [edge_self]; omega
  by_cases hxy : x = y
  · subst y; simp only [edge_self,zero_add,le_refl]
  by_cases hyz : y = z
  · subst z; simp only [edge_self,add_zero,le_refl]
  have hceil : ⌈dist x z/u⌉₊ ≤ ⌈dist x y/u⌉₊+⌈dist y z/u⌉₊ := by
    calc
      _ ≤ ⌈dist x y/u+dist y z/u⌉₊ := Nat.ceil_mono (by
        rw [← add_div]; exact div_le_div_of_nonneg_right (dist_triangle x y z) hu.le)
      _ ≤ _ := Nat.ceil_add_le _ _
  simp only [edge,ite_eq_right hxz,ite_eq_right hxy,ite_eq_right hyz]
  omega

@[instance_reducible]
noncomputable def metric (u : ℝ) (hu : 0 < u) (C : ℕ) (hC : 0 < C) : MetricSpace V where
  dist x y := edge u C x y
  dist_self x := by exact_mod_cast edge_self u C x
  dist_comm x y := by exact_mod_cast edge_symm u C x y
  dist_triangle x y z := by exact_mod_cast edge_triangle u hu C x y z
  eq_of_dist_eq_zero := by
    intro x y he
    by_contra hn
    have hh := edge_pos u hC hn
    have hz : edge u C x y = 0 := by exact_mod_cast he
    omega

end MetricKMedianRecovery.Rounding

end OAI
end


