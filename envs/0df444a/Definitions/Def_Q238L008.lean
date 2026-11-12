-- Prove2me | Definitions.Def_Q238L008
-- name    : Q238L008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:22:04.297618+00:00
-- url     : https://prove2.me/theorems/b1a789ab-8c80-4d1e-adf7-ad469b2f310d
-- title:
--   Definitions bundle Q238L008 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 58 declarations of OpenAI's Lean: 30 definitions and 28 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.rule`, `OAI.MetricKMedianRecovery.BitMachine.BinaryClearRow.rowD`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.choices`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.digitBit`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.digitRem`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.process`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.quotient`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDivision.remainder`, `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.normalizeBig`, `OAI.MetricKMedianRecovery.BitMachine.Signed.natWords`, `OAI.MetricKMedianRecovery.BlueDP.Route`, `OAI.MetricKMedianRecovery.BlueDP.Spec`, `OAI.MetricKMedianRecovery.BlueDP.Valid`, `OAI.MetricKMedianRecovery.BlueDP.best`, `OAI.MetricKMedianRecovery.BlueDP.block`, `OAI.MetricKMedianRecovery.BlueDP.blockAt`, `OAI.MetricKMedianRecovery.BlueDP.collect`, `OAI.MetricKMedianRecovery.BlueDP.cost`, `OAI.MetricKMedianRecovery.BlueDP.destinations`, `OAI.MetricKMedianRecovery.BlueDP.item`, `OAI.MetricKMedianRecovery.BlueDP.labels`, `OAI.MetricKMedianRecovery.Categorical.Selected.orderedRule`, `OAI.MetricKMedianRecovery.LeafMetric.attachedMetric`, `OAI.MetricKMedianRecovery.RationalLeaves.level`, `OAI.MetricKMedianRecovery.RationalLeaves.metric`, `OAI.MetricKMedianRecovery.RationalLeaves.original`, `OAI.MetricKMedianRecovery.RationalLeaves.parent`, `OAI.MetricKMedianRecovery.RationalLeaves.rationalHeight`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_CompletionAlgorithm`, `KMedianRecovery_Branching_BlueChoice`, `KMedianRecovery_Branching_BlueDPValue`, `KMedianRecovery_Branching_BlueNextTable`, `KMedianRecovery_Branching_BluePlan`, `KMedianRecovery_Branching_CategoricalChoice`, `KMedianRecovery_Branching_CompletionFair`, `KMedianRecovery_Branching_CopyAge`, `KMedianRecovery_Branching_RationalBranch`, `KMedianRecovery_Encoding_DivNatWords`, `KMedianRecovery_Encoding_LabelOrder`, `KMedianRecovery_Encoding_NatWords`, `KMedianRecovery_Encoding_RationalLeaves`, `KMedianRecovery_Encoding_UniformWord`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_DigitBit`, `KMedianRecovery_Recovery_OrderedMaximum`, `KMedianRecovery_Recovery_Pack`, `KMedianRecovery_Recovery_PhasesBounded`, `KMedianRecovery_Recovery_RawUnary`.
--
--   **Imports.** It imports the bundles `Q238L000`, `Q238L001` and `Q238L002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L016`, `Q238L017`, `Q238L018`, `Q238L019` and `Q238L020`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.planned_successful_completion_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result_guarantee_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result_guarantee_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result_guarantee_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.sixtyTwoFin_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result_guarantee_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_Q238L000
import Definitions.Def_Q238L001
import Definitions.Def_Q238L002

section
-- module Solutions.Q238_KM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing
namespace BinaryDivision
open BinaryArithmetic BinarySubtraction

def quotient (x : List Bool) := extractPrefix (discardPrefix (discardPrefix x.tail))
def remainder (x : List Bool) := discardPrefix (discardPrefix (discardPrefix x.tail))

end BinaryDivision
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DigitBit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing
namespace BinaryDivision
open BinaryArithmetic BinarySubtraction

def digitBit (b : Bool) (y r : List Bool) : Bool := decide (value y ≤ value (b::r))
def digitRem (b : Bool) (y r : List Bool) : List Bool :=
  if digitBit b y r then BinaryArithmetic.normalize (subtract (b::r) y) else b::r

def process : List Bool → List Bool → List Bool → List Bool → List Bool × List Bool
  | [],_,q,r => (q,r)
  | b::ds,y,q,r => process ds y (digitBit b y r::q) (digitRem b y r)

end BinaryDivision
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_DivNatWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
namespace Signed

lemma signed_ediv_nat (s : Bool) (n d : ℕ) : signed s n/(d:ℤ)=
    if d=0 then 0 else if s then
      if n%d=0 then signed true (n/d) else signed true (n/d+1)
    else signed false (n/d) := by
  by_cases hd : d=0
  · simp only [hd,Int.natCast_zero,Int.ediv_zero,ite_true, if_true]
  · have hp : (0:ℤ)<d := by exact_mod_cast Nat.pos_of_ne_zero hd
    cases s with
    | false => simp only [ite_eq_right hd,Bool.false_eq_true,ite_false, if_false,signed,Int.natCast_ediv]
    | true =>
      simp only [ite_eq_right hd,ite_true, if_true,signed,Int.neg_ediv,Int.natCast_ediv,
        Int.natCast_dvd_natCast,Nat.dvd_iff_mod_eq_zero,Int.sign_eq_one_of_pos hp]
      split_ifs <;> omega

end Signed
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_OrderedMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.OrderedMaximum
variable {E β : Type*} [LinearOrder β]
lemma mem (score : E→β) (s : E) (as : List E) : run score s as=s ∨ run score s as∈as := by
  induction as generalizing s with
  | nil=>exact Or.inl rfl
  | cons a as ih=>
    unfold run
    rcases ih (if score s < score a then a else s) with h|h
    · by_cases hs : score s < score a
      · simp only [ite_eq_left hs] at h
        simpa only [ite_eq_left hs] using Or.inr (List.mem_cons.mpr (Or.inl h))
      · simpa only [ite_eq_right hs] using Or.inl h
    · exact Or.inr (List.mem_cons.mpr (Or.inr h))
lemma own_le (score : E→β) (s : E) (as : List E) : score s ≤ score (run score s as) := by
  induction as generalizing s with
  | nil=>exact le_rfl
  | cons a as ih=>
    unfold run
    by_cases hs : score s < score a
    · rw [ite_eq_left hs]
      exact hs.le.trans (ih a)
    · rw [ite_eq_right hs]
      exact ih s
lemma score_le (score : E→β) (s : E) (as : List E) (a : E) (ha : a∈as) : score a ≤ score (run score s as) := by
  induction as generalizing s with
  | nil=>exact False.elim (List.not_mem_nil ha)
  | cons b as ih=>
    unfold run
    rcases List.mem_cons.mp ha with rfl|ha
    · by_cases hs : score s < score a
      · rw [ite_eq_left hs]; exact own_le score a as
      · rw [ite_eq_right hs]; exact (le_of_not_gt hs).trans (own_le score s as)
    · exact ih (if score s < score b then b else s) ha
lemma ofList_mem (score : E→β) (as : List E) (h : as≠[]) : ofList score as h∈as := by
  rcases mem score (as.head h) as.tail with he|he
  · rw [ofList,he]
    exact List.head_mem h
  · exact List.mem_of_mem_tail he
lemma le_ofList (score : E→β) (as : List E) (h : as≠[]) (a : E) (ha : a∈as) :
    score a ≤ score (ofList score as h) := by
  cases as with
  | nil=>exact False.elim (h rfl)
  | cons b as=>
    rcases List.mem_cons.mp ha with rfl|ha
    · exact own_le score a as
    · exact score_le score b as a ha
end MetricKMedianRecovery.OrderedMaximum

namespace MetricKMedianRecovery.Categorical.Selected
variable {E : Type*} [DecidableEq E] {a : ℕ}
noncomputable def orderedRule (es : List E) (he : ∀ e,e∈es) (part : E→Fin a)
    (hp : Function.Surjective part) : Rule part where
  choose score j:=OrderedMaximum.ofList score (bag es part j) (bag_ne_nil es he part hp j)
  spec score j:=by
    have hm := OrderedMaximum.ofList_mem score (bag es part j) (bag_ne_nil es he part hp j)
    refine ⟨by exact of_decide_eq_true (List.mem_filter.mp hm).2,?_⟩
    intro e hpart
    exact OrderedMaximum.le_ofList score (bag es part j) (bag_ne_nil es he part hp j) e
      (List.mem_filter.mpr ⟨he e,by simpa only [decide_eq_true_eq] using hpart⟩)
end MetricKMedianRecovery.Categorical.Selected

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_NatWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
namespace Signed
noncomputable def natWords (x : List Bool) : List Bool := if sign x then [] else normalize x.tail
end Signed
end MetricKMedianRecovery.BitMachine

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
variable {q a T L : ℕ}
noncomputable def rule (part : Fin q→Fin a) (hp : Function.Surjective part) : Categorical.Selected.Rule part :=
  Categorical.Selected.orderedRule (elements q) mem_elements part hp
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PhasesBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LeafMetric
variable {V C : Type*} [PseudoMetricSpace V]

lemma leafDist_comm (root : C → V) (u : C → ℝ) (x y : V ⊕ C) :
    leafDist root u x y = leafDist root u y x := by
  by_cases h : x = y
  · subst y; rfl
  · simp only [leafDist,ite_eq_right h,ite_eq_right (Ne.symm h)]
    rw [dist_comm]
    ring
lemma leafDist_triangle (root : C → V) (u : C → ℝ) (hu : ∀ c, 0 ≤ u c) (x y z : V ⊕ C) :
    leafDist root u x z ≤ leafDist root u x y + leafDist root u y z := by
  by_cases hxz : x = z
  · subst z
    rw [leafDist_self]
    exact add_nonneg (leafDist_nonneg root u hu _ _) (leafDist_nonneg root u hu _ _)
  by_cases hxy : x = y
  · subst y
    rw [leafDist_self,zero_add]
  by_cases hyz : y = z
  · subst z
    rw [leafDist_self,add_zero]
  simp only [leafDist,ite_eq_right hxz,ite_eq_right hxy,ite_eq_right hyz]
  have h := dist_triangle (parent root x) (parent root y) (parent root z)
  have hh := height_nonneg u hu y
  linarith

@[instance_reducible]
noncomputable def attachedMetric (root : C → V) (u : C → ℝ) (hu : ∀ c, 0 ≤ u c) :
    PseudoMetricSpace (V ⊕ C) where
  dist := leafDist root u
  dist_self := leafDist_self root u
  dist_comm := leafDist_comm root u
  dist_triangle := leafDist_triangle root u hu

end MetricKMedianRecovery.LeafMetric

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

@[instance_reducible] noncomputable def metric : PseudoMetricSpace (Label V) :=
  LeafMetric.attachedMetric root height (fun c=>by
    dsimp only [height]
    exact_mod_cast (le_max_right c.2.2 0))

attribute [local instance] metric

def original : V ↪ Label V := ⟨Sum.inl,Sum.inl_injective⟩

def parent : Label V → V := Sum.elim id root

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyAge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [DecidableEq V]

def level : Label V → ℕ
  | .inl _ => 0
  | .inr c => c.1+1

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [LinearOrder V]
def rationalHeight : Label V → ℚ
  | .inl _=>0
  | .inr c=>c.2.2

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RawUnary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.RawUnary
lemma copies_singleton (n : ℕ) (b : Bool) : RepeatedAppend.copies n [b]=List.replicate n b := by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [RepeatedAppend.copies,ih,List.replicate_succ']
end MetricKMedianRecovery.BitMachine.RawUnary

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_UniformWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
open BinaryArithmetic
noncomputable def normalizeBig (x : List Bool) : List Bool := BinaryArithmetic.normalize x.reverse
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_CompletionAlgorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm
open WordList BinaryArithmetic
variable {n q a p r b T L : ℕ}
noncomputable def choices (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ)
    (part : Fin q→Fin a) (hp : Function.Surjective part)
    (seed : (Fin T→Categorical.OracleSeed (Fin q) a T L)×(Fin a→Fin T)) : List (Fin q) :=
  BinaryCategorical.drawn (Categorical.Selected.greedyRun part (BinaryCategorical.rule part hp)
    (fun S=>(BinaryCompletion.savingQ k base distance weight redBase redDistance S:ℝ)) seed.1).2 seed.2
end MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {A : Type*}
lemma choose_mem (x y : Candidate A) : choose x y=x ∨ choose x y=y := by
  cases x <;> cases y <;> simp only [choose]
  all_goals first | exact Or.inl trivial | exact Or.inr trivial | (split_ifs <;> simp)
lemma choose_property (P : Candidate A→Prop) (x y : Candidate A) (hx : P x) (hy : P y) : P (choose x y) := by
  rcases choose_mem x y with h|h
  · rw [h];exact hx
  · rw [h];exact hy

lemma fold_property (P : Candidate A→Prop) (xs : List (Candidate A)) (s : Candidate A)
    (hs : P s) (hx : ∀ x∈xs,P x) : P (xs.foldl choose s) := by
  induction xs generalizing s with
  | nil=>exact hs
  | cons x xs ih=>exact ih (choose s x) (choose_property P s x hs (hx x (by simp))) (fun x h=>hx x (by simp [h]))
lemma fold_mem (xs : List (Candidate A)) (s : Candidate A) : xs.foldl choose s=s ∨ xs.foldl choose s∈xs := by
  induction xs generalizing s with
  | nil=>simp
  | cons x xs ih=>
    rw [List.foldl_cons]
    rcases ih (choose s x) with h|h
    · rcases choose_mem s x with he|he
      · exact Or.inl (h.trans he)
      · exact Or.inr (List.mem_cons.mpr (Or.inl (h.trans he)))
    · exact Or.inr (List.mem_cons_of_mem _ h)
end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueDPValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {A L : Type*}
lemma value_merge (x y : Candidate (List A)) : value (merge x y)=value x+value y := by
  cases x with
  | none=>simp [merge,value]
  | some x=>
    cases y with
    | none=>simp [merge,value]
    | some y=>simp [merge,value,Rat.cast_add,WithTop.coe_add]
def collect (xs : List (Candidate (List A))) : Candidate (List A) := xs.foldr merge (some (0,[]))

variable [LinearOrder L]
def best (C : Finset L→Candidate (List A)) (c : ℕ) (U : Finset L) : Candidate (List A) :=
  if U=∅ then some (0,[]) else select ((List.range c).map (fun t=>recurrence C (t+1) U))
end MetricKMedianRecovery.BlueDP

namespace MetricKMedianRecovery.BlueDP
variable {L R Y : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder Y]

def item (B : Finset R) (label : R→L) (q : R→Y→ℚ) (l : L) (y : Y) : Candidate (List (Atom L R Y)) :=
  select (((B.filter (label ·=l)).sort (·≤·)).map (fun r=>some (q r y,[(l,r,y)])))
def blockAt (B : Finset R) (label : R→L) (q : R→Y→ℚ) (U : Finset L) (y : Y) : Candidate (List (Atom L R Y)) :=
  collect ((U.sort (·≤·)).map (fun l=>item B label q l y))
def block (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (U : Finset L) : Candidate (List (Atom L R Y)) :=
  select ((F.sort (·≤·)).map (blockAt B label q U))
end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueNextTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {L R Y : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder Y]
def labels (xs : List (Atom L R Y)) : List L := xs.map Prod.fst
def destinations (xs : List (Atom L R Y)) : Finset Y := (xs.map (fun a=>a.2.2)).toFinset
def cost (q : R→Y→ℚ) (xs : List (Atom L R Y)) : ℚ := (xs.map (fun a=>q a.2.1 a.2.2)).sum
def Valid (B : Finset R) (F : Finset Y) (label : R→L) (xs : List (Atom L R Y)) : Prop :=
  ∀ a∈xs,a.2.1∈B ∧ label a.2.1=a.1 ∧ a.2.2∈F
def Route (U : Finset L) (xs : List (Atom L R Y)) : Prop := (labels xs).Nodup ∧ (labels xs).toFinset=U
def Spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ)
    (U : Finset L) (c : ℕ) : Candidate (List (Atom L R Y))→Prop
  | none=>True
  | some (k,xs)=>Route U xs ∧ Valid B F label xs ∧ (destinations xs).card ≤ c ∧ k=cost q xs
lemma select_spec {A : Type*} (P : Candidate A→Prop) (xs : List (Candidate A)) (h0 : P none)
    (hxs : ∀ x∈xs,P x) : P (select xs) := fold_property P xs none h0 hxs
omit [LinearOrder R] [LinearOrder Y] in
lemma route_append (U V : Finset L) (xs ys : List (Atom L R Y)) (hx : Route U xs) (hy : Route V ys)
    (hUV : Disjoint U V) : Route (U∪V) (xs++ys) := by
  rcases hx with ⟨hxn,hx⟩
  rcases hy with ⟨hyn,hy⟩
  refine ⟨?_,?_⟩
  · rw [labels,List.map_append,List.nodup_append]
    refine ⟨hxn,hyn,?_⟩
    intro a hax b hay hab
    subst b
    exact (Finset.disjoint_left.mp hUV (hx ▸ List.mem_toFinset.mpr hax) (hy ▸ List.mem_toFinset.mpr hay))
  · simp only [labels,List.map_append,List.toFinset_append] at hx hy ⊢
    rw [hx,hy]
omit [LinearOrder L] [LinearOrder R] [LinearOrder Y] in
lemma valid_append (B : Finset R) (F : Finset Y) (label : R→L) (xs ys : List (Atom L R Y))
    (hx : Valid B F label xs) (hy : Valid B F label ys) : Valid B F label (xs++ys) := by
  intro a ha
  rcases List.mem_append.mp ha with h|h
  · exact hx a h
  · exact hy a h
omit [LinearOrder R] in
lemma merge_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ)
    (U V : Finset L) (c d : ℕ) (x y : Candidate (List (Atom L R Y)))
    (hx : Spec B F label q U c x) (hy : Spec B F label q V d y) (hUV : Disjoint U V) :
    Spec B F label q (U∪V) (c+d) (merge x y) := by
  cases x with
  | none=>trivial
  | some x=>
    cases y with
    | none=>trivial
    | some y=>
      rcases x with ⟨k,xs⟩
      rcases y with ⟨j,ys⟩
      rcases hx with ⟨hx,hxv,hxc,rfl⟩
      rcases hy with ⟨hy,hyv,hyc,rfl⟩
      refine ⟨route_append U V xs ys hx hy hUV,valid_append B F label xs ys hxv hyv,?_,?_⟩
      · simp only [destinations,List.map_append,List.toFinset_append]
        exact (Finset.card_union_le _ _).trans (Nat.add_le_add hxc hyc)
      · simp [cost,List.sum_append]
omit [LinearOrder R] in
lemma empty_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (c : ℕ) :
    Spec B F label q ∅ c (some (0,[])) := by
  simp [Spec,Route,labels,Valid,destinations,cost]
omit [LinearOrder Y] in
lemma item_witness (B : Finset R) (label : R→L) (q : R→Y→ℚ) (l : L) (y : Y)
    (k : ℚ) (xs : List (Atom L R Y)) (h : item B label q l y=some (k,xs)) :
    ∃ r∈B,label r=l ∧ k=q r y ∧ xs=[(l,r,y)] := by
  have hh:=fold_mem (((B.filter (label ·=l)).sort (·≤·)).map (fun r=>some (q r y,[(l,r,y)]))) none
  change item B label q l y=none ∨ item B label q l y∈_ at hh
  rcases hh with he|hm
  · rw [h] at he;cases he
  · rw [h] at hm
    obtain ⟨r,hr,he⟩:=List.mem_map.mp hm
    have hr':=Finset.mem_filter.mp ((Finset.mem_sort (·≤·)).mp hr)
    have he':=Option.some.inj he
    exact ⟨r,hr'.1,hr'.2,(congrArg Prod.fst he').symm,(congrArg Prod.snd he').symm⟩
lemma item_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (l : L) (y : Y) (hy : y∈F) :
    Spec B F label q {l} 1 (item B label q l y) := by
  cases he : item B label q l y with
  | none=>trivial
  | some x=>
    rcases x with ⟨k,xs⟩
    obtain ⟨r,hr,hlabel,rfl,rfl⟩:=item_witness B label q l y k xs he
    simp [Spec,Route,labels,Valid,destinations,cost,hr,hlabel,hy]
lemma collect_items_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ)
    (ls : List L) (hls : ls.Nodup) (y : Y) (hy : y∈F) :
    Spec B F label q ls.toFinset ls.length (collect (ls.map (fun l=>item B label q l y))) := by
  induction ls with
  | nil=>exact empty_spec B F label q 0
  | cons l ls ih=>
    have hls':=List.nodup_cons.mp hls
    have hh:=merge_spec B F label q {l} ls.toFinset 1 ls.length _ _ (item_spec B F label q l y hy) (ih hls'.2)
      (by simpa using hls'.1)
    simpa only [List.map_cons,collect,List.foldr_cons,List.toFinset_cons,List.length_cons,
      Finset.singleton_union,Nat.add_comm 1] using hh
omit [LinearOrder Y] in
lemma collect_dest (B : Finset R) (label : R→L) (q : R→Y→ℚ) (ls : List L) (y : Y)
    (k : ℚ) (xs : List (Atom L R Y)) (h : collect (ls.map (fun l=>item B label q l y))=some (k,xs)) :
    ∀ a∈xs,a.2.2=y := by
  induction ls generalizing k xs with
  | nil=>simp only [List.map_nil,collect,List.foldr_nil,Option.some.injEq,Prod.mk.injEq] at h;rw [←h.2];simp
  | cons l ls ih=>
    change merge (item B label q l y) (collect (ls.map (fun l=>item B label q l y)))=some (k,xs) at h
    cases hi : item B label q l y with
    | none=>simp [hi,merge] at h
    | some v=>
      rcases v with ⟨j,ys⟩
      obtain ⟨r,_,_,rfl,rfl⟩:=item_witness B label q l y j ys hi
      cases ht : collect (ls.map (fun l=>item B label q l y)) with
      | none=>simp [hi,ht,merge] at h
      | some v=>
        rcases v with ⟨z,zs⟩
        rw [hi,ht,merge] at h
        have he:=congrArg Prod.snd (Option.some.inj h)
        dsimp only at he
        rw [←he]
        intro a ha
        rcases List.mem_append.mp ha with ha|ha
        · simpa using (List.mem_singleton.mp ha ▸ rfl : a.2.2=y)
        · exact ih z zs ht a ha
lemma blockAt_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ)
    (U : Finset L) (y : Y) (hy : y∈F) : Spec B F label q U 1 (blockAt B label q U y) := by
  have hs:=collect_items_spec B F label q (U.sort (·≤·)) (Finset.sort_nodup U (·≤·)) y hy
  simp only [Finset.sort_toFinset,Finset.length_sort] at hs
  cases he : blockAt B label q U y with
  | none=>trivial
  | some v=>
    rcases v with ⟨k,xs⟩
    change Spec B F label q U U.card (blockAt B label q U y) at hs
    rw [he] at hs
    refine ⟨hs.1,hs.2.1,?_,hs.2.2.2⟩
    have hsub : destinations xs⊆{y} := by
      intro z hz
      obtain ⟨a,ha,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hz)
      exact Finset.mem_singleton.mpr (collect_dest B label q (U.sort (·≤·)) y k xs he a ha)
    exact (Finset.card_le_card hsub).trans (by simp)
lemma block_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (U : Finset L) :
    Spec B F label q U 1 (block B F label q U) := by
  apply select_spec _ _ trivial
  intro x hx
  obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hx
  exact blockAt_spec B F label q U y ((Finset.mem_sort (·≤·)).mp hy)
end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BluePlan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {L R Y : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder Y]
omit [LinearOrder R] in
lemma spec_mono (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (U : Finset L)
    (c d : ℕ) (hcd : c≤d) (x : Candidate (List (Atom L R Y))) (hx : Spec B F label q U c x) : Spec B F label q U d x := by
  cases x with
  | none=>trivial
  | some x=>exact ⟨hx.1,hx.2.1,hx.2.2.1.trans hcd,hx.2.2.2⟩
end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionFair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionFair
open WordList BinaryArithmetic
open Categorical.Explicit
variable {n q a p r c : ℕ}
section Correct
variable (F S Q : Finset (Fin n)) (part : Fin q→Fin a) (hp : Function.Surjective part)
    (o : Fin a→Fin q) (loc : Fin q→Fin n) (redLoc : Fin r→Fin n) (blueLoc blueDest : Fin c→Fin n)
    (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ)
noncomputable def result
    (bits : Categorical.BinaryOracleIndex (Fin q) a (exponent a) (samples q a)→Bool) : Finset (Fin n) :=
  let xs:=BinaryCompletionAlgorithm.choices k base distance weight redBase redDistance part hp
    (Categorical.binarySeedEquiv (Fin q) a (exponent a) (samples q a) bits)
  Completion.Canonical.realize F S Q part o loc redLoc blueLoc blueDest xs
    (BinaryRationalSort.indexSet (fun i=>weight i*BinaryCompletion.capped (redBase i) (redDistance i) xs.toFinset) k)
end Correct
end MetricKMedianRecovery.BitMachine.BinaryCompletionFair

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RationalBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open Completion Categorical FiniteSampling BinaryBranchContext
variable {n m : ℕ}
noncomputable def result (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (hH : ∀ i,(balls δ F s i).Nonempty) (sel dest : Fin m→Fin n) (k : ℕ)
    (bits : BinaryOracleIndex (Fin (s.leaves.length*n)) s.leaves.length (Explicit.exponent s.leaves.length)
      (Explicit.samples (s.leaves.length*n) s.leaves.length)→Bool) : Finset (Fin n) :=
  let red:=(S\s.deleted).filter (fun i=>colors i=1)
  let green:=(S\s.deleted).filter (fun i=>colors i=0)
  let loc:=CopyGround.location (balls δ F s) hH
  BinaryCompletionFair.result F S s.deleted CopyGround.part (CopyGround.part_surjective (balls δ F s) hH)
    (CopyGround.origin (balls δ F s) hH) loc (SortedIndex.enum red) sel dest k
    (fun i=>RationalSampling.reference δ S Δ s (SortedIndex.enum D i))
    (fun i e=>δ (SortedIndex.enum D i) (loc e))
    (fun i=>RationalSampling.assignmentWeight δ D S Δ s (SortedIndex.enum red i))
    (fun i=>RationalSampling.reference δ green Δ ⟨∅,s.leaves⟩ (SortedIndex.enum red i))
    (fun i e=>δ (SortedIndex.enum red i) (loc e)) bits
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

end OAI
end


