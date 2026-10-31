-- Prove2me | Definitions.Def_GongReusable_Myopic_Model
-- name    : GongReusable_Myopic_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:24:10.121848+00:00
-- url     : https://prove2.me/theorems/c3c0ea4a-b980-4bd6-abaf-4c43301b01c3
-- title:
--   Reusable inventory, integrable rental fees and operational assortment decisions
-- statement:
--   There are finitely many products P, arbitrary user types Z, and a finite family of feasible product subsets containing the empty offer. Each product has an arbitrary natural capacity, a Borel probability law on extended nonnegative usage durations, and a measurable integrable real rental-fee function. Its mean fee is the integral of that function and is nonnegative. Realized fees need not be nonnegative. Choice probabilities are defined on every subset, include no purchase, and obey product regularity for S contained in a feasible U. There is no downward-closure assumption.
--
--   A fixed arrival sequence consists of T types and nondecreasing finite nonnegative real epochs. A history records each past epoch, offer, selected product or no purchase, and sampled duration; future positions are initialized to zero. A product is available precisely when the number of its past rentals with return epochs strictly after the current epoch is less than its capacity. Returns at the current epoch are processed before the next ordered offer. A duration is revealed after allocation.
--
--   Policies are measurable randomized rules on their own history, current epoch and current choice model. An infeasible proposal is interpreted as rejection; all feasible behavior is representable, and the constant rejection policy is explicitly constructed. The myopic offer maximizes the sum of mean fees times choice probabilities among feasible available offers. An arbitrary measurable tie proposal is used if maximizing, otherwise the first member of a fixed enumeration of maximizers is used. No random future variable, other policy history or coupling queue enters this decision interface.
-- source:
--   Gong, Goyal, Iyengar, Simchi-Levi, Udwani and Wang, Online Assortment Optimization with Reusable Resources, https://doi.org/10.1287/mnsc.2021.4134, supplied manuscript (SSRN 3334789 footers; journal pagination and revision year unverified), printed pp. 3–6, 9 / PDF pp. 3–6, 9

import Definitions.Def_GongReusable_Myopic_Choice
import Definitions.Def_GongReusable_Myopic_RandomizedRule

open MeasureTheory
open scoped ENNReal
noncomputable section

namespace GongReusable.Myopic

abbrev Rental (P : Type) := NNReal × Finset P × Option P × ℝ≥0∞
abbrev History (P : Type) := ℕ → Rental P

/-- Physical data. Validity is separate so the copy construction is literal data. -/
structure Model (P Z : Type) [Fintype P] where
  capacity : P → ℕ
  feasible : Finset (Finset P)
  choice : Z → ChoiceProb P
  duration : P → Measure ℝ≥0∞
  rentalRevenue : P → ℝ≥0∞ → ℝ

def meanRevenue {P Z : Type} [Fintype P] (M : Model P Z) (j : P) : ℝ :=
  ∫ d, M.rentalRevenue j d ∂M.duration j

structure Valid {P Z : Type} [Fintype P] (M : Model P Z) : Prop where
  reject : ∅ ∈ M.feasible
  prob : ∀ j, IsProbabilityMeasure (M.duration j)
  fee_measurable : ∀ j, Measurable (M.rentalRevenue j)
  fee_integrable : ∀ j, Integrable (M.rentalRevenue j) (M.duration j)
  mean_nonneg : ∀ j, 0 ≤ meanRevenue M j
  choice_law : ∀ z, IsChoiceLaw (M.choice z)
  regular : ∀ z S U, S ⊆ U → U ∈ M.feasible →
    ∀ j ∈ S, M.choice z U (some j) ≤ M.choice z S (some j)

structure Arrivals (Z : Type) (T : ℕ) where
  epoch : Fin T → NNReal
  type : Fin T → Z
  ordered : Monotone epoch

def initialHistory {P : Type} : History P := fun _ => (0, ∅, none, 0)

def available {P Z : Type} [Fintype P] (M : Model P Z)
    (t : ℕ) (a : NNReal) (h : History P) : Finset P := by
  classical
  exact Finset.univ.filter fun j =>
    ((Finset.range t).filter fun s =>
      (h s).2.2.1 = some j ∧ (a : ℝ≥0∞) < (h s).1 + (h s).2.2.2).card < M.capacity j

def offers {P Z : Type} [Fintype P] (M : Model P Z)
    (t : ℕ) (a : NNReal) (h : History P) : Finset (Finset P) := by
  classical
  exact M.feasible.filter fun S => S ⊆ available M t a h

def revenue {P Z : Type} [Fintype P] (M : Model P Z)
    (q : ChoiceProb P) (S : Finset P) : ℝ :=
  ∑ j ∈ S, meanRevenue M j * q S (some j)

/-- A randomized history policy. Its only random input is a fresh uniform variable.
The fixed future input may inform the chosen benchmark policy, never future draws. -/
abbrev Policy (P : Type) [Fintype P] :=
  RandomizedRule (ℕ × NNReal × ChoiceProb P) (History P) (Finset P)

def rejection {P : Type} [Fintype P] : Policy P where
  act := fun _ _ _ => ∅
  measurable_act := fun _ => measurable_const

/-- Infeasible proposals mean rejection, making the admissible class nonempty on every history. -/
def offer {P Z : Type} [Fintype P] (M : Model P Z) (π : Policy P)
    (t : ℕ) (a : NNReal) (q : ChoiceProb P) (h : History P) (u : ℝ) : Finset P := by
  classical
  exact if π.act (t, a, q) h u ∈ offers M t a h then π.act (t, a, q) h u else ∅

/-- All maximizing feasible offers; no closure of the feasible family is assumed. -/
def maximizers {P Z : Type} [Fintype P] (M : Model P Z)
    (t : ℕ) (a : NNReal) (q : ChoiceProb P) (h : History P) : Finset (Finset P) := by
  classical
  exact (offers M t a h).filter fun S =>
    ∀ U ∈ offers M t a h, revenue M q U ≤ revenue M q S

/-- A concrete maximizing selection, with arbitrary measurable tie proposals. -/
def myopicOffer {P Z : Type} [Fintype P] (M : Model P Z) (tie : Policy P)
    (t : ℕ) (a : NNReal) (q : ChoiceProb P) (h : History P) (u : ℝ) : Finset P := by
  classical
  let A := maximizers M t a q h
  exact if tie.act (t, a, q) h u ∈ A then tie.act (t, a, q) h u else A.toList.headD ∅

end GongReusable.Myopic


