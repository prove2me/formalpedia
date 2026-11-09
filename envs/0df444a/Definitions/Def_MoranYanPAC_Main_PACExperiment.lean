-- Prove2me | Definitions.Def_MoranYanPAC_Main_PACExperiment
-- name    : MoranYanPAC_Main_PACExperiment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T03:06:29.616883+00:00
-- url     : https://prove2.me/theorems/4268023e-6164-4e3e-ac9f-5d7a59b02682
-- title:
--   Population error, iid samples and the randomized PAC experiment
-- statement:
--   Let $P$ be a probability measure on labeled examples $X\times\{0,1\}$. The **population loss** and **realizability** condition are
--
--   $$L_P(h)=P\{(x,y):h(x)\ne y\},\qquad\exists h^*\in H,\quad h^*(x)=y\ \ P\text{-almost surely}.$$
--
--   The sample law $P^n$ reuses the published independent-product law. After sampling $S\sim P^n$, the rule draws $h\sim A(S)$. Its success probability is
--
--   $$\int A(S)\{h:L_P(h)\le\alpha\}\,dP^n(S).$$
--
--   The individual loss events, the one-sample uniform bad events and the two-sample uniform comparison events are explicitly required measurable by the VC-event predicate. The PAC-experiment predicate requires measurable losses for every possible output and almost-everywhere measurability of the conditional success probability. These predicates assert only well-posedness, with no probability bound, accuracy or privacy conclusion inside them. The headline theorem asserts the selected learner's experiment well-posedness as a conclusion. Thus an unmeasurable learner cannot evade its accuracy obligation. No countability, separability, standard-Borel or finite-support distribution assumption is included. The outer integral is a nonnegative integral of conditional probabilities, not a Bochner integral with a nonintegrability default.
-- source:
--   Shay Moran, Chao Yan, STOC 2027 submission #772 (October 2026), Section 4.1, pp. 13–14, Definition 4, p. 14, and Lemma 1, p. 15 (PDF pp. 13–15); ordinary measurable-event convention

import Mathlib
import Definitions.Def_UnderstandingML_Framework
import Definitions.Def_MoranYanPAC_Main_PrivateLaw
import Definitions.Def_MoranYanPAC_Main_EmpiricalLoss

set_option autoImplicit false

open scoped ENNReal

open MeasureTheory

namespace MoranYanPAC.Main

/-- Section 4.1, p. 13: population misclassification probability.
Statements using it require the loss event measurable and P a probability measure. -/
noncomputable def populationLoss {X : Type*} [MeasurableSpace X]
    (P : Measure (X × Bool)) (h : X → Bool) : ℝ :=
  (P {z | h z.1 ≠ z.2}).toReal

/-- Genuine independent, identically distributed labeled data, including the empty product. -/
noncomputable def sampleLaw {X : Type*} [MeasurableSpace X]
    (P : Measure (X × Bool)) (n : ℕ) : Measure (Fin n → X × Bool) :=
  UnderstandingML.iidLaw P n

/-- Realizability uses one fixed member of H, not a target selected separately at each point. -/
def Realizable {X : Type*} [MeasurableSpace X]
    (H : Set (X → Bool)) (P : Measure (X × Bool)) : Prop :=
  ∃ h ∈ H, ∀ᵐ z ∂P, h z.1 = z.2

/-- The ordinary measurable-event convention for VC generalization, made explicit.
Besides individual loss events, both the one-sample bad events and the two-sample
comparison events are measurable. No countable subclass or separability is assumed. -/
def VCEventsMeasurable {X : Type*} [MeasurableSpace X]
    (G : Set (X → Bool)) (P : Measure (X × Bool)) : Prop :=
  (∀ h ∈ G, MeasurableSet {z : X × Bool | h z.1 ≠ z.2}) ∧
  (∀ (n : ℕ) (a b : ℝ), MeasurableSet
    {s : Fin n → X × Bool | ∃ h ∈ G,
      empiricalRate (List.ofFn s) h ≤ a ∧ b < populationLoss P h}) ∧
  (∀ (n m : ℕ) (a b : ℝ), MeasurableSet
    {p : (Fin n → X × Bool) × (Fin m → X × Bool) | ∃ h ∈ G,
      empiricalRate (List.ofFn p.1) h ≤ a ∧ b < empiricalRate (List.ofFn p.2) h})

/-- Conditional probability of successful prediction after observing one sample. -/
noncomputable def conditionalSuccess {X : Type*} [MeasurableSpace X]
    (A : List (X × Bool) → PMF (X → Bool)) (P : Measure (X × Bool))
    (α : ℝ) (S : List (X × Bool)) : ℝ≥0∞ :=
  eventProbability (A S) {h | populationLoss P h ≤ α}

/-- The standard well-posedness convention for the actual randomized PAC experiment.
Only measurability is asserted here, never privacy, accuracy, a count, or a probability bound. -/
def PACExperimentMeasurable {X : Type*} [MeasurableSpace X]
    (A : List (X × Bool) → PMF (X → Bool)) (P : Measure (X × Bool)) (α : ℝ) (n : ℕ) : Prop :=
  (∀ S : List (X × Bool), ∀ h ∈ (A S).support,
    MeasurableSet {z : X × Bool | h z.1 ≠ z.2}) ∧
  AEMeasurable (fun s : Fin n → X × Bool => conditionalSuccess A P α (List.ofFn s))
    (sampleLaw P n)

/-- Joint probability over the iid sample and the learner's independent randomization.
The inner quantity is a probability from a PMF, and the outer integral is nonnegative.
Theorems require PACExperimentMeasurable, so this is the ordinary iterated probability. -/
noncomputable def pacSuccessProbability {X : Type*} [MeasurableSpace X]
    (A : List (X × Bool) → PMF (X → Bool)) (P : Measure (X × Bool))
    (α : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ s, conditionalSuccess A P α (List.ofFn s) ∂sampleLaw P n

/-- Simultaneous relative-VC success event, with empirical errors allowed up to α/2. -/
def vcSuccessEvent {X : Type*} [MeasurableSpace X]
    (G : Set (X → Bool)) (P : Measure (X × Bool)) (α : ℝ) (n : ℕ) : Set (Fin n → X × Bool) :=
  {s | ∀ h ∈ G, empiricalRate (List.ofFn s) h ≤ α / 2 → populationLoss P h ≤ α}

end MoranYanPAC.Main


