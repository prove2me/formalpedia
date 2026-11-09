-- Prove2me | Definitions.Def_MetricTesting_Characterization_decision_tree
-- name    : MetricTesting_Characterization_decision_tree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:00.751478+00:00
-- url     : https://prove2.me/theorems/e23bb3e1-885e-4182-9f77-268531afb95b
-- title:
--   Operational adaptive decision trees and one-sided testability
-- statement:
--   A deterministic decision tree chooses either acceptance, rejection, or an unordered pair to query from its finite history of queried pairs and exact $\Lambda$-valued answers. A randomized tree has an arbitrary probability space of internal seeds, independent of the input, and a measurable seed-and-history rule. Its transcript is computed recursively by answering every query from the input array. Stopped states remain stopped, and repeated queries each count toward the worst-case cost.
--
--   A one-sided $q$-query $\epsilon$-tester terminates after at most $q$ queries for every input and seed, has measurable acceptance and rejection events, and satisfies
--   $$D\in\mathcal P_n\Longrightarrow\Pr[\text{accept }D]=1,\qquad d(D,\mathcal P_n)>\epsilon\Longrightarrow\Pr[\text{reject }D]\ge\frac23.$$
--   The family is one-sided testable when
--   $$\forall\epsilon>0\ \exists q\in\mathbb N\ \forall n\ge1\ \exists A_n:\ A_n\text{ is such a tester}.$$
--   There is no finite-alphabet, time, uniform-computability, or numerical-precision restriction. All finite transcript lengths use their usual product measurable spaces, combined by a disjoint union over the length. This operational model keeps adaptive testers independent from removal or completion conditions.
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), p. 6, Definition 2.1 (PDF p. 7); p. 9, Lemmas 3.1–3.2 (PDF p. 10)

import Mathlib
import Definitions.Def_MetricTesting_Characterization_arrays

set_option autoImplicit false

noncomputable section

namespace MetricTesting.Characterization

open MeasureTheory

/-- Finite transcripts use the disjoint union of their fixed-length product
spaces. This preserves real answers rather than making them discrete. -/
instance listSpace {α : Type} [MeasurableSpace α] : MeasurableSpace (List α) :=
  MeasurableSpace.comap
    (fun h : List α => (⟨h.length, fun i : Fin h.length => h[i]⟩ : Σ m : ℕ, Fin m → α))
    inferInstance

abbrev History (Λ : Set NNReal) (n : ℕ) := List (Edge n × Λ)
abbrev Action (n : ℕ) := Bool ⊕ Edge n

instance optionBoolSpace : MeasurableSpace (Option Bool) := ⊤
abbrev DecisionTree (Λ : Set NNReal) (n : ℕ) := History Λ n → Action n

structure RunState (Λ : Set NNReal) (n : ℕ) where
  history : History Λ n
  decision : Option Bool

/-- true accepts; false rejects. Stopped states are absorbing. The oracle
may use the history, allowing lazy exposure as well as a fixed input. -/
def run {Λ : Set NNReal} {n : ℕ} (T : DecisionTree Λ n)
    (oracle : History Λ n → Edge n → Λ) : ℕ → RunState Λ n
  | 0 => ⟨[], none⟩
  | t + 1 =>
    let s := run T oracle t
    match s.decision with
    | some _ => s
    | none => match T s.history with
      | .inl b => ⟨s.history, some b⟩
      | .inr e => ⟨s.history ++ [(e, oracle s.history e)], none⟩

/-- The trace contains all finite prefixes, including termination. No cap on
transcript length is imposed on the deterministic coupling lemma. -/
def trace {Λ : Set NNReal} {n : ℕ} (T : DecisionTree Λ n)
    (oracle : History Λ n → Edge n → Λ) : ℕ → History Λ n × Option Bool :=
  fun t => let s := run T oracle t; (s.history, s.decision)

/-- An arbitrary input-independent probability seed and a measurable adaptive
rule; performance and query bounds are predicates, not fields. -/
structure RandomTree (Λ : Set NNReal) (n : ℕ) where
  Seed : Type
  seedSpace : MeasurableSpace Seed
  law : @Measure Seed seedSpace
  probability : @IsProbabilityMeasure Seed seedSpace law
  rule : Seed → DecisionTree Λ n
  rule_measurable : @Measurable (Seed × History Λ n) (Action n)
    (@MeasurableSpace.prod Seed (History Λ n) seedSpace inferInstance)
    inferInstance (fun p => rule p.1 p.2)

attribute [instance] RandomTree.seedSpace RandomTree.probability

def StopsWithin {Λ : Set NNReal} {n : ℕ} (A : RandomTree Λ n) (q : ℕ) : Prop :=
  ∀ (D : Array Λ n) (ω : A.Seed),
    (run (A.rule ω) (fun _ => D) (q+1)).decision.isSome ∧
    (run (A.rule ω) (fun _ => D) (q+1)).history.length ≤ q

def acceptEvent {Λ : Set NNReal} {n : ℕ} (A : RandomTree Λ n)
    (q : ℕ) (D : Array Λ n) : Set A.Seed :=
  {ω | (run (A.rule ω) (fun _ => D) (q+1)).decision = some true}

def rejectEvent {Λ : Set NNReal} {n : ℕ} (A : RandomTree Λ n)
    (q : ℕ) (D : Array Λ n) : Set A.Seed :=
  {ω | (run (A.rule ω) (fun _ => D) (q+1)).decision = some false}

/-- Event measurability is stated explicitly so no nonmeasurable-event outer
measure is used in any success claim. -/
def IsTester (F : LocalData) {n : ℕ} (ε : ℝ) (q : ℕ)
    (A : RandomTree F.values n) : Prop :=
  StopsWithin A q ∧
  (∀ D : Array F.values n,
    MeasurableSet (acceptEvent A q D) ∧ MeasurableSet (rejectEvent A q D)) ∧
  (∀ D : Array F.values n, Valid F D → A.law (acceptEvent A q D) = 1) ∧
  (∀ D : Array F.values n, ε < repairDistance F D →
    (2 / 3 : ENNReal) ≤ A.law (rejectEvent A q D))

def HasTester (F : LocalData) (ε : ℝ) (q : ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ A : RandomTree F.values n, IsTester F ε q A

def OneSidedTestable (F : LocalData) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ q : ℕ, HasTester F ε q

end MetricTesting.Characterization


