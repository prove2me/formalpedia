-- Prove2me | Definitions.Def_MetricTesting_Characterization_Supplement_testing
-- name    : MetricTesting_Characterization_Supplement_testing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:20:18.17965+00:00
-- url     : https://prove2.me/theorems/65f0fd63-c39a-4b43-858f-165c140f8afa
-- title:
--   Fixed-order operational query complexity and rate functions
-- statement:
--   A testing problem specifies its valid target arrays and normalized repair distance. Testers use the published measurable randomized real-answer decision tree. For a fixed order $n$ and proximity $\epsilon$, one-sided testing has perfect completeness; two-sided testing accepts valid inputs with probability at least $2/3$. Both reject inputs at distance strictly greater than $\epsilon$ with probability at least $2/3$. The query cap is a worst-case bound for every input and seed.
--
--   Nonadaptive queries form a prefix of a list fixed by the seed before oracle answers. Early termination is permitted. The complexity $Q$ is the infimum of feasible natural query caps, with value $+\infty$ when none exists. The rational-promise version only restricts which inputs require the success guarantee; the same real-answer oracle model and worst-case cap apply. Bounded inputs may use bounded repairs or arbitrary positive metric repairs.
--
--   For $n\ge3$ and $0<\epsilon\le1$, define
--
--   $$F(n,\epsilon)=\begin{cases}n^2&\epsilon\le n^{-2},\\n/\sqrt\epsilon&n^{-2}<\epsilon\le n^{-1},\\\sqrt n/\epsilon&n^{-1}<\epsilon\le n^{-1/2},\\(n/\epsilon)^{2/3}&n^{-1/2}<\epsilon\le1.\end{cases}$$
--
--   The adaptive rate is $\sqrt{n/\log n}$, with the natural logarithm. Adjacent branches agree at their boundaries. Complexity is represented in extended nonnegative reals so an empty feasible set cannot silently become zero.
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), Definitions 2.1–2.2, printed p. 6 (PDF p. 7); §6.4–6.5, printed pp. 29–31 (PDF pp. 30–32)

import Mathlib
import Definitions.Def_MetricTesting_Characterization_Supplement_completion
import Definitions.Def_MetricTesting_Characterization_Supplement_bit_size
import Definitions.Def_MetricTesting_Characterization_decision_tree

set_option autoImplicit false
noncomputable section

namespace MetricTesting.Characterization.Supplement

open MeasureTheory

/-- Target validity and distance are computed from the represented target class. -/
structure TestingProblem (Λ : Set NNReal) where
  good : {n : ℕ} → Array Λ n → Prop
  distance : {n : ℕ} → Array Λ n → ℝ

def localProblem (F : LocalData) : TestingProblem F.values where
  good := Valid F
  distance := repairDistance F

def crossProblem (Λ : Set NNReal) (F : LocalData) : TestingProblem Λ where
  good := fun {n} D => ∃ B : Array F.values n, Valid F B ∧ ∀ e, (B e : NNReal) = (D e : NNReal)
  distance := crossDistance F

def boundedProblem (C : ℝ) (hC : 1 < C) (unrestrictedRepairs : Bool) :
    TestingProblem (BoundedValues C) :=
  if unrestrictedRepairs then crossProblem (BoundedValues C) positiveMetric
  else localProblem (boundedMetric C hC)

/-- All queries are prefixes of a schedule fixed by the input-independent seed. -/
def Nonadaptive {Λ : Set NNReal} {n : ℕ} (A : RandomTree Λ n) (q : ℕ) : Prop :=
  ∃ schedule : A.Seed → List (Edge n),
    (∀ ω, (schedule ω).length ≤ q) ∧
    ∀ D : Array Λ n, ∀ ω,
      ((run (A.rule ω) (fun _ => D) (q+1)).history.map Prod.fst).IsPrefix (schedule ω)

/-- Performance may be restricted to an input promise, without changing oracle answers or randomness. -/
def TesterOn {Λ : Set NNReal} {n : ℕ} (P : TestingProblem Λ)
    (domain : Array Λ n → Prop) (oneSided nonadaptive : Bool) (ε : ℝ) (q : ℕ)
    (A : RandomTree Λ n) : Prop :=
  StopsWithin A q ∧ (nonadaptive = true → Nonadaptive A q) ∧
  (∀ D, MeasurableSet (acceptEvent A q D) ∧ MeasurableSet (rejectEvent A q D)) ∧
  (∀ D, domain D → P.good D →
    if oneSided then A.law (acceptEvent A q D) = 1
    else (2/3 : ENNReal) ≤ A.law (acceptEvent A q D)) ∧
  (∀ D, domain D → ε < P.distance D → (2/3 : ENNReal) ≤ A.law (rejectEvent A q D))

/-- Infimum of natural worst-case caps; +infinity if no tester exists. -/
def queryComplexity {Λ : Set NNReal} (P : TestingProblem Λ) (n : ℕ)
    (domain : Array Λ n → Prop) (oneSided nonadaptive : Bool) (ε : ℝ) : ENNReal :=
  ⨅ (q : ℕ) (_ : ∃ A : RandomTree Λ n, TesterOn P domain oneSided nonadaptive ε q A),
    (q : ENNReal)

def Q {Λ : Set NNReal} (P : TestingProblem Λ) (n : ℕ)
    (oneSided nonadaptive : Bool) (ε : ℝ) : ENNReal :=
  queryComplexity P n (fun _ => True) oneSided nonadaptive ε

def rationalQ {Λ : Set NNReal} (P : TestingProblem Λ) (B n : ℕ)
    (oneSided nonadaptive : Bool) (ε : ℝ) : ENNReal :=
  queryComplexity P n (SmallRational B) oneSided nonadaptive ε

/-- All four source regimes; adjacent formulas coincide at their shared boundaries. -/
def rate (n : ℕ) (ε : ℝ) : ℝ :=
  if ε ≤ (n : ℝ)⁻¹^2 then (n : ℝ)^2
  else if ε ≤ (n : ℝ)⁻¹ then (n : ℝ) / Real.sqrt ε
  else if ε ≤ (Real.sqrt (n : ℝ))⁻¹ then Real.sqrt (n : ℝ) / ε
  else ((n : ℝ) / ε) ^ (2/3 : ℝ)

def adaptiveRate (n : ℕ) : ℝ := Real.sqrt ((n : ℝ) / Real.log (n : ℝ))

end MetricTesting.Characterization.Supplement


