-- Prove2me | Definitions.Def_QTolTest1673_Unified_Supplement_Model
-- name    : QTolTest1673_Unified_Supplement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:17:33.363019+00:00
-- url     : https://prove2.me/theorems/8be99f0a-9597-48d8-b5c8-5e30fd8b2b29
-- title:
--   Query bounds and explicit threshold functions
-- statement:
--   Let $f:\mathbb F_2^n\to\{\pm1\}$ be recorded by its bit function. Quantum algorithms, their probabilities and actual query counts use the published adaptive quantum query model; randomized adaptive classical algorithms use the published behaviour-strategy query model with deterministic answers $x\mapsto f(x)$. Classical correctness means success at least $2/3$ separately on each tolerant promise. A classical lower bound quantifies over every correct algorithm and every uniform query budget. A quantum lower bound charges the maximum query count on a positive-probability transcript over all inputs. Quantum upper bounds exhibit actual algorithms; the nonadaptive version repeats a fixed circuit with a final classical decision rule.
--
--   The finite uniform average is the sum divided by the cardinality. The block mean and the Section 11 thresholds are computed from the data:
--   $$e_s=\frac{1-2^{-2^s}\binom{2^s}{2^{s-1}}}{2},\quad t=\lceil\log_2 k\rceil,\quad s=2t,\quad L=2^s,$$
--   $$\mu_L=\frac{\sum_{j=0}^L\binom Lj\min(j,L-j)}{L2^L},\quad\varepsilon_1(k)=\mu_L-\frac3{4L^2},\quad\varepsilon_2(k)=\mu_L-\frac1{4L^2}.$$
--   The file also defines the mass gap and extension by irrelevant variables. These are interfaces for the companion results, not assumptions that assert any query bound. Empty finite averages and the unused $L=0$ formula totalize to zero; probabilistic uses have nonempty carriers, and the asymptotic threshold results apply for sufficiently large $k$.
--
--   Nonadaptive upper bounds use independent repetitions of the same one-query circuit; the decision rule sees the recorded outcomes only after all queries.
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, §2.2 p.14; (4) p.22; §5.2 p.25; §11.1 pp.48–49

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Classes
import Definitions.Def_QTolTest1673_Unified_Tester
import Definitions.Def_QuarticGap_QueryAlg

noncomputable section
open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum

namespace QTolTest1673.Unified.Supplement

/-- Uniform average on a finite set. All probabilistic uses have nonempty carriers. -/
def avg {X : Type*} [Fintype X] (g : X → ℝ) : ℝ :=
  (Fintype.card X : ℝ)⁻¹ * ∑ x, g x

/-- Probability of an event for a finite PMF. -/
def prob {X : Type*} [Fintype X] (p : PMF X) (E : X → Prop) : ℝ :=
  ∑ x, if E x then (p x).toReal else 0

/-- Probability under the independent uniform law. -/
def frac {X : Type*} [Fintype X] (E : X → Prop) : ℝ := avg fun x => if E x then 1 else 0

/-- The paper's mass gap, §2.2 p.14. -/
def gap (e₁ e₂ : ℝ) : ℝ := (1-2*e₁)^2-(1-2*e₂)

/-- General randomized adaptive classical model; the oracle returns the input's bit. -/
abbrev CAlg (n : ℕ) := QuarticGap.QueryAlg (V n) Bool Bool

def answer {n : ℕ} (f : BoolFn n) (x : V n) : PMF Bool := PMF.pure (f x)

/-- Classical tolerant correctness, success at least 2/3 on each promised input. -/
def CCorrect {n : ℕ} (A : CAlg n) (S : Set (BoolFn n)) (e₁ e₂ : ℝ) : Prop :=
  ∀ f, (distToSet f S ≤ e₁ → 2/3 ≤ A.outProb (answer f) true) ∧
    (e₂ ≤ distToSet f S → 2/3 ≤ A.outProb (answer f) false)

/-- A classical lower bound means every correct bounded-query algorithm pays the bound. -/
def CLower {n : ℕ} (S : Set (BoolFn n)) (e₁ e₂ B : ℝ) : Prop :=
  ∀ A : CAlg n, CCorrect A S e₁ e₂ → ∀ q : ℕ,
    (∀ f, A.MakesAtMost (answer f) q) → B ≤ (q : ℝ)

/-- Maximum number of actual queries over all inputs and positive-probability branches. -/
def qcost {X : Type} [Fintype X] [DecidableEq X] (A : AdaptiveQueryAlg X Bool) : ℕ :=
  Finset.univ.sup fun f : X → Bool => A.maxQueries f

def QLower {n : ℕ} (S : Set (BoolFn n)) (e₁ e₂ B : ℝ) : Prop :=
  ∀ A : AdaptiveQueryAlg (V n) Bool, IsTolerantTester A S e₁ e₂ (1/3) →
    B ≤ (qcost A : ℝ)

/-- Quantum upper bound, by an actual algorithm chosen independently of the unknown f. -/
def QUpper {n : ℕ} (S : Set (BoolFn n)) (e₁ e₂ B : ℝ) : Prop :=
  ∃ A : AdaptiveQueryAlg (V n) Bool,
    IsTolerantTester A S e₁ e₂ (1/3) ∧ (worstCaseQueries A : ℝ) ≤ B

/-- Nonadaptive upper bound: independent repetitions of one fixed one-query circuit. -/
def NQUpper {n : ℕ} (S : Set (BoolFn n)) (e₁ e₂ δ B : ℝ) : Prop :=
  ∃ m w : ℕ, ∃ A : QueryAlg (V n) Bool (Fin w) 1,
    ∃ decision : List ((V n × Bool) × Fin w) → Bool,
      IsTolerantTester (nonadaptiveTester m A decision) S e₁ e₂ δ ∧
      (worstCaseQueries (nonadaptiveTester m A decision) : ℝ) ≤ B

/-- Equation (4), p.22: the mean distance to a constant on a block of 2^s points. -/
def blockMean (s : ℕ) : ℝ :=
  (1 - (Nat.choose (2^s) (2^s/2) : ℝ) / (2 : ℝ)^(2^s))/2

/-- First m coordinates, for adding irrelevant variables; the proof m≤n makes this exact. -/
def extendFn {m n : ℕ} (hmn : m ≤ n) (f : BoolFn m) : BoolFn n :=
  fun x => f (fun i => x (Fin.castLE hmn i))

/-- Section 11.1, pp.48–49, explicit parameter functions (not free thresholds). -/
def logceil (k : ℕ) : ℕ := ⌈Real.logb 2 (k : ℝ)⌉₊
def s11 (k : ℕ) : ℕ := 2 * logceil k
def n11 (k : ℕ) : ℕ := k + s11 k
def L11 (k : ℕ) : ℕ := 2^(s11 k)
def mu (L : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (L+1), (Nat.choose L j : ℝ) * (min j (L-j) : ℕ)) /
    ((L : ℝ) * (2 : ℝ)^L)
def epsOne (k : ℕ) : ℝ := mu (L11 k) - 3 / (4*(L11 k : ℝ)^2)
def epsTwo (k : ℕ) : ℝ := mu (L11 k) - 1 / (4*(L11 k : ℝ)^2)

end QTolTest1673.Unified.Supplement


