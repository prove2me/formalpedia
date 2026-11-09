-- Prove2me | Definitions.Def_FluidGreedyMatching_CliqueBomb_ProcessModel
-- name    : FluidGreedyMatching_CliqueBomb_ProcessModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:57:00.886219+00:00
-- url     : https://prove2.me/theorems/40f10bae-10d2-4858-bb7b-287fe39eb5a6
-- title:
--   Adapted process, ODE and certification interfaces
-- statement:
--   For an arbitrary finite dimension $a$, a process family consists of probability spaces $(\Omega_n,\mathcal F_n,P_n)$, filtrations $(\mathcal F_{n,t})_{t\ge0}$, and adapted real vectors $Z_{n,t}\in\mathbb R^a$. The spaces may vary with $n$. Index $n$ represents source size $N=n+1$; write $z_{n,t}=Z_{n,t}/N$ and $\Delta Z_{n,t}=Z_{n,t+1}-Z_{n,t}$. The drift is the conditional expectation of this increment given the history. The maximum norm is used on finite products.
--
--   Convergence in probability of $X_n$ to $L$ means
--   $$\forall\delta>0,\quad P_n(|X_n-L|>\delta)\longrightarrow0.$$
--
--   Staying in a time-state domain through step $t$ expresses that $t$ precedes first exit. A maximal nonnegative ODE trajectory has its initial value, continuity, the prescribed derivatives, lies in the domain, approaches its boundary, and agrees with every other local solution on the overlap. Its clearance cutoff is the supremum of times through which the whole trajectory stays at distance at least $C\lambda$ from the boundary. Zero is inserted into this set for the finitely many sizes where the initial clearance is too small. A bounded open box is a product of bounded open coordinate intervals.
--
--   Count-law closure says that the conditional probability of every Borel increment event is a function of the current count vector. It is a hypothesis, not an asserted property of all RDO counts. An algorithm run is defined by its initial state, measurability in the filtration, and the conditional next-state probabilities of the MRG or RDO kernel. These interfaces contain no drift bounds, certification conclusions, or assumed convergence.
-- source:
--   Sayan Mukherjee, Fluid Limits and Upper Bounds for Randomized Greedy Matching, STOC 2027 submission #492 (October 2026), Section 2.3, p. 7; Section 3.3 and Lemma 3.1, pp. 11–12

import Mathlib
import Definitions.Def_FluidGreedyMatching_CliqueBomb_MRGModel

set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology

namespace FluidGreedyMatching.CliqueBomb

noncomputable section
universe u

abbrev Vec (a : ℕ) := Fin a → ℝ

/-- Index n represents the positive size n+1 throughout all asymptotic statements. -/
def scale (n : ℕ) : ℝ := (n + 1 : ℕ)

/-- Arbitrary real adapted processes, on probability spaces which may vary with n.
There are no bounded-jump, drift, ODE or convergence assumptions in this data type. -/
structure ProcessFamily (a : ℕ) where
  space : ℕ → Type u
  measurable : (n : ℕ) → MeasurableSpace (space n)
  law : (n : ℕ) → @Measure (space n) (measurable n)
  probability : ∀ n, @IsProbabilityMeasure (space n) (measurable n) (law n)
  history : (n : ℕ) → Filtration ℕ (measurable n)
  Z : (n : ℕ) → ℕ → space n → Vec a
  adapted : ∀ n t, StronglyMeasurable[history n t] (Z n t)

attribute [instance] ProcessFamily.measurable ProcessFamily.probability

def normalized {a : ℕ} (P : ProcessFamily.{u} a) (n t : ℕ) (ω : P.space n) : Vec a :=
  (scale n)⁻¹ • P.Z n t ω

def increment {a : ℕ} (P : ProcessFamily.{u} a) (n t : ℕ) (ω : P.space n) : Vec a :=
  P.Z n (t + 1) ω - P.Z n t ω

/-- Conditional expectation with respect to the given history, not just the count. -/
def meanIncrement {a : ℕ} (P : ProcessFamily.{u} a) (n t : ℕ) : P.space n → Vec a :=
  (P.law n)[increment P n t | P.history n t]

/-- Staying in D through step t is exactly t before the first exit. -/
def beforeExit {a : ℕ} (P : ProcessFamily.{u} a)
    (D : Set (ℝ × Vec a)) (n t : ℕ) (ω : P.space n) : Prop :=
  ∀ k ≤ t, ((k : ℝ) / scale n, normalized P n k ω) ∈ D

/-- Convergence in probability for real observables on changing sample spaces. -/
def tendsInProbability {a : ℕ} (P : ProcessFamily.{u} a)
    (X : (n : ℕ) → P.space n → ℝ) (L : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → Tendsto
    (fun n => ((P.law n) {ω | δ < |X n ω - L|}).toReal) atTop (𝓝 0)

/-- A time-dependent ODE solution in an open domain, on its maximal nonnegative interval.
The boundary is approached from the interior. Uniqueness concerns all other local solutions. -/
def maximalDomainSolution {a : ℕ} (D : Set (ℝ × Vec a))
    (f : ℝ × Vec a → Vec a) (z₀ : Vec a) (S : ℝ) (z : ℝ → Vec a) : Prop :=
  0 < S ∧ z 0 = z₀ ∧ ContinuousOn z (Set.Ico 0 S) ∧
  (∀ t ∈ Set.Ico 0 S, (t, z t) ∈ D ∧
    HasDerivWithinAt z (f (t, z t)) (Set.Ici 0) t) ∧
  (∀ δ : ℝ, 0 < δ → ∃ t ∈ Set.Ico 0 S,
    Metric.infDist (t, z t) (frontier D) < δ) ∧
  (∀ (T : ℝ) (w : ℝ → Vec a), 0 < T → w 0 = z₀ →
    ContinuousOn w (Set.Ico 0 T) →
    (∀ t ∈ Set.Ico 0 T, (t, w t) ∈ D ∧
      HasDerivWithinAt w (f (t, w t)) (Set.Ici 0) t) →
    ∀ t, 0 ≤ t → t < min S T → w t = z t)

/-- The explicit supremum in Theorem 2.1. Inserting 0 handles the finitely many
small n for which Cλ exceeds the initial clearance. The set is bounded by S. -/
def cutoffTime {a : ℕ} (D : Set (ℝ × Vec a)) (S : ℝ) (z : ℝ → Vec a)
    (C lam : ℝ) : ℝ :=
  sSup (insert 0 {τ : ℝ | 0 ≤ τ ∧ τ < S ∧
    ∀ t ∈ Set.Icc 0 τ, C * lam ≤ Metric.infDist (t, z t) (frontier D)})

/-- A bounded open box, with no restriction to positive coordinates. -/
def IsOpenBox {a : ℕ} (D : Set (Vec a)) : Prop :=
  ∃ l r : Vec a, (∀ i, l i < r i) ∧ D = {z | ∀ i, l i < z i ∧ z i < r i}

/-- Conditional count-law closure on a domain. Equality for every Borel event
expresses the conditional distribution without assuming a regular conditional probability. -/
def countLawClosed {a : ℕ} (P : ProcessFamily.{u} a) (D : Set (Vec a)) : Prop :=
  ∀ n, ∃ K : Vec a → Measure (Vec a),
    (∀ x, IsProbabilityMeasure (K x)) ∧
    ∀ t (B : Set (Vec a)), MeasurableSet B →
      ∀ᵐ ω ∂P.law n, normalized P n t ω ∈ D →
        (P.law n)[B.indicator (fun _ => (1 : ℝ)) ∘ increment P n t | P.history n t] ω =
          (K (P.Z n t ω) B).toReal

/-- A run with exactly the prescribed step kernel on a finite graph. -/
def isAlgorithmRun {a : ℕ} (P : ProcessFamily.{u} a) (N : ℕ → ℕ)
    (G : (n : ℕ) → SimpleGraph (Fin (N n)))
    (rule : (n : ℕ) → NeighborRule (Fin (N n)))
    (run : (n : ℕ) → ℕ → P.space n → RunState (Fin (N n))) : Prop :=
  (∀ n, ∀ᵐ ω ∂P.law n, run n 0 ω = (Finset.univ, ∅)) ∧
  (∀ n t S, MeasurableSet[P.history n t] {ω | run n t ω = S}) ∧
  ∀ n t S, ∀ᵐ ω ∂P.law n,
    (P.law n)[(fun ω => if run n (t + 1) ω = S then (1 : ℝ) else 0) |
      P.history n t] ω = ((stepLaw (G n) (rule n) (run n t ω)) S).toReal

end
end FluidGreedyMatching.CliqueBomb


