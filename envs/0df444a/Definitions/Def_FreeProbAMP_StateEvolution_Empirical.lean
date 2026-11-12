-- Prove2me | Definitions.Def_FreeProbAMP_StateEvolution_Empirical
-- name    : FreeProbAMP_StateEvolution_Empirical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:23:28.659982+00:00
-- url     : https://prove2.me/theorems/b4cba1e5-108f-45f8-9bbd-96d477a6db39
-- title:
--   Pseudo-Lipschitz functions and all-moment empirical convergence
-- statement:
--   For a vector $x\in\mathbb R^k$, use its Euclidean norm. A function $f$ is pseudo-Lipschitz of integer order $m\ge1$ if there exists $L>0$ such that
--
--   $$|f(x)-f(y)|\le L(1+\|x\|_2^{m-1}+\|y\|_2^{m-1})\|x-y\|_2.$$
--
--   Finite-order regularity for $f$ and its first partial derivatives, convergence in probability, upper limiting tail bounds, and tightness are defined here. Tightness means: for every $\epsilon>0$, some finite $L>0$ and $d_0$ bound the probability of $|X_d|>L$ by $\epsilon$ for all $d\ge d_0$.
--
--   Given probability spaces with measures $\mu,\nu$, an array $X_i^d\in\mathbb R^k$ with $n(d)\to\infty$ converges empirically to an all-moment vector $Y$ if, for every finite-order pseudo-Lipschitz test $\psi$,
--
--   $$\frac1{n(d)}\sum_{i=1}^{n(d)}\psi(X_i^d)\xrightarrow{\mathbb P}\int\psi(Y)\,d\nu.$$
--
--   The test integral must be finite. The initialization predicate uses almost-sure weak convergence and convergence of every absolute integer moment, equivalently the source's convergence in every finite Wasserstein distance. A bounded Borel readout has a discontinuity set of limiting probability zero. These definitions provide the common convergence interface for every vector-side statement.
--
--   **Formalization Note** Coordinate arrays are indexed by $\mathrm{Fin}(k)$, with the Euclidean norm defined explicitly. Differentiability uses the equivalent finite-dimensional product topology. Order zero powers are used for moments, while pseudo-Lipschitz orders start at one.
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), pp. 3–5, (2.1), Assumption 2.2, Definitions 2.6–2.7 and Assumption 2.8

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution

/-- Euclidean norm, even though coordinate arrays carry the product norm in Lean. -/
def euclid {k : ℕ} (x : Fin k → ℝ) : ℝ := Real.sqrt (∑ j, x j ^ 2)

def PseudoLipschitz {k : ℕ} (m : ℕ) (f : (Fin k → ℝ) → ℝ) : Prop :=
  1 ≤ m ∧ ∃ L : ℝ, 0 < L ∧ ∀ x y,
    |f x - f y| ≤ L * (1 + euclid x ^ (m-1) + euclid y ^ (m-1)) * euclid (x-y)

def FinitePL {k : ℕ} (f : (Fin k → ℝ) → ℝ) : Prop := ∃ m, PseudoLipschitz m f

def derivCoord {k : ℕ} (f : (Fin k → ℝ) → ℝ) (r : Fin k) (x : Fin k → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single r 1)

def SmoothPL {k : ℕ} (f : (Fin k → ℝ) → ℝ) : Prop :=
  ContDiff ℝ 1 f ∧ ∃ m, PseudoLipschitz m f ∧ ∀ r, PseudoLipschitz m (derivCoord f r)

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

def InProb (μ : Measure Ω) (X : ℕ → Ω → ℝ) (c : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → Tendsto (fun d => μ {ω | η < |X d ω-c|}) atTop (𝓝 0)

def TailBound (μ : Measure Ω) (X : ℕ → Ω → ℝ) (c : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → Tendsto (fun d => μ {ω | c+η < X d ω}) atTop (𝓝 0)

/-- O_P(1), with the threshold after the error probability and before dimension. -/
def Tight (μ : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, 0 < L ∧ ∃ d₀ : ℕ, ∀ d, d₀ ≤ d →
    μ {ω | L < |X d ω|} ≤ ENNReal.ofReal ε

def avg (n : ℕ) (x : Fin n → ℝ) : ℝ := (∑ i, x i) / n

def AllMoments {k : ℕ} (ν : Measure E) (X : E → Fin k → ℝ) : Prop :=
  Measurable X ∧ ∀ p : ℕ, Integrable (fun ξ => euclid (X ξ) ^ p) ν

/-- Definition 2.6: every finite growth order and integrable test expectation. -/
def Empirical {k : ℕ} (μ : Measure Ω) (ν : Measure E) (n : ℕ → ℕ)
    (X : (d : ℕ) → Ω → Fin (n d) → Fin k → ℝ) (Y : E → Fin k → ℝ) : Prop :=
  Tendsto n atTop atTop ∧ AllMoments ν Y ∧ (∀ d, Measurable (X d)) ∧
  ∀ (m : ℕ) (ψ : (Fin k → ℝ) → ℝ), PseudoLipschitz m ψ →
    Integrable (fun ξ => ψ (Y ξ)) ν ∧
    InProb μ (fun d ω => avg (n d) (fun i => ψ (X d ω i))) (∫ ξ, ψ (Y ξ) ∂ν)

/-- Almost-sure weak convergence plus all absolute moments; Assumption 2.2. -/
def InitialLimit (μ : Measure Ω) (ν : Measure E) (n : ℕ → ℕ)
    (u : (d : ℕ) → Ω → Fin (n d) → ℝ) (U : E → ℝ) : Prop :=
  Measurable U ∧ (∀ d, Measurable (u d)) ∧
  (∀ p : ℕ, Integrable (fun ξ => |U ξ| ^ p) ν) ∧
  ∀ᵐ ω ∂μ,
    (∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      Tendsto (fun d => avg (n d) (fun i => f (u d ω i))) atTop (𝓝 (∫ ξ, f (U ξ) ∂ν))) ∧
    (∀ p : ℕ, Tendsto (fun d => avg (n d) (fun i => |u d ω i| ^ p))
      atTop (𝓝 (∫ ξ, |U ξ| ^ p ∂ν)))

def append {k : ℕ} (x : Fin k → ℝ) (y : ℝ) : Fin (k+1) → ℝ :=
  Fin.snoc x y

def BoundedReadout {k : ℕ} (ν : Measure E) (X : E → Fin k → ℝ)
    (h : (Fin k → ℝ) → ℝ) : Prop :=
  Measurable h ∧ (∃ C : ℝ, ∀ x, |h x| ≤ C) ∧ ν {ξ | ¬ ContinuousAt h (X ξ)} = 0

end FreeProbAMP.StateEvolution


