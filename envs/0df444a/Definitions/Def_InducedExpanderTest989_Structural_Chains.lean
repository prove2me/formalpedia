-- Prove2me | Definitions.Def_InducedExpanderTest989_Structural_Chains
-- name    : InducedExpanderTest989_Structural_Chains
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:57:23.190352+00:00
-- url     : https://prove2.me/theorems/2c962aec-6e1c-4e40-be1d-06f6c129adfd
-- title:
--   Averaging walks, trace chains and independent collision experiments
-- statement:
--   For a finite stochastic matrix K, a row vector a has total variation norm equal to half its ℓ¹ norm. The averaging kernel, uniform law on a set U, and Dirichlet energy are
--   $$Q_\ell=\ell^{-1}\sum_{j=0}^{\ell-1}K^j,\qquad \pi_U(x)=\mathbf1_{x\in U}/|U|,\qquad \mathcal E_K(f)=\tfrac12\sum_{x,y}\pi(x)K(x,y)(f(x)-f(y))^2.$$
--   Chain conductance minimizes one-step flow out of a set divided by its uniform mass. The infinite trajectory law is the Ionescu–Tulcea measure with transition K and fixed initial state. Visit times take values in the extended natural numbers, retaining infinity if the visit never occurs. Their nonnegative expectations retain infinity as well. The trace matrix on the actual state subtype U is the law of the first positive return to U.
--
--   For probability vectors p,q, independent lists A,D of lengths a,b have product weights. Their collision probability is the sum of these weights over pairs of lists sharing a vertex. Ordered cross-part overlap is the sum of inner products of endpoint rows, divided by n². These objects support both the infinite-horizon trace arguments and the finite collision experiment.
--
--   **Formalization Note** Stochastic means membership in Mathlib's rowStochastic. No irreducibility is bundled. A state space without a nontrivial cut has chain conductance 1; the uniform law on an empty set is zero. A nonstochastic matrix row holds at its starting state in the path-law construction, a default never used under stochastic hypotheses.
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.13 (PDF p.15), §3; Definition 3.1 p.14; §4.2.1 p.16; Definition 4.1 p.25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/989.pdf

import Mathlib
import Definitions.Def_MarkovChain
import Definitions.Def_GibbsCongestion_dirichletForm
import Definitions.Def_InducedExpanderTest989_Structural_Graph

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural

/-- Stochastic matrices use Mathlib's existing submonoid, with no irreducibility. -/
def Stochastic {X : Type} [Fintype X] [DecidableEq X] (K : Matrix X X ℝ) : Prop :=
  K ∈ Matrix.rowStochastic ℝ X

def averaging {X : Type} [Fintype X] [DecidableEq X]
    (K : Matrix X X ℝ) (ℓ : ℕ) : Matrix X X ℝ :=
  fun x y => (∑ j ∈ Finset.range ℓ, (K ^ j) x y) / ℓ

def tvNorm {X : Type} [Fintype X] (a : X → ℝ) : ℝ := MarkovChain.tvDist a 0

def dot {X : Type} [Fintype X] (p q : X → ℝ) : ℝ := ∑ z, p z * q z

def uniformOn {X : Type} [Fintype X] (U : Finset X) : X → ℝ := by
  classical
  exact fun x => if x ∈ U then 1 / (U.card : ℝ) else 0

/-- Uniform stationary conductance, with value 1 when there is no nontrivial cut. -/
def chainConductance {X : Type} [Fintype X] (K : Matrix X X ℝ) : ℝ := by
  classical
  let cuts := (Finset.univ : Finset (Finset X)).filter
    fun S => 0 < S.card ∧ 2 * S.card ≤ Fintype.card X
  exact if cuts.Nonempty then sInf {r : ℝ | ∃ S ∈ cuts,
    r = (∑ x ∈ S, ∑ y ∈ Sᶜ, K x y) / S.card} else 1

def energy {X : Type} [Fintype X] (K : Matrix X X ℝ) (f : X → ℝ) : ℝ :=
  GibbsCongestion.dirichletForm K (MarkovChain.unif X) f f

def weightedSq {X : Type} [Fintype X] (f : X → ℝ) : ℝ :=
  ∑ x, MarkovChain.unif X x * (f x)^2

/-- A real probability vector is converted without normalization; invalid rows hold. -/
def rowPMF {X : Type} [Fintype X] (K : Matrix X X ℝ) (x : X) : PMF X := by
  classical
  exact if h : (∀ y, 0 ≤ K x y) ∧ ∑ y, K x y = 1 then
    PMF.ofFintype (fun y => ENNReal.ofReal (K x y)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => h.1 y), h.2]
      norm_num)
  else PMF.pure x

/-- Natural path σ-algebra, from discrete finite states. -/
abbrev Path (X : Type) := ℕ → X

/-- Infinite-horizon Ionescu–Tulcea law, started at x (not a horizon surrogate). -/
def pathLaw {X : Type} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (K : Matrix X X ℝ) (x : X) : MeasureTheory.Measure (Path X) := by
  classical
  let step : ProbabilityTheory.Kernel X X :=
    ⟨fun z => (rowPMF K z).toMeasure, measurable_of_countable _⟩
  letI : ProbabilityTheory.IsMarkovKernel step := ⟨fun z => by change MeasureTheory.IsProbabilityMeasure (rowPMF K z).toMeasure; infer_instance⟩
  let κ := fun t : ℕ => step.comap (fun h : Finset.Iic t → X => h ⟨t, by simp⟩) (measurable_pi_apply _)
  exact ProbabilityTheory.Kernel.trajMeasure (MeasureTheory.Measure.dirac x) κ

/-- ∞ on a trajectory which never hits U at or after a. -/
def firstVisit {X : Type} (U : Finset X) (a : ℕ∞) (w : Path X) : ℕ∞ :=
  sInf {t : ℕ∞ | ∃ s : ℕ, t = s ∧ a ≤ t ∧ w s ∈ U}

def traceTime {X : Type} (U : Finset X) (w : Path X) : ℕ → ℕ∞
  | 0 => 0
  | i+1 => firstVisit U (traceTime U w i + 1) w

def elapsedMean {X : Type} [MeasurableSpace X] (μ : MeasureTheory.Measure (Path X))
    (τ : Path X → ℕ∞) : ℝ≥0∞ := ∫⁻ w, (τ w).toENNReal ∂μ

/-- Equality to a finite stopping value depends only on the observed prefix. -/
def NaturalStopping {X : Type} (τ : Path X → ℕ∞) : Prop :=
  ∀ t : ℕ, ∀ w w' : Path X, (∀ s ≤ t, w s = w' s) → (τ w = t ↔ τ w' = t)

def stoppedLaw {X : Type} [MeasurableSpace X] (μ : MeasureTheory.Measure (Path X))
    (τ : Path X → ℕ∞) (y : X) : ℝ :=
  (∑' t : ℕ, μ {w | τ w = t ∧ w t = y}).toReal

/-- Trace matrix on the actual subtype U, rather than a cylinder on V. -/
def traceMatrix {n : ℕ} (d : ℕ) (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) :
    Matrix U U ℝ := fun x y =>
  stoppedLaw (pathLaw (graphWalk d G) x.val) (fun w => traceTime U w 1) y.val

/-- Product-law probability of m independent samples, no black-box walk primitive. -/
def iidWeight {X : Type} (p : X → ℝ) (m : ℕ) (a : Fin m → X) : ℝ :=
  ∏ i, p (a i)

def collide {X : Type} {a b : ℕ} (A : Fin a → X) (D : Fin b → X) : Prop :=
  ∃ i j, A i = D j

def collisionProb {X : Type} [Fintype X] (p q : X → ℝ) (a b : ℕ) : ℝ := by
  classical
  exact ∑ A : Fin a → X, ∑ D : Fin b → X,
    if collide A D then iidWeight p a A * iidWeight q b D else 0

def crossOverlap {n s : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (C : Fin n → Fin s) : ℝ := by
  classical
  exact (∑ x, ∑ y, if C x ≠ C y then dot (Q x) (Q y) else 0) / (n : ℝ)^2

end InducedExpanderTest989.Structural


