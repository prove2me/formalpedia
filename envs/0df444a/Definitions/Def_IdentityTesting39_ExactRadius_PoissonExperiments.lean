-- Prove2me | Definitions.Def_IdentityTesting39_ExactRadius_PoissonExperiments
-- name    : IdentityTesting39_ExactRadius_PoissonExperiments
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:54.589662+00:00
-- url     : https://prove2.me/theorems/49d0b0d5-7901-4286-b45b-544888b736f4
-- title:
--   Poisson experiments, priors, gradients and the three-statistic rejection rule
-- statement:
--   For a finite label set, the Poisson experiment at intensity $n$ has independent counts $X_i\sim\operatorname{Poi}(np_i)$. Mixtures are defined by integrating the singleton probabilities against the prior and summing the resulting weighted Dirac measures on the countable count space. This construction does not use the default value of a nonmeasurable bind kernel.
--
--   On $\mathbb N$, the extended nonnegative sum $1+\chi^2(P,Q)=\sum_m P\{m\}^2/Q\{m\}$ retains infinite divergence. A normalized prior is a probability measure almost surely on the probability simplex. Its far mass is its probability of $\operatorname{TV}(p,q)>\varepsilon$.
--
--   The gradient vectors are exactly those in (5), with both derivatives equal to one at a zero reference coordinate and the collision derivative zero off the quadratic coordinates. A separating optimizer records moment feasibility, attained optimality, the active-cost multiplier and its separating inequality. The three statistics are
--
--   $$L=\sum_i a_i(X_i-nq_i),\quad Q=\sum_i b_i((X_i-nq_i)^2-X_i),\quad V=\sum_i a_i^2X_i.$$
--
--   The rejection event is $L>J/2$ or $Q>J/2$ or $V>AJ$. A strict branch is defined by existence of a deterministic strict alternative; this implements the branch-omission rule exactly.
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.5, §4, displays (5)–(7) and statistics L,Q,V; mixtures: §5, (9)–(11), pp.6–7; priors: §§6,9–10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Definitions.Def_IdentityTesting39_ExactRadius_MomentPrograms
import Definitions.Def_TotalVariationDist

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IdentityTesting39.ExactRadius

/-- Finite independent Poisson counts, including rate zero. Only n,p≥0 are used. -/
def poissonExperiment {ι : Type} [Fintype ι] (n : ℝ) (p : ι → ℝ) : Measure (ι → ℕ) :=
  Measure.pi (fun i => poissonMeasure (Real.toNNReal (n*p i)))

/-- A discrete mixture is specified by its singleton masses. This avoids Measure.bind's
nonmeasurable-kernel default; the integrands are the actual Poisson probabilities. -/
def poissonMixture {ι : Type} [Fintype ι] (n : ℝ) (π : Measure (ι → ℝ)) : Measure (ι → ℕ) :=
  Measure.sum (fun x => (∫⁻ p, ∏ i,
    poissonMeasure (Real.toNNReal (n*p i)) {x i} ∂π) • Measure.dirac x)

def scalarPoissonMixture (n : ℝ) (μ : Measure ℝ) : Measure ℕ :=
  Measure.sum (fun m => (∫⁻ u, poissonMeasure (Real.toNNReal (n*u)) {m} ∂μ) •
    Measure.dirac m)

/-- Nonnegative extended sums retain infinity; no real tsum default is used. -/
def onePlusChiSquare (P Q : Measure ℕ) : ℝ≥0∞ := ∑' m : ℕ, (P {m})^2 / Q {m}
def chiSquare (P Q : Measure ℕ) : ℝ≥0∞ := onePlusChiSquare P Q - 1

def NormalizedPrior {ι : Type} [Fintype ι] (π : Measure (ι → ℝ)) : Prop :=
  IsProbabilityMeasure π ∧ ∀ᵐ p ∂π, ProbabilityVector p

def farMass {ι : Type} [Fintype ι] (q : ι → ℝ) (ε : ℝ)
    (π : Measure (ι → ℝ)) : ℝ≥0∞ := π {p | ε < FoundationsRL.GeneralDM.totalVariationDiscrete p q}

/-- These derivatives are defined explicitly at q=0, as on printed p.5. -/
def meanGradient (q r : ℝ) : ℝ := if q = 0 then 1 else 1-4*q^2/(r+q)^2
def quadraticGradient (q w : ℝ) : ℝ :=
  if q = 0 then 1 else w*(2*q^2+w)/(q^2+w)^2

def aVector {ι : Type} (q : ι → ℝ) (x : MomentFamily ι) : ι → ℝ :=
  fun i => meanGradient (q i) (x i 0)
def bVector {ι : Type} [Fintype ι] [DecidableEq ι] (q : ι → ℝ)
    (B : Branch ι) (x : MomentFamily ι) : ι → ℝ := by
  classical
  exact fun i => if i ∈ quadraticCoords B then quadraticGradient (q i) (x i 1) else 0

/-- An optimizer and a max-subgradient multiplier, not an assumed statistical test or prior. -/
def SeparatingOptimizer {ι : Type} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (ε n : ℝ) (B : Branch ι) (x : MomentFamily ι) (θ : ℝ) : Prop :=
  x ∈ feasibleMoments q ε B ∧ objective q B n x = programValue q ε n B ∧
  θ ∈ Set.Icc 0 1 ∧
  (n*meanCost q x ≠ programValue q ε n B → θ = 0) ∧
  (n^2*quadraticCost q B x ≠ programValue q ε n B → θ = 1) ∧
  ∀ y ∈ feasibleMoments q ε B,
    0 ≤ θ*n*(∑ i, aVector q x i*(y i 0-x i 0)) +
      (1-θ)*n^2*(∑ i, bVector q B x i*(y i 1-x i 1))

def linearStatistic {ι : Type} [Fintype ι] (q a : ι → ℝ) (n : ℝ) (X : ι → ℕ) : ℝ :=
  ∑ i, a i*((X i : ℝ)-n*q i)
def quadraticStatistic {ι : Type} [Fintype ι] (q b : ι → ℝ) (n : ℝ) (X : ι → ℕ) : ℝ :=
  ∑ i, b i*(((X i : ℝ)-n*q i)^2-X i)
def varianceStatistic {ι : Type} [Fintype ι] (a : ι → ℝ) (X : ι → ℕ) : ℝ :=
  ∑ i, (a i)^2*X i

def rejectEvent {ι : Type} [Fintype ι] (q a b : ι → ℝ) (n J A : ℝ) : Set (ι → ℕ) :=
  {X | J/2 < linearStatistic q a n X ∨ J/2 < quadraticStatistic q b n X ∨
    A*J < varianceStatistic a X}

/-- Branches that contain a strict deterministic alternative; this implements the exact
omission rule without a minimum on an empty tail. -/
def StrictBranch {ι : Type} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (ε : ℝ) (B : Branch ι) : Prop :=
  ∃ p, ProbabilityVector p ∧
    (match B with
    | .all => ε < FoundationsRL.GeneralDM.totalVariationDiscrete p q
    | .excess _ => ε < ∑ i ∈ quadraticCoords B, max (p i-q i) 0
    | .deficit _ => ε < ∑ i ∈ quadraticCoords B, max (q i-p i) 0)

def RelevantBranch {ι : Type} (q : ι → ℝ) (i₀ : ι) (B : Branch ι) : Prop :=
  if q i₀ < 1/8 then B = .all else B = .excess i₀ ∨ B = .deficit i₀

end IdentityTesting39.ExactRadius


