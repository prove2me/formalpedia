-- Prove2me | Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Approximation
-- name    : QuantumFunctionalEstimation_Master_Supplement_Approximation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:55:30.67523+00:00
-- url     : https://prove2.me/theorems/4ed5ffff-4ec8-4b60-bca8-93a9444f6af1
-- title:
--   Uniform approximation witnesses and supported moment laws
-- statement:
--   For a continuous real function $f$ on a nonempty compact interval $[a,b]$, define its best degree-$K$ uniform polynomial approximation error by
--   $$E_K(f,[a,b])=\inf_{\deg P\le K}\sup_{x\in[a,b]}|f(x)-P(x)|.$$
--   The error is represented in $[0,+\infty]$ so that empty or unbounded sets never acquire a spurious real value zero. On the intervals used in the statements it is finite and equals the displayed classical error. Logarithmic, power and trace witnesses record exactly the approximation inequalities in Lemmas 5.1, 5.4 and 5.12, with their positivity and uniformity conditions. The logarithmic cutoff constant may be shrunk to at most $1/4$. Write $\Delta_\alpha=2c_\alpha\gamma_\alpha^\alpha$ for the power witness gap.
--
--   A supported moment pair consists of arbitrary Borel probability laws on the real line, equality and integrability of integer moments from zero through $K$, almost-sure support in the stated set, and the prescribed common mean. Expectations are actual integrals, and $\pi_b$ is the probability of the positive half-line. These definitions supply the common vocabulary for all eight supporting lemmas; none assumes its desired moment separation.
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), printed pp. 12–13, 20, 22, 30 (PDF pp. 14–15, 22, 24, 32), Definition 2.1, Lemmas 2.2, 5.1, 5.4, 5.12

import Definitions.Def_QuantumFunctionalEstimation_Master_Model
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace QuantumFunctionalEstimation.Master.Supplement

/-- Least uniform error, in extended nonnegative reals: no empty/unbounded real-sup default.
On the compact intervals and continuous functions used here this is the usual finite error. -/
def bestError (K : ℕ) (f : ℝ → ℝ) (a b : ℝ) : ℝ≥0∞ :=
  ⨅ P : {P : Polynomial ℝ // P.natDegree ≤ K},
    ⨆ x : Set.Icc a b, ENNReal.ofReal |f x.val - P.val.eval x.val|

def LogWitness (c₀ cLog : ℝ) : Prop :=
  0 < c₀ ∧ c₀ ≤ 1 / 4 ∧ 0 < cLog ∧ ∀ K : ℕ, 2 ≤ K →
    ENNReal.ofReal cLog ≤ bestError K (fun x => Real.log (1 / x)) (c₀ / (K : ℝ)^2) 1

def PowerWitness (α c γ : ℝ) : Prop :=
  0 < c ∧ 0 < γ ∧ γ ≤ 1 / 8 ∧ ∀ K : ℕ, 2 ≤ K →
    ENNReal.ofReal (c * (γ / (K : ℝ)^2) ^ (α - 1)) ≤
      bestError K (fun x => x ^ (α - 1)) (γ / (K : ℝ)^2) 1

def TraceWitness (d₀ c₀ c₁ : ℝ) : Prop :=
  1 < d₀ ∧ 0 < c₀ ∧ c₀ < 1 ∧ 0 < c₁ ∧ c₁ < 1 ∧
  ∀ K : ℕ, 2 ≤ K → ∀ a : ℝ, 0 < a → a ≤ 1 / 2 →
    (ENNReal.ofReal (if (K : ℝ)⁻¹ ^ 2 ≤ a then c₀ / ((K : ℝ) * Real.sqrt a) else c₁) ≤
      bestError K (fun x => (|x - a| - a) / x) (a / d₀) 1)

def powerGap (α c γ : ℝ) : ℝ := 2 * c * γ ^ α

def mean (μ : ProbabilityMeasure ℝ) : ℝ := ∫ x, x ∂(μ : Measure ℝ)

def expectation (f : ℝ → ℝ) (μ : ProbabilityMeasure ℝ) : ℝ :=
  ∫ x, f x ∂(μ : Measure ℝ)

/-- The two laws have the specified common mean, matching moments and a.s. support. -/
def MatchingOn (K : ℕ) (s : Set ℝ) (a : ℝ) (μ₀ μ₁ : ProbabilityMeasure ℝ) : Prop :=
  MomentMatching K μ₀ μ₁ ∧ Supported μ₀ s ∧ Supported μ₁ s ∧ mean μ₀ = a ∧ mean μ₁ = a

def positiveMass (μ : ProbabilityMeasure ℝ) : ℝ := (μ : Measure ℝ).real (Set.Ioi 0)

end QuantumFunctionalEstimation.Master.Supplement


