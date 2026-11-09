-- Prove2me | Definitions.Def_WangRenyiEntropy_Noninteger_SamplingExperiment
-- name    : WangRenyiEntropy_Noninteger_SamplingExperiment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:03.046707+00:00
-- url     : https://prove2.me/theorems/cfe8b009-b072-4600-a224-56c4215a2330
-- title:
--   Observation experiments, unrestricted estimators, and sample budgets
-- statement:
--   Let $d$ be an alphabet size. A law $p$ has real coordinates $p_i\ge0$ and $\sum_i p_i=1$. Write
--   $$F_\alpha(p)=\sum_i p_i^\alpha,\qquad H_\alpha(p)=\frac{\log F_\alpha(p)}{1-\alpha}.$$
--   The entropy is the published natural-log definition, including its Shannon branch at order one. The multinomial experiment observes an ordered word of exactly $n$ independent samples. The Poisson experiment observes the pair consisting of its length $N\sim\operatorname{Poi}(n)$ and an iid word of that length. A randomized estimator assigns an arbitrary Borel probability measure on the real output to each observed word. Its success probability integrates its internal randomness and the observation law. Uniform success means probability at least $2/3$ for every unknown $p$, with one estimator chosen before $p$.
--
--   The sample complexities are extended nonnegative infima over attainable budgets, equal to infinity when no budget works. In the Poisson model the budget is the expected sample count. The independent count-vector law and its two independent batches are also defined; their total expected cost is $2n$. The two headline rates are
--   $$A_\alpha(d,\varepsilon)=\frac{d^{\max\{1/\alpha,1\}}}{\varepsilon^{1/\alpha}\log d},\qquad B_\alpha(d,\varepsilon)=\frac{d^{|1-1/\alpha|}}{\varepsilon^2}.$$
--   These definitions specify the statistical problem without assuming any complexity, success, or indistinguishability bound. All observation spaces are countable and discrete, so every output-law assignment is a measurable kernel.
-- source:
--   Qisheng Wang, STOC 2027 submission #447 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/447.pdf, printed 1,3,12 / PDF 3, 5, 14, §§1, 1.2 and 4.1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P23

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section

namespace WangRenyiEntropy.Noninteger

/-- Wang, submission #447, printed pp.1,3 / PDF pp.3,5.
The published finite-law predicate imposes exactly nonnegativity and normalization. -/
abbrev Law (d : ℕ) := {p : Fin d → ℝ //
  QAlgorithms.Papers.Independent.Information100.P56.IsLaw p}

/-- The source's power sum; all uses of fractional orders have positive order. -/
def powerSum {d : ℕ} (α : ℝ) (p : Law d) : ℝ := ∑ i, Real.rpow (p.val i) α

/-- Published natural-log entropy, including its Shannon branch. -/
def entropy {d : ℕ} (α : ℝ) (p : Law d) : ℝ :=
  QAlgorithms.Papers.Independent.Advance50.P23.classicalRenyi α p.val

/-- A known sample size and its ordered observations. The size may be zero. -/
abbrev Word (d n : ℕ) := Fin n → Fin d

/-- The full random-length word, including the observed length. -/
abbrev PoissonWord (d : ℕ) := (n : ℕ) × Word d n

/-- Every probability kernel from a discrete observation to the real estimate.
All maps from the countable discrete observation spaces below are measurable. -/
abbrev Estimator (S : Type) := S → ProbabilityMeasure ℝ

/-- Exactly n iid draws; the product of coordinate probabilities is its word mass. -/
def multinomialLaw {d : ℕ} (n : ℕ) (p : Law d) : Measure (Word d n) :=
  ∑ w : Word d n, ENNReal.ofReal (∏ j, p.val (w j)) • Measure.dirac w

/-- Poisson mean n and, conditionally on length, iid ordered observations.
Real.toNNReal only supplies a default outside the nonnegative mean domain. -/
def poissonWordLaw {d : ℕ} (n : ℝ) (p : Law d) : Measure (PoissonWord d) :=
  Measure.sum fun w : PoissonWord d =>
    ((poissonMeasure (Real.toNNReal n)) {w.1} *
      ENNReal.ofReal (∏ j, p.val (w.2 j))) • Measure.dirac w

/-- Internal estimator randomness is integrated into the success probability. -/
def successProbability {S : Type} [MeasurableSpace S] (μ : Measure S)
    (A : Estimator S) (target ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ w, (A w : Measure ℝ) {z | |z - target| ≤ ε} ∂μ

/-- A single estimator, selected before the unknown law, must succeed on every law. -/
def MultinomialAchievable (α ε : ℝ) (d n : ℕ) : Prop :=
  ∃ A : Estimator (Word d n), ∀ p : Law d,
    (2 / 3 : ℝ≥0∞) ≤ successProbability (multinomialLaw n p) A (entropy α p) ε

/-- The cost is the expected number of draws, not a deterministic cap. -/
def PoissonAchievable (α ε : ℝ) (d : ℕ) (n : ℝ) : Prop :=
  0 ≤ n ∧ ∃ A : Estimator (PoissonWord d), ∀ p : Law d,
    (2 / 3 : ℝ≥0∞) ≤ successProbability (poissonWordLaw n p) A (entropy α p) ε

/-- Empty feasible sets have infimum +infinity. -/
def multinomialComplexity (α ε : ℝ) (d : ℕ) : ℝ≥0∞ :=
  sInf {r | ∃ n : ℕ, r = (n : ℝ≥0∞) ∧ MultinomialAchievable α ε d n}

/-- Real, nonnegative expected budgets; empty infimum is +infinity. -/
def poissonComplexity (α ε : ℝ) (d : ℕ) : ℝ≥0∞ :=
  sInf {r | ∃ n : ℝ, r = ENNReal.ofReal n ∧ PoissonAchievable α ε d n}

/-- Count every symbol of the actual random-length word. -/
def wordCounts {d : ℕ} (w : PoissonWord d) : Fin d → ℕ :=
  fun i => (Finset.univ.filter (fun j => w.2 j = i)).card

/-- Independent Poisson coordinates, with their full unbounded natural ranges. -/
def countLaw {d : ℕ} (n : ℝ) (p : Law d) : Measure (Fin d → ℕ) :=
  Measure.pi fun i => poissonMeasure (Real.toNNReal (n * p.val i))

/-- Two independent batches, each with expected cost n (total expected cost 2n). -/
def twoBatchLaw {d : ℕ} (n : ℝ) (p : Law d) :
    Measure ((Fin d → ℕ) × (Fin d → ℕ)) := (countLaw n p).prod (countLaw n p)

/-- The nonparametric and parametric terms of Theorem 1.1. -/
def rateA (α : ℝ) (d : ℕ) (ε : ℝ) : ℝ :=
  Real.rpow d (max (1 / α) 1) / (Real.rpow ε (1 / α) * Real.log d)

def rateB (α : ℝ) (d : ℕ) (ε : ℝ) : ℝ :=
  Real.rpow d |1 - 1 / α| / ε ^ 2

/-- Positive orders outside the natural-number integers. -/
def NonintegerOrder (α : ℝ) : Prop := 0 < α ∧ ∀ k : ℕ, α ≠ (k : ℝ)

end WangRenyiEntropy.Noninteger


