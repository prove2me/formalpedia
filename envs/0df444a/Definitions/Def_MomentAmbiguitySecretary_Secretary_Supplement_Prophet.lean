-- Prove2me | Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Prophet
-- name    : MomentAmbiguitySecretary_Secretary_Supplement_Prophet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:49:25.810465+00:00
-- url     : https://prove2.me/theorems/185a7afd-ab21-4b5b-afb8-3da593be8159
-- title:
--   Fixed-order moment disclosure experiment and guarantee-based competitive value
-- statement:
--   The experiment is the actual independent product of arbitrary nonnegative all-moment laws in index order. A policy is a general causal randomized single-choice kernel depending measurably on the full moment disclosures. Expected reward is the selected cardinal value, and the benchmark is the expected one-based decreasing order statistic with ties. The value is the supremum of nonnegative guarantee coefficients valid under one policy for every instance, including zero benchmarks.
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied checksum-pinned preprint. Definitions, PDF/printed pp.17–20; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf; SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Laws
import Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Choice

open MeasureTheory Set
open scoped NNReal BigOperators

namespace MomentAmbiguitySecretary.Secretary.Supplement
noncomputable section

abbrev ProphetPolicy (m : ℕ) := CausalChoice (Fin m → Disclosure) m

def prophetExperiment {m : ℕ} (laws : Fin m → Law) : Measure (Fin m → ℝ≥0) :=
  Measure.pi fun i => (laws i).val.toMeasure

def selectedValue {m : ℕ} (π : ProphetPolicy m) (s : Fin m → Disclosure)
    (x : Fin m → ℝ≥0) : ℝ := ∑ i : Fin m, (π.mass i s x : ℝ) * (x i : ℝ)

def expectedReward {m : ℕ} (π : ProphetPolicy m) (laws : Fin m → Law) : ℝ :=
  ∫ x, selectedValue π (fun i => disclose (laws i)) x ∂prophetExperiment laws

/-- r is one-based; ties remain in the sorted list. Out-of-range ranks return 0. -/
def orderStatistic {m : ℕ} (r : ℕ) (x : Fin m → ℝ≥0) : ℝ≥0 :=
  ((List.ofFn x).mergeSort (fun a b => b ≤ a))[r - 1]?.getD 0

def expectedBenchmark {m : ℕ} (r : ℕ) (laws : Fin m → Law) : ℝ :=
  ∫ x, (orderStatistic r x : ℝ) ∂prophetExperiment laws

def achievable (m r : ℕ) : Set ℝ :=
  {α | 0 ≤ α ∧ ∃ π : ProphetPolicy m, ∀ laws : Fin m → Law,
    α * expectedBenchmark r laws ≤ expectedReward π laws}

/-- The guarantee-based supremum, p.17; zero-benchmark inputs impose no ratio. -/
def prophetValue (m r : ℕ) : ℝ := sSup (achievable m r)

end
end MomentAmbiguitySecretary.Secretary.Supplement


