-- Prove2me | Definitions.Def_StandardMapEntropy
-- name    : StandardMapEntropy
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:26.172955+00:00
-- url     : https://prove2.me/theorems/3bd4f641-8cee-4375-a3ea-cc792addd5db
-- statement:
--   The circle is ℝ/ℤ (AddCircle 1) and the torus is the product of two circles. The function sine sends x on the circle to sin(2πx), which is well defined because it is 1-periodic. For a real parameter k, standardMap(k) sends (x,y) on the torus to (x+y+k·sin(2πx), y+k·sin(2πx)), with coordinates taken mod 1. The measure area is the product of the volume measure on the circle with itself. A FinitePartition with parameter r is a measurable map from the torus to Fin(r+1), i.e. a labelling by r+1 symbols. For a self-map f of the torus, a partition p, a length n and a word w of n symbols, blockAtom is the set of points z with p(f^i(z)) = w(i) for every i<n. blockEntropy of μ, f, p, n is −Σ over all words w of μ(atom)·log μ(atom), using real parts of the measures of the atoms. partitionEntropy is the infimum over n≥0 of ofReal(blockEntropy for length n+1 divided by n+1), an extended nonnegative real. metricEntropy of μ and f is the supremum of partitionEntropy over all r and all finite partitions of this kind. MainObligation is a defined proposition, not an established theorem. It says that there exists k₀>0 such that for every real k≥k₀, the metric entropy of the standard map with parameter k with respect to area is strictly positive.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/StandardMapEntropy.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/StandardMapEntropy.lean; bytes 16..1707
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StandardMapEntropy

abbrev Circle := AddCircle (1 : ℝ)
abbrev Torus := Circle × Circle

lemma sine_periodic : Function.Periodic (fun x : ℝ => Real.sin (2 * Real.pi * x)) 1 := by
  intro x
  dsimp only
  rw [show 2 * Real.pi * (x + 1) = 2 * Real.pi * x + 2 * Real.pi by ring]
  exact Real.sin_add_two_pi _

noncomputable def sine (x : Circle) : ℝ := sine_periodic.lift x

noncomputable def standardMap (k : ℝ) (z : Torus) : Torus :=
  (z.1 + z.2 + (k * sine z.1 : ℝ), z.2 + (k * sine z.1 : ℝ))

noncomputable def area : Measure Torus :=
  (volume : Measure Circle).prod (volume : Measure Circle)

def FinitePartition (r : ℕ) := { p : Torus → Fin (r + 1) // Measurable p }

def blockAtom {r : ℕ} (f : Torus → Torus) (p : FinitePartition r)
    (n : ℕ) (w : Fin n → Fin (r + 1)) : Set Torus :=
  { z | ∀ i : Fin n, p.val (f^[i.val] z) = w i }

noncomputable def blockEntropy {r : ℕ} (μ : Measure Torus) (f : Torus → Torus)
    (p : FinitePartition r) (n : ℕ) : ℝ :=
  - ∑ w : Fin n → Fin (r + 1),
    (μ (blockAtom f p n w)).toReal * Real.log (μ (blockAtom f p n w)).toReal

noncomputable def partitionEntropy {r : ℕ} (μ : Measure Torus) (f : Torus → Torus)
    (p : FinitePartition r) : ℝ≥0∞ :=
  ⨅ n : ℕ, ENNReal.ofReal (blockEntropy μ f p (n + 1) / (n + 1 : ℝ))

noncomputable def metricEntropy (μ : Measure Torus) (f : Torus → Torus) : ℝ≥0∞ :=
  ⨆ r : ℕ, ⨆ p : FinitePartition r, partitionEntropy μ f p

def MainObligation : Prop :=
  ∃ k₀ : ℝ, 0 < k₀ ∧ ∀ k : ℝ, k₀ ≤ k → 0 < metricEntropy area (standardMap k)



end StandardMapEntropy
end OAI


