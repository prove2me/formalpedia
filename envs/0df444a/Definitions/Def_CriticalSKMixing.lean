-- Prove2me | Definitions.Def_CriticalSKMixing
-- name    : CriticalSKMixing
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:06.275127+00:00
-- url     : https://prove2.me/theorems/2de54ab7-d9d4-4710-85dd-9654968bc365
-- statement:
--   For a natural number n, a spin configuration assigns a Boolean to each of n sites, interpreted as a sign σᵢ∈{−1,1}; edges are pairs i<j, and a disorder W assigns a real weight to each edge. The Hamiltonian is H_W(σ)=∑_{i<j}Wᵢⱼσᵢσⱼ, the partition function is Z_W=∑_σ exp(H_W(σ)), and the Gibbs weight is π_W(σ)=exp(H_W(σ))/Z_W. The disorder law makes edge weights independent centered Gaussian variables with variance 1/n. Configurations agree except at site i if all their other coordinates coincide. The site-update matrix Kᵢ(x,y) is zero unless x and y agree except at i; otherwise it is π_W(y) divided by the total Gibbs weight of configurations agreeing with x away from i. The discrete transition matrix is P=n⁻¹∑ᵢKᵢ, while the continuous-time generator is Q=∑ᵢ(Kᵢ−I) and its kernel at real time t is exp(tQ). For any real-valued vector p on configurations, its total-variation expression relative to π_W is ½∑_y|p(y)−π_W(y)|. Applying this expression to rows of exp(tQ) and Pᵏ defines distances from equilibrium for each initial configuration. The continuous mixing time is the real infimum of nonnegative times at which every initial configuration has distance at most 1/4; the discrete mixing time is the natural-number infimum of step counts satisfying the same bound. The definitions allow n=0, with reciprocal zero interpreted as zero, so the discrete matrix is then zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CriticalSKMixing.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CriticalSKMixing.lean; bytes 16..2256
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter

noncomputable section
namespace CriticalSK

abbrev Spin (n : ℕ) := Fin n → Bool

abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

abbrev Disorder (n : ℕ) := Edge n → ℝ

def spinValue (b : Bool) : ℝ := if b then 1 else -1

def hamiltonian {n : ℕ} (W : Disorder n) (x : Spin n) : ℝ :=
  ∑ e : Edge n, W e * spinValue (x e.val.1) * spinValue (x e.val.2)

def partition {n : ℕ} (W : Disorder n) : ℝ :=
  ∑ x : Spin n, Real.exp (hamiltonian W x)

def gibbs {n : ℕ} (W : Disorder n) (x : Spin n) : ℝ :=
  Real.exp (hamiltonian W x) / partition W

def disorderLaw (n : ℕ) : Measure (Disorder n) :=
  Measure.pi fun _ : Edge n => gaussianReal 0 (n : ℝ≥0)⁻¹

def sameExcept {n : ℕ} (i : Fin n) (x y : Spin n) : Prop :=
  ∀ j, j ≠ i → y j = x j

instance {n : ℕ} (i : Fin n) (x y : Spin n) : Decidable (sameExcept i x y) :=
  Classical.propDecidable _

def siteKernel {n : ℕ} (W : Disorder n) (i : Fin n) : Matrix (Spin n) (Spin n) ℝ :=
  fun x y => if sameExcept i x y then
    gibbs W y / (∑ z : Spin n, if sameExcept i x z then gibbs W z else 0)
  else 0

def discreteKernel {n : ℕ} (W : Disorder n) : Matrix (Spin n) (Spin n) ℝ :=
  (n : ℝ)⁻¹ • ∑ i : Fin n, siteKernel W i

def generator {n : ℕ} (W : Disorder n) : Matrix (Spin n) (Spin n) ℝ :=
  ∑ i : Fin n, (siteKernel W i - 1)

def continuousKernel {n : ℕ} (W : Disorder n) (t : ℝ) :
    Matrix (Spin n) (Spin n) ℝ :=
  NormedSpace.exp (t • generator W)

def totalVariation {n : ℕ} (W : Disorder n) (p : Spin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ y : Spin n, |p y - gibbs W y|

def continuousDistance {n : ℕ} (W : Disorder n) (t : ℝ) (x : Spin n) : ℝ :=
  totalVariation W (continuousKernel W t x)

def discreteDistance {n : ℕ} (W : Disorder n) (k : ℕ) (x : Spin n) : ℝ :=
  totalVariation W ((discreteKernel W ^ k) x)

def continuousMixingTime {n : ℕ} (W : Disorder n) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ∀ x, continuousDistance W t x ≤ 1 / 4}

def discreteMixingTime {n : ℕ} (W : Disorder n) : ℕ :=
  sInf {k : ℕ | ∀ x, discreteDistance W k x ≤ 1 / 4}



end CriticalSK
end
end OAI


