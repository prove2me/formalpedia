-- Prove2me | Definitions.Def_CriticalSK
-- name    : CriticalSK
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:06.206456+00:00
-- url     : https://prove2.me/theorems/2288d7f9-75b8-4627-9a53-9dbeab90c45f
-- statement:
--   For a nonnegative integer n, a spin configuration assigns a value σᵢ ∈ {−1,1} to each of n sites, and disorder assigns a real coupling Wᵢⱼ to each pair i<j. The Hamiltonian is H_W(σ)=∑ᵢ<ⱼ Wᵢⱼσᵢσⱼ, the partition function is Z_W=∑σ exp(H_W(σ)), and the Gibbs weight is π_W(σ)=exp(H_W(σ))/Z_W. The disorder law makes the couplings independent centered Gaussians of variance 1/n. The single-site heat-bath kernel Kᵢ keeps every other spin fixed and resamples site i according to the Gibbs weights normalized over configurations with those fixed spins. The discrete kernel is P=(1/n)∑ᵢKᵢ, while the continuous generator is L=∑ᵢ(Kᵢ−I) and the continuous kernel is exp(tL), corresponding to rate-one updates at each site. Distance from equilibrium is defined by ½∑σ|p(σ)−π_W(σ)|; starting from x, the distributions used are the x rows of Pᵏ and exp(tL). The discrete and continuous mixing times are the infima of, respectively, nonnegative integer attempts and nonnegative real times when this distance is at most 1/4 for every initial configuration. Gibbs expectation and variance are defined by finite weighted sums, and the Dirichlet form is D_W(f)=∑ᵢ E_π[(f−Kᵢf)²]. For a real coefficient vector a, the linear observable is ∑ᵢaᵢσᵢ. The covariance matrix consists of the centered Gibbs spin covariances, and its norm is its Euclidean operator norm. The linear Rayleigh quantity is the supremum of Var_π(∑ᵢaᵢσᵢ)/D_W(∑ᵢaᵢσᵢ) over a≠0. Finally, the continuous and discrete good-mass quantities sum the Gibbs weights of initial configurations whose corresponding distance from equilibrium remains strictly greater than 1/4 at the specified time or attempt count.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CriticalSK.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CriticalSK.lean; bytes 16..4171
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-!
# Critical SK equilibrium starts, covariance, and mixing lower bounds

The zero-field model has independent Gaussian edge couplings of variance `1 / n`.
Continuous heat bath updates each site at rate one; a discrete attempt chooses a
site uniformly. Distances and mixing times use total variation threshold `1 / 4`.
-/

noncomputable section

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter

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

def mean {n : ℕ} (W : Disorder n) (f : Spin n → ℝ) : ℝ :=
  ∑ x : Spin n, gibbs W x * f x

def variance {n : ℕ} (W : Disorder n) (f : Spin n → ℝ) : ℝ :=
  mean W (fun x => (f x - mean W f) ^ 2)

def dirichlet {n : ℕ} (W : Disorder n) (f : Spin n → ℝ) : ℝ :=
  ∑ i : Fin n, mean W (fun x => (f x - ∑ y : Spin n, siteKernel W i x y * f y) ^ 2)

def linearObservable {n : ℕ} (a : Fin n → ℝ) (x : Spin n) : ℝ :=
  ∑ i : Fin n, a i * spinValue (x i)

def covariance {n : ℕ} (W : Disorder n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => mean W (fun x =>
    (spinValue (x i) - mean W (fun y => spinValue (y i))) *
    (spinValue (x j) - mean W (fun y => spinValue (y j))))

def covarianceNorm {n : ℕ} (W : Disorder n) : ℝ :=
  ‖(covariance W).toEuclideanLin.toContinuousLinearMap‖

/-- The supremum of variance divided by the rate-one Dirichlet form over nonzero
linear spin observables. -/
def linearRayleigh {n : ℕ} (W : Disorder n) : ℝ :=
  sSup {r : ℝ | ∃ a : Fin n → ℝ, a ≠ 0 ∧
    r = variance W (linearObservable a) / dirichlet W (linearObservable a)}

/-- Gibbs mass of realized initial states still farther than `1 / 4` from equilibrium. -/
def continuousGoodMass {n : ℕ} (W : Disorder n) (t : ℝ) : ℝ :=
  ∑ x : Spin n, if 1 / 4 < continuousDistance W t x then gibbs W x else 0

/-- Gibbs mass of realized initial states still farther than `1 / 4` after `k` attempts. -/
def discreteGoodMass {n : ℕ} (W : Disorder n) (k : ℕ) : ℝ :=
  ∑ x : Spin n, if 1 / 4 < discreteDistance W k x then gibbs W x else 0



end CriticalSK
end
end OAI


