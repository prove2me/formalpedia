-- Prove2me | Definitions.Def_SKBarriers
-- name    : SKBarriers
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:18.478079+00:00
-- url     : https://prove2.me/theorems/f1b2209f-d123-4022-b046-ae30e19bcc7b
-- statement:
--   This block sets up the Sherrington-Kirkpatrick spin glass and its Glauber dynamics. A configuration on n sites is a map from Fin n to Bool, with spin(b)=+1 for true and -1 for false. An edge is a pair (i,j) with i<j, and a disorder is a real number J_e for each edge. The Hamiltonian is H(x)=(1/√n) Σ_{i<j} J_{ij} spin(x_i) spin(x_j), the partition function is Z=Σ_x exp(βH(x)), and the Gibbs weight of x is exp(βH(x))/Z. The coupling of i and j is J_{ij} or J_{ji} according to the order of the indices, and is 0 when i=j. The local field at site i is (1/√n) Σ_j coupling(i,j) spin(x_j). The heat-bath step from x to y has probability (1/n) Σ_i [y differs from x at most at coordinate i] exp(β spin(y_i) h_i(x)) / (2 cosh(β h_i(x))), where h_i(x) is the local field at i in x. In words, a uniformly chosen site is resampled from its conditional Gibbs law given the other spins. The discrete kernel is the k-fold iterate of this step, with the identity at k=0. The continuous-time kernel at time t is Σ_k e^{-nt}(nt)^k/k! times the k-step kernel, a Poisson mixture with rate n. The discrete and continuous distances from a start x are half the l1 distance, that is, the total variation distance, between the kernel started at x (after k steps or time t) and the Gibbs measure. The disorder law makes all edge couplings independent standard Gaussians. With κ=1/10000 the time scale is exp(n^κ). The continuous bad mass at β and n is the disorder expectation of the total Gibbs mass of those starting configurations x whose continuous distance at the time scale exceeds 1/4. The discrete bad mass is defined the same way, using the discrete distance after ⌊exp(n^κ)⌋ steps. Only these definitions are given, with no theorem about the bad masses.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKBarriers.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SKBarriers.lean; bytes 16..2798
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

section

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

namespace SK
abbrev Config (n : ℕ) := Fin n → Bool
abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Disorder (n : ℕ) := Edge n → ℝ

def spin (b : Bool) : ℝ := if b then 1 else -1

def hamiltonian {n : ℕ} (J : Disorder n) (x : Config n) : ℝ :=
  (∑ e : Edge n, J e * spin (x e.val.1) * spin (x e.val.2)) / Real.sqrt n

def partition {n : ℕ} (β : ℝ) (J : Disorder n) : ℝ :=
  ∑ x : Config n, Real.exp (β * hamiltonian J x)

def gibbs {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) : ℝ :=
  Real.exp (β * hamiltonian J x) / partition β J

def coupling {n : ℕ} (J : Disorder n) (i j : Fin n) : ℝ :=
  if h : i < j then J ⟨(i, j), h⟩ else
    if h : j < i then J ⟨(j, i), h⟩ else 0

def localField {n : ℕ} (J : Disorder n) (x : Config n) (i : Fin n) : ℝ :=
  (∑ j : Fin n, coupling J i j * spin (x j)) / Real.sqrt n

def heatBath {n : ℕ} (β : ℝ) (J : Disorder n) (x y : Config n) : ℝ :=
  (∑ i : Fin n, if Function.update x i (y i) = y then
    Real.exp (β * spin (y i) * localField J x i) /
      (2 * Real.cosh (β * localField J x i)) else 0) / n

def discreteKernel {n : ℕ} (β : ℝ) (J : Disorder n) : ℕ → Config n → Config n → ℝ
  | 0, x, y => if x = y then 1 else 0
  | k + 1, x, y => ∑ z : Config n, heatBath β J x z * discreteKernel β J k z y

def continuousKernel {n : ℕ} (β : ℝ) (J : Disorder n) (t : ℝ)
    (x y : Config n) : ℝ :=
  ∑' k : ℕ, (Real.exp (-(n : ℝ) * t) * ((n : ℝ) * t) ^ k /
    (Nat.factorial k : ℝ)) * discreteKernel β J k x y

def discreteDistance {n : ℕ} (β : ℝ) (J : Disorder n)
    (x : Config n) (k : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ y : Config n, |discreteKernel β J k x y - gibbs β J y|

def continuousDistance {n : ℕ} (β : ℝ) (J : Disorder n)
    (x : Config n) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ y : Config n, |continuousKernel β J t x y - gibbs β J y|

def disorderLaw (n : ℕ) : Measure (Disorder n) :=
  Measure.pi (fun _ : Edge n => gaussianReal 0 1)

def kappa : ℝ := 1 / 10000

def timeScale (n : ℕ) : ℝ := Real.exp ((n : ℝ) ^ kappa)

def continuousBadMass (β : ℝ) (n : ℕ) : ℝ :=
  ∫ J : Disorder n, (∑ x : Config n, if 1 / 4 < continuousDistance β J x (timeScale n)
    then gibbs β J x else 0) ∂disorderLaw n

def discreteBadMass (β : ℝ) (n : ℕ) : ℝ :=
  ∫ J : Disorder n, (∑ x : Config n, if 1 / 4 < discreteDistance β J x ⌊timeScale n⌋₊
    then gibbs β J x else 0) ∂disorderLaw n

end SK
end
end
end

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

namespace SK



end SK
end
end OAI


