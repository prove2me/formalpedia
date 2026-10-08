-- Prove2me | Definitions.Def_SKHighTemperature
-- name    : SKHighTemperature
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:17.811989+00:00
-- url     : https://prove2.me/theorems/498d0a57-a544-44a8-8c41-f2f81e7b1c9b
-- statement:
--   A spin configuration on n sites is a function from Fin n to Bool, with spinValue sending true to +1 and false to −1. A disorder g assigns a real number to each pair i<k, and coupling(g,i,k) is the symmetric extension, equal to zero when i=k. Given g and a field h, the hamiltonian is H(x) = ½ Σᵢ Σₖ σᵢ J_{ik} σₖ + Σᵢ hᵢ σᵢ, where σᵢ is the spin value at site i. The weight is exp(H(x)) with no minus sign or inverse temperature inserted, the partition is the sum of weights over all configurations, mass is weight divided by partition, and expectation and variance are taken under this mass. flip(i,x) reverses the spin at site i, and conditionalExpectation of f at x is the weight-average of f over x and flip(i,x), given all other spins. dirichlet(g,h,f) is the sum over sites i of the expectation of (f − conditionalExpectation_i f)², so each site has a rate-one clock. disorderLaw(β,n) is the product measure over the edges i<k of centered Gaussians with variance β²/n. poincareEvent(n,C) is the set of disorders g, with zero field, such that variance(f) ≤ C·dirichlet(f) for every real function f on configurations. discreteGap(g) is the infimum, over f with positive variance at zero field, of dirichlet(f) divided by n times variance(f). MainStatement(β) is a defined proposition, not an established theorem. It says that there exists a constant C>0 such that, as n tends to infinity, both the disorderLaw(β,n)-probability of poincareEvent(n,C) and the probability of the event 1/(Cn) ≤ discreteGap(g) tend to 1.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKHighTemperature.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SKHighTemperature.lean; bytes 16..2707
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

namespace SKGap

abbrev Spin (n : ℕ) := Fin n → Bool
abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Disorder (n : ℕ) := Edge n → ℝ

def spinValue (b : Bool) : ℝ := if b then 1 else -1

def coupling {n : ℕ} (g : Disorder n) (i k : Fin n) : ℝ :=
  if h : i < k then g ⟨(i, k), h⟩ else
    if h : k < i then g ⟨(k, i), h⟩ else 0

def hamiltonian {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ k, spinValue (x i) * coupling g i k * spinValue (x k) +
    ∑ i, h i * spinValue (x i)

def weight {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) : ℝ :=
  Real.exp (hamiltonian g h x)

def partition {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) : ℝ :=
  ∑ x, weight g h x

def mass {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) : ℝ :=
  weight g h x / partition g h

def expectation {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) : ℝ :=
  ∑ x, mass g h x * f x

def variance {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) : ℝ :=
  expectation g h (fun x => (f x - expectation g h f) ^ 2)

def flip {n : ℕ} (i : Fin n) (x : Spin n) : Spin n :=
  Function.update x i (!(x i))

/-- Conditional expectation under the actual Gibbs law given all other spins. -/
def conditionalExpectation {n : ℕ} (g : Disorder n) (h : Fin n → ℝ)
    (i : Fin n) (f : Spin n → ℝ) (x : Spin n) : ℝ :=
  (weight g h x * f x + weight g h (flip i x) * f (flip i x)) /
    (weight g h x + weight g h (flip i x))

/-- Unscaled form: each site has a rate-one clock. -/
def dirichlet {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) : ℝ :=
  ∑ i, expectation g h (fun x => (f x - conditionalExpectation g h i f x) ^ 2)

def disorderLaw (β : ℝ) (n : ℕ) : Measure (Disorder n) :=
  Measure.pi (fun _ : Edge n => gaussianReal 0 (Real.toNNReal (β ^ 2 / n)))

def poincareEvent (n : ℕ) (C : ℝ) : Set (Disorder n) :=
  {g | ∀ f : Spin n → ℝ, variance g 0 f ≤ C * dirichlet g 0 f}

/-- Rayleigh quotient definition of the uniform-site discrete heat-bath gap. -/
def discreteGap {n : ℕ} (g : Disorder n) : ℝ :=
  sInf {r : ℝ | ∃ f : Spin n → ℝ, 0 < variance g 0 f ∧
    r = dirichlet g 0 f / ((n : ℝ) * variance g 0 f)}

def MainStatement (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    Tendsto (fun n : ℕ => disorderLaw β n (poincareEvent n C)) atTop (nhds 1) ∧
    Tendsto (fun n : ℕ => disorderLaw β n {g | 1 / (C * (n : ℝ)) ≤ discreteGap g})
      atTop (nhds 1)



end SKGap
end
end OAI


