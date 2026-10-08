-- Prove2me | Definitions.Def_SKRatio
-- name    : SKRatio
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:18.059997+00:00
-- url     : https://prove2.me/theorems/50617ce3-6a17-478d-89b0-b6868d609c9f
-- statement:
--   For n spins, a configuration Spin(n) is a function from Fin n to Bool, with spinValue sending true to +1 and false to −1, and an Edge is a pair of sites i<j. A Disorder g assigns a real coupling to each edge, and coupling(g,i,j) is the symmetric extension of g to ordered pairs, equal to zero when i=j. Given disorder g and external field h, the Hamiltonian of a configuration x is (1/2)Σ_i Σ_j σ_i J_ij σ_j + Σ_i h_i σ_i, where σ_i=spinValue(x i) and J_ij=coupling(g,i,j); its weight is exp of the Hamiltonian, the partition function is the sum of weights over all configurations, and mass(g,h,x) is weight divided by partition, a Gibbs probability on configurations. disorderLaw(β,n) is the product measure over edges of centered Gaussians, each with variance β²/n (taken as a nonnegative real via toNNReal). The map flip(i,x) reverses spin i. For zero field, siteKernel(g,i) is the heat-bath Markov matrix that, from x, stays at x with probability mass(x)/(mass(x)+mass(flip i x)) and moves to flip(i,x) with probability mass(flip i x)/(mass(x)+mass(flip i x)). The transition matrix is the identity when n=0, and otherwise the average over sites i of siteKernel(g,i), so a uniformly random site is updated at each step. totalVariation(p,q) is half the sum of absolute differences of two functions on a finite type. discreteDistance(g,k) is the maximum over starting configurations x of the total variation distance between row x of the k-th power of the transition matrix and the zero-field mass of g. mixingTime(g,ε) is the infimum of the natural numbers k with discreteDistance(g,k) ≤ ε, which by the Lean convention for the infimum of an empty set equals 0 if no such k exists.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKRatio.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SKRatio.lean; bytes 16..2077
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

namespace SKRatio

abbrev Spin (n : ℕ) := Fin n → Bool
abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Disorder (n : ℕ) := Edge n → ℝ

def spinValue (b : Bool) : ℝ := if b then 1 else -1

def coupling {n : ℕ} (g : Disorder n) (i j : Fin n) : ℝ :=
  if h : i < j then g ⟨(i, j), h⟩ else
    if h : j < i then g ⟨(j, i), h⟩ else 0

def hamiltonian {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, spinValue (x i) * coupling g i j * spinValue (x j) +
    ∑ i, h i * spinValue (x i)

def weight {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) : ℝ :=
  Real.exp (hamiltonian g h x)

def partition {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) : ℝ :=
  ∑ x, weight g h x

def mass {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) : ℝ :=
  weight g h x / partition g h

def flip {n : ℕ} (i : Fin n) (x : Spin n) : Spin n :=
  Function.update x i (!(x i))

def disorderLaw (β : ℝ) (n : ℕ) : Measure (Disorder n) :=
  Measure.pi (fun _ : Edge n => gaussianReal 0 (Real.toNNReal (β ^ 2 / n)))

def siteKernel {n : ℕ} (g : Disorder n) (i : Fin n) :
    Matrix (Spin n) (Spin n) ℝ := fun x y =>
  (if y = x then mass g 0 x / (mass g 0 x + mass g 0 (flip i x)) else 0) +
  (if y = flip i x then
    mass g 0 (flip i x) / (mass g 0 x + mass g 0 (flip i x)) else 0)

def transition {n : ℕ} (g : Disorder n) : Matrix (Spin n) (Spin n) ℝ :=
  if n = 0 then 1 else fun x y => (∑ i, siteKernel g i x y) / (n : ℝ)

def totalVariation {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ y, |p y - q y|

def discreteDistance {n : ℕ} (g : Disorder n) (k : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun x : Spin n => totalVariation ((transition g ^ k) x) (mass g 0))

def mixingTime {n : ℕ} (g : Disorder n) (ε : ℝ) : ℕ :=
  sInf {k : ℕ | discreteDistance g k ≤ ε}



end SKRatio
end
end OAI


