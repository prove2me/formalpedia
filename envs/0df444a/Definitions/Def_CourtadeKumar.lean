-- Prove2me | Definitions.Def_CourtadeKumar
-- name    : CourtadeKumar
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:05.931966+00:00
-- url     : https://prove2.me/theorems/fa0633e7-7079-4116-9708-61b905d50d9e
-- statement:
--   For each nonnegative integer n, Cube(n) is the set of Boolean vectors of length n, and cubeAverage(g) is 2⁻ⁿ times the sum of g over this cube. The bit-flip kernel Kε(x,y) is the product over coordinates of 1−ε when the coordinates agree and ε when they differ. For a Boolean function f, the joint quantity P(b,y) is the cube average of Kε(x,y) restricted to inputs with f(x)=b; its function and observation marginals are obtained by summing over y and b, respectively. When 0≤ε≤1, these describe a uniform input X, its Boolean value f(X), and the observation Y formed by independently flipping each input bit with probability ε. Using natural logarithms and ℓ=log 2, xlogx(t)=t log t and binaryEntropy(ε)=−[xlogx(ε)+xlogx(1−ε)]/ℓ. Mutual information is the sum of P(b,y) log(P(b,y)/(P(b)P(y))) over pairs with P(b,y)>0, divided by ℓ; other pairs contribute zero. These formulas are defined algebraically for every real ε. A dictator returns one selected input coordinate, and a complement dictator returns its Boolean negation. CourtadeKumarStatement is the defined proposition that for every n≥1, every 0≤ε≤1/2, and every Boolean function f, this mutual information is at most 1−binaryEntropy(ε). DictatorAttainmentStatement asserts that both dictators and complement dictators attain equality for every coordinate throughout the same parameter range. FullStatement is the conjunction of these two propositions; no proof of them is supplied by these definitions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CourtadeKumar.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CourtadeKumar.lean; bytes 16..2098
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

abbrev Cube (n : ℕ) := Fin n → Bool

end LeanBlast.GotsmanLinial

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

abbrev Cube (n : ℕ) := LeanBlast.GotsmanLinial.Cube n

def cubeAverage {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  (∑ x, g x) / (2 : ℝ) ^ n

def ell : ℝ := Real.log 2

def bitFlipKernel {n : ℕ} (ε : ℝ) (x y : Cube n) : ℝ :=
  ∏ i, if x i = y i then 1 - ε else ε

def jointProbability {n : ℕ} (ε : ℝ) (f : Cube n → Bool) (b : Bool) (y : Cube n) : ℝ :=
  cubeAverage (fun x => if f x = b then bitFlipKernel ε x y else 0)

def functionMarginal {n : ℕ} (ε : ℝ) (f : Cube n → Bool) (b : Bool) : ℝ :=
  ∑ y, jointProbability ε f b y

def observationMarginal {n : ℕ} (ε : ℝ) (f : Cube n → Bool) (y : Cube n) : ℝ :=
  ∑ b : Bool, jointProbability ε f b y

def xlogx (t : ℝ) : ℝ := t * Real.log t

def binaryEntropy (ε : ℝ) : ℝ :=
  -(xlogx ε + xlogx (1 - ε)) / ell

def mutualInformation {n : ℕ} (ε : ℝ) (f : Cube n → Bool) : ℝ :=
  (∑ b : Bool, ∑ y : Cube n,
    if 0 < jointProbability ε f b y then
      jointProbability ε f b y *
        Real.log (jointProbability ε f b y /
          (functionMarginal ε f b * observationMarginal ε f y))
    else 0) / ell

def dictator {n : ℕ} (i : Fin n) (x : Cube n) : Bool := x i

def complementDictator {n : ℕ} (i : Fin n) (x : Cube n) : Bool := !(x i)

def CourtadeKumarStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ ε : ℝ, 0 ≤ ε → ε ≤ (1 : ℝ) / 2 →
      ∀ f : Cube n → Bool, mutualInformation ε f ≤ 1 - binaryEntropy ε

def DictatorAttainmentStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ ε : ℝ, 0 ≤ ε → ε ≤ (1 : ℝ) / 2 →
      ∀ i : Fin n,
        mutualInformation ε (dictator i) = 1 - binaryEntropy ε ∧
        mutualInformation ε (complementDictator i) = 1 - binaryEntropy ε

def FullStatement : Prop := CourtadeKumarStatement ∧ DictatorAttainmentStatement



end LeanBlast.CourtadeKumar
end
end OAI


