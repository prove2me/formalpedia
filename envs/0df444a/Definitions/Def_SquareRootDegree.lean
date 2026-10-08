-- Prove2me | Definitions.Def_SquareRootDegree
-- name    : SquareRootDegree
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:25.751453+00:00
-- url     : https://prove2.me/theorems/97b636ee-f203-4864-bd53-095443ebc4c4
-- statement:
--   This block works with Boolean-cube functions in the real Fourier basis, where a Bool encodes a sign (false is +1, true is -1), averages are uniform, and degree means ordinary real Fourier degree rather than F₂ degree or threshold degree. Cube(ι) is the set of functions ι → Bool, sign(b) is -1 for true and +1 for false, and average(f) is the uniform mean of a real function on a finite type. For a finite set s of coordinates, character(s,x) is the product of sign(x_i) over i in s, fourierCoeff(f,s) is the average of f(x)·character(s,x), and fourierDegree(f) is the largest cardinality of a set s with nonzero Fourier coefficient (zero if all vanish). IsBoolean(f) means every value of f is -1 or 1, and Nonconstant(f) means f takes two different values. singletonSum(f) is the sum over coordinates i of the degree-one coefficients fourierCoeff(f,{i}), while absoluteSingletonSum(f) is the sum of their absolute values. SignedViolations is a defined proposition, not an established theorem: for every real C>0 there exist n>0 and a nonconstant Boolean-valued f on Cube(Fin n) with C·√(fourierDegree f) < singletonSum f, i.e. no constant C bounds the signed singleton sum by √degree. AbsoluteRatios is the set of real numbers r of the form absoluteSingletonSum(f)/√(fourierDegree f), over all n>0 and all Boolean-valued f on Cube(Fin n) with positive Fourier degree.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SquareRootDegree.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SquareRootDegree.lean; bytes 16..1677
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-!
Bool encodes a sign: false is +1 and true is -1. The average is uniform,
and degree is ordinary real Fourier degree, not F₂ degree or threshold degree.
-/

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

abbrev Cube (ι : Type*) := ι → Bool

def sign (b : Bool) : ℝ := if b then -1 else 1

def average {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x, f x

def character {ι : Type*} (s : Finset ι) (x : Cube ι) : ℝ :=
  ∏ i ∈ s, sign (x i)

def fourierCoeff {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) (s : Finset ι) : ℝ := by
  classical
  exact average (fun x => f x * character s x)

def fourierDegree {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun s : Finset ι => fourierCoeff f s ≠ 0)).sup Finset.card

def IsBoolean {α : Type*} (f : α → ℝ) : Prop :=
  ∀ x, f x = -1 ∨ f x = 1

def Nonconstant {α : Type*} (f : α → ℝ) : Prop :=
  ∃ x y, f x ≠ f y

def singletonSum {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) : ℝ :=
  ∑ i, fourierCoeff f {i}

def absoluteSingletonSum {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) : ℝ :=
  ∑ i, |fourierCoeff f {i}|

def SignedViolations : Prop :=
  ∀ C : ℝ, 0 < C → ∃ n : ℕ, 0 < n ∧ ∃ f : Cube (Fin n) → ℝ,
    IsBoolean f ∧ Nonconstant f ∧ C * Real.sqrt (fourierDegree f) < singletonSum f

def AbsoluteRatios : Set ℝ :=
  {r | ∃ n : ℕ, 0 < n ∧ ∃ f : Cube (Fin n) → ℝ,
    IsBoolean f ∧ 0 < fourierDegree f ∧
      r = absoluteSingletonSum f / Real.sqrt (fourierDegree f)}



end SquareRootDegree
end
end OAI


