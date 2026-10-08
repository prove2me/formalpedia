-- Prove2me | Definitions.Def_GotsmanLinial
-- name    : GotsmanLinial
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:13.228978+00:00
-- url     : https://prove2.me/theorems/84fc8258-d917-40bf-b18b-447fc66263d6
-- statement:
--   The cube Cube(n) is the set of Boolean vectors of length n, with cubeCoord sending a vertex x and coordinate i to +1 if x i is true and −1 otherwise, and flip(i,x) toggling the ith bit of x. thresholdSign(t) is 1 when t≥0 and −1 otherwise. For a real-valued function f on the cube, sensitiveVertices(f,i) is the set of vertices x where f(x)≠f(flip(i,x)), and averageSensitivity(f) is the sum over coordinates i of the number of such vertices divided by 2^n. A polynomial p in n real variables is IsMultilinear if every monomial in its support has exponent at most 1 in each variable. polynomialValue(p,x) evaluates p at the ±1 point given by cubeCoord of x, and polynomialThreshold(p) is the ±1-valued function x ↦ thresholdSign(polynomialValue(p,x)). GotsmanLinialStatement is a defined proposition, not an established theorem: for all natural numbers n and d with 1≤d≤n, and every real multilinear polynomial p in n variables with total degree at most d, the average sensitivity of the threshold function of p is at most 8·d·√n.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GotsmanLinial.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GotsmanLinial.lean; bytes 192..1564
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum

namespace OAI

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

abbrev Cube (n : ℕ) := Fin n → Bool

def cubeCoord {n : ℕ} (x : Cube n) (i : Fin n) : ℝ :=
  if x i then 1 else -1

def flip {n : ℕ} (i : Fin n) (x : Cube n) : Cube n :=
  Function.update x i (!(x i))

noncomputable def thresholdSign (t : ℝ) : ℝ :=
  if 0 ≤ t then 1 else -1

noncomputable def sensitiveVertices {n : ℕ} (f : Cube n → ℝ) (i : Fin n) :
    Finset (Cube n) := by
  classical
  exact Finset.univ.filter fun x => f x ≠ f (flip i x)

noncomputable def averageSensitivity {n : ℕ} (f : Cube n → ℝ) : ℝ :=
  ∑ i : Fin n, ((sensitiveVertices f i).card : ℝ) / (2 : ℝ) ^ n

def IsMultilinear {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ m ∈ p.support, ∀ i : Fin n, m i ≤ 1

noncomputable def polynomialValue {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (x : Cube n) : ℝ :=
  MvPolynomial.eval (cubeCoord x) p

noncomputable def polynomialThreshold {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Cube n → ℝ :=
  fun x => thresholdSign (polynomialValue p x)

def GotsmanLinialStatement : Prop :=
  ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d → d ≤ n →
    ∀ p : MvPolynomial (Fin n) ℝ,
      IsMultilinear p → p.totalDegree ≤ d →
        averageSensitivity (polynomialThreshold p) ≤ 8 * (d : ℝ) * Real.sqrt (n : ℝ)



end LeanBlast.GotsmanLinial
end OAI


