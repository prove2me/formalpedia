-- Prove2me | Definitions.Def_UniformSparsestCut
-- name    : UniformSparsestCut
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:36.316983+00:00
-- url     : https://prove2.me/theorems/73a1e9c7-f56c-4a3b-8417-83296944c8c7
-- statement:
--   For n points, a Capacity is a symmetric matrix cap of nonnegative real entries indexed by Fin n with zero diagonal, i.e. cap(i,j)=cap(j,i)≥0 and cap(i,i)=0. pairSum(f) adds f(i,j) over all pairs with i<j, so each unordered pair is counted once. For a subset B of the points, cutRatio(C,B) is the total capacity crossing from B to its complement, the sum of cap(i,j) over i in B and j outside B, divided by |B|(n−|B|). OPT(C) is the real infimum of cutRatio(C,B) over all nonempty proper subsets B, the uniform sparsest cut value; it is taken in the reals, so it is 0 if no such subset exists. A function d on pairs is NegativeType if there are vectors x_i in n-dimensional Euclidean space with d(i,j)=‖x_i−x_j‖² for all i,j, and d satisfies the triangle inequality d(i,k)≤d(i,j)+d(j,k) for all i,j,k. d is Feasible if it is NegativeType and pairSum(d)=1. glValue(C) is the infimum, over all feasible d, of pairSum(cap(i,j)·d(i,j)), which is the value of the corresponding squared-distance relaxation with triangle inequalities. The block only defines these objects and does not state any inequality relating OPT and glValue.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/UniformSparsestCut.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/UniformSparsestCut.lean; bytes 16..1196
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace UniformSparsestCut

structure Capacity (n : ℕ) where
  cap : Fin n → Fin n → ℝ
  nonneg : ∀ i j, 0 ≤ cap i j
  symm : ∀ i j, cap i j = cap j i
  diagonal : ∀ i, cap i i = 0

def pairSum {n : ℕ} (f : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j then f i j else 0

noncomputable def cutRatio {n : ℕ} (C : Capacity n) (B : Finset (Fin n)) : ℝ :=
  (∑ i ∈ B, ∑ j ∈ Bᶜ, C.cap i j) /
    ((B.card : ℝ) * ((n : ℝ) - (B.card : ℝ)))

noncomputable def OPT {n : ℕ} (C : Capacity n) : ℝ :=
  sInf {r | ∃ B : Finset (Fin n), B.Nonempty ∧ B ≠ Finset.univ ∧ r = cutRatio C B}

def NegativeType {n : ℕ} (d : Fin n → Fin n → ℝ) : Prop :=
  (∃ x : Fin n → EuclideanSpace ℝ (Fin n), ∀ i j, d i j = ‖x i - x j‖ ^ 2) ∧
  ∀ i j k, d i k ≤ d i j + d j k

def Feasible {n : ℕ} (d : Fin n → Fin n → ℝ) : Prop :=
  NegativeType d ∧ pairSum d = 1

noncomputable def glValue {n : ℕ} (C : Capacity n) : ℝ :=
  sInf {r | ∃ d : Fin n → Fin n → ℝ, Feasible d ∧
    r = pairSum (fun i j => C.cap i j * d i j)}

open Filter



end UniformSparsestCut
end
end OAI


