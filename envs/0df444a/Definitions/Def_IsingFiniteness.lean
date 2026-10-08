-- Prove2me | Definitions.Def_IsingFiniteness
-- name    : IsingFiniteness
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:15.658585+00:00
-- url     : https://prove2.me/theorems/ee9bec4f-43a5-425a-9d64-490ba7a6ceb0
-- statement:
--   For real s and d and a function U, gaussianTransform(s,d,U)(x) is the Gaussian smoothing of U at x with variance s: if d=0 it is the expectation E[U(x+√s Z)] for a standard normal Z, and otherwise it is the soft-max (1/d)·log E[exp(d·U(x+√s Z))]. A Partition is a positive number k of levels with strictly increasing cut points 0=c₀<c₁<…<c_k=1. A FieldStep is a partition together with nonnegative, nondecreasing values v₀≤…≤v_{k-1}; stepAt(h,i) returns v_i for i<k and 0 otherwise, and stepFunction(h) equals v_i on each open interval (c_i,c_{i+1}) and 0 elsewhere, including at the cut points. fieldRecursion(h) starts from x ↦ log cosh x − v_{k-1}/2 and successively applies gaussianTransform with variance v_i−v_{i−1} (taking v_{−1}=0) and parameter d=c_i, applying the index i=k−1 first and i=0 last, and then evaluates the result at 0. pathMeasure is Lebesgue measure restricted to (0,1). An OverlapPath is a pathMeasure-almost-everywhere class of real functions admitting a representative q that is monotone on (0,1) with values in [0,1]. cellAverage(q,k,i) is the mean of q over the interval (i/k,(i+1)/k). For a function f, uniformPattern(f,q,n) uses k=n+1 cells and level values equal to the cell averages for i<k and 1 for i=k, then applies gaussianTransform to f with variances equal to successive level differences (starting from level 0) and parameters i/k for i=0,…,k, and evaluates at 0. patternFunctional(f,q) is the limit of these values as n→∞, taken with Lean's limUnder, so it is only meaningful when the limit exists. isingEntropy(q), valued in the extended reals, is the supremum over all FieldSteps h of fieldRecursion(h) plus one half of ∫ stepFunction(h)(u)·q(u) du over (0,1). Finally variationalValue(α,f) is the infimum over all OverlapPaths q of α·patternFunctional(f,q) + isingEntropy(q), a Parisi-type variational formula for the Ising perceptron.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/IsingFiniteness.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/IsingFiniteness.lean; bytes 16..2672
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

noncomputable section
namespace IsingPerceptron

def gaussianTransform (s d : ℝ) (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  if d = 0 then ∫ z, U (x + Real.sqrt s * z) ∂gaussianReal 0 1
  else (Real.log (∫ z, Real.exp (d * U (x + Real.sqrt s * z))
    ∂gaussianReal 0 1)) / d

structure Partition where
  levels : ℕ
  positive : 0 < levels
  cut : Fin (levels + 1) → ℝ
  ordered : StrictMono cut
  first : cut ⟨0, Nat.zero_lt_succ levels⟩ = 0
  last : cut ⟨levels, Nat.lt_succ_self levels⟩ = 1

structure FieldStep where
  partition : Partition
  value : Fin partition.levels → ℝ
  nonneg : ∀ i, 0 ≤ value i
  ordered : Monotone value

 
def stepAt (h : FieldStep) (i : ℕ) : ℝ :=
  if hi : i < h.partition.levels then h.value ⟨i, hi⟩ else 0

 

def stepFunction (h : FieldStep) (u : ℝ) : ℝ :=
  ∑ i : Fin h.partition.levels,
    if h.partition.cut i.castSucc < u ∧ u < h.partition.cut i.succ then h.value i else 0

 
def fieldRecursion (h : FieldStep) : ℝ :=
  let k := h.partition.levels
  let increments := List.ofFn (fun i : Fin k =>
    (stepAt h i - (if i.val = 0 then 0 else stepAt h (i.val - 1)),
      h.partition.cut i.castSucc))
  increments.foldr (fun sd U => gaussianTransform sd.1 sd.2 U)
    (fun x => Real.log (Real.cosh x) - stepAt h (k - 1) / 2) 0

def pathMeasure : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)

 
structure OverlapPath where
  val : ℝ →ₘ[pathMeasure] ℝ
  admissible : ∃ q : ℝ → ℝ,
    (q =ᵐ[pathMeasure] val) ∧ MonotoneOn q (Set.Ioo 0 1) ∧
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, q u ∈ Set.Icc (0 : ℝ) 1

 
def cellAverage (q : OverlapPath) (k i : ℕ) : ℝ :=
  (k : ℝ) * ∫ u in Set.Ioo ((i : ℝ) / k) (((i : ℝ) + 1) / k),
    q.val u ∂pathMeasure

 

def uniformPattern (f : ℝ → ℝ) (q : OverlapPath) (n : ℕ) : ℝ :=
  let k := n + 1
  let levelVal := fun i => if i < k then cellAverage q k i else 1
  let increments := List.ofFn (fun i : Fin (k + 1) =>
    (levelVal i - (if i.val = 0 then 0 else levelVal (i.val - 1)), (i : ℝ) / k))
  increments.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) f 0

 

def patternFunctional (f : ℝ → ℝ) (q : OverlapPath) : ℝ :=
  Filter.limUnder atTop (uniformPattern f q)

 

def isingEntropy (q : OverlapPath) : EReal :=
  ⨆ h : FieldStep,
    ((fieldRecursion h + (∫ u, stepFunction h u * q.val u ∂pathMeasure) / 2 : ℝ) : EReal)

def variationalValue (α : ℝ) (f : ℝ → ℝ) : EReal :=
  ⨅ q : OverlapPath, (α * patternFunctional f q : ℝ) + isingEntropy q



end IsingPerceptron
end
end OAI


