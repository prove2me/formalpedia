-- Prove2me | Definitions.Def_KMedianRefinedRecovery
-- name    : KMedianRefinedRecovery
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:16.166997+00:00
-- url     : https://prove2.me/theorems/576874a4-751e-4713-a749-008d0ccf5f6a
-- statement:
--   This block formalizes ingredients for refined recovery in metric k-median. A RationalMetricInput consists of finitely many points, a rational pseudometric-like distance (nonnegative, zero on the diagonal, symmetric, satisfying the triangle inequality), client and facility sets that together cover all points, a positive budget, and a nonempty facility set. A set S is feasible if it lies in the facilities, has at most budget elements, and is nonempty whenever there are clients; its cost is the sum over clients of the distance to the nearest member of S (zero for empty S). The input has a size (number of clients plus facilities) and a self-delimiting binary encoding of the point count, budget, client and facility indicators, and all rational distances; a binary output string is decoded as the set of facilities whose indexed bit is true. A BinaryRandomizedAlgorithm is a polynomial bound on random bits together with a polynomial-time Turing-machine computable function on pairs of bit strings, with finite work alphabets. The refined Input strengthens the metric: clients and facilities are disjoint, all distances are natural numbers, distinct points are at positive distance, and a distinguished anchor set of facilities has exactly budget elements. It is Bounded by a polynomial if every distance is at most that polynomial evaluated at the size. For a center set O, each point is assigned to its nearest center, with ties broken by smallest index, giving clusters of clients and real-valued cluster costs. A Certificate with parameters μ and L₀ consists of a facility set of centers with the same cardinality as the anchor and positive cost, a good subset, and an injective proxy map from good centers into the anchor, such that reassigning each good cluster to its proxy raises the total distance by at most μ times the full cost of the centers, while the number of non-good centers is at most L₀ log(size). The block also defines the precision ⌈log(1/ζ)/log 2⌉, the query encoding (metric bits paired with anchor bits followed by that many ones), the seed length given by the polynomial on the query length, the output set for each seed, the success probability that cost is at most a target (the fraction of seeds achieving it), a work bound adding query length, seed length and running time, and PolynomialWork, which says that work is at most c(size+1)^d(1+log(1/ζ))^d for all bounded inputs and all ζ in (0,1). No theorem is asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/KMedianRefinedRecovery.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/KMedianRefinedRecovery.lean; bytes 16..5883
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace MetricKMedianRecovery

structure RationalMetricInput where
  pointCount : ℕ
  distance : Fin pointCount → Fin pointCount → ℚ
  clients : Finset (Fin pointCount)
  facilities : Finset (Fin pointCount)
  budget : ℕ
  facilities_nonempty : facilities.Nonempty
  budget_pos : 0 < budget
  covered : clients ∪ facilities = Finset.univ
  distance_nonneg : ∀ x y, 0 ≤ distance x y
  distance_self : ∀ x, distance x x = 0
  distance_symm : ∀ x y, distance x y = distance y x
  distance_triangle : ∀ x y z, distance x z ≤ distance x y + distance y z

namespace RationalMetricInput

def size (I : RationalMetricInput) : ℕ := I.clients.card + I.facilities.card

def Feasible (I : RationalMetricInput) (S : Finset (Fin I.pointCount)) : Prop :=
  S ⊆ I.facilities ∧ S.card ≤ I.budget ∧ (I.clients.Nonempty → S.Nonempty)

def cost (I : RationalMetricInput) (S : Finset (Fin I.pointCount)) : ℚ :=
  if hS : S.Nonempty then ∑ p ∈ I.clients, S.inf' hS (I.distance p) else 0

def natBits (n : ℕ) : List Bool :=
  List.replicate (Nat.bits n).length true ++ [false] ++ Nat.bits n

def rationalBits (r : ℚ) : List Bool :=
  [decide (r < 0)] ++ natBits r.num.natAbs ++ natBits r.den

def bits (I : RationalMetricInput) : List Bool :=
  natBits I.pointCount ++ natBits I.budget ++
    List.ofFn (fun i : Fin I.pointCount => decide (i ∈ I.clients)) ++
    List.ofFn (fun i : Fin I.pointCount => decide (i ∈ I.facilities)) ++
    (List.ofFn (fun i : Fin I.pointCount =>
      (List.ofFn (fun j : Fin I.pointCount => rationalBits (I.distance i j))).flatten)).flatten

def decodeOutput (I : RationalMetricInput) (out : List Bool) : Finset (Fin I.pointCount) :=
  I.facilities.filter (fun i => out[i.val]?.getD false = true)

end RationalMetricInput

def pairBits (p : List Bool × List Bool) : List Bool :=
  p.1.flatMap (fun b => [true, b]) ++ [false] ++ p.2

structure BinaryRandomizedAlgorithm where
  randomBits : Polynomial ℕ
  run : List Bool × List Bool → List Bool
  computation : Turing.TM2ComputableInPolyTime pairBits id run
  finiteWorkAlphabet : ∀ k : computation.tm.K, Finite (computation.tm.Γ k)


end MetricKMedianRecovery


namespace MetricKMedianRecovery.RefinedRecovery

structure Input where
  metric : RationalMetricInput
  disjoint : Disjoint metric.clients metric.facilities
  integral : ∀ x y, ∃ z : ℕ, metric.distance x y = (z : ℚ)
  positive : ∀ x y, x ≠ y → 0 < metric.distance x y
  anchor : Finset (Fin metric.pointCount)
  anchor_subset : anchor ⊆ metric.facilities
  anchor_card : anchor.card = metric.budget

namespace Input
abbrev Point (I : Input) := Fin I.metric.pointCount

def size (I : Input) : ℕ := I.metric.size

def Bounded (I : Input) (bound : Polynomial ℕ) : Prop :=
  ∀ x y, I.metric.distance x y ≤ ((bound.eval I.size : ℕ) : ℚ)

noncomputable def assign (I : Input) (O : Finset I.Point) (p : I.Point) : I.Point :=
  if h : O.Nonempty then
    Classical.choose (Finset.exists_min_image O
      (fun i => toLex (I.metric.distance p i, i)) h)
  else p

noncomputable def cluster (I : Input) (O : Finset I.Point) (i : I.Point) : Finset I.Point :=
  I.metric.clients.filter (fun p => I.assign O p = i)

noncomputable def clusterCost (I : Input) (O : Finset I.Point) (i : I.Point) : ℝ :=
  ∑ p ∈ I.cluster O i, (I.metric.distance p i : ℝ)

def anchorBits (I : Input) : List Bool :=
  List.ofFn (fun i : I.Point => decide (i ∈ I.anchor))

end Input

structure Certificate (I : Input) (μ : ℚ) (L₀ : ℝ) where
  centers : Finset I.Point
  centers_subset : centers ⊆ I.metric.facilities
  same_card : centers.card = I.anchor.card
  positive_cost : 0 < (I.metric.cost centers : ℝ)
  good : Finset I.Point
  good_subset : good ⊆ centers
  proxy : I.Point → I.Point
  proxy_mem : ∀ i ∈ good, proxy i ∈ I.anchor
  proxy_inj : Set.InjOn proxy (↑good)
  proxy_cost : (∑ i ∈ good, ∑ p ∈ I.cluster centers i,
      (I.metric.distance p (proxy i) : ℝ)) ≤
    (∑ i ∈ good, I.clusterCost centers i) + (μ : ℝ) * (I.metric.cost centers : ℝ)
  few_bad : (((centers \ good).card : ℕ) : ℝ) ≤ L₀ * Real.log (I.size : ℝ)

noncomputable def precision (ζ : ℝ) : ℕ :=
  ⌈Real.log (1 / ζ) / Real.log 2⌉₊

noncomputable def queryBits (I : Input) (ζ : ℝ) : List Bool :=
  pairBits (I.metric.bits, I.anchorBits ++ List.replicate (precision ζ) true)

noncomputable def seedLength (A : BinaryRandomizedAlgorithm) (I : Input) (ζ : ℝ) : ℕ :=
  A.randomBits.eval (queryBits I ζ).length

abbrev Seed (A : BinaryRandomizedAlgorithm) (I : Input) (ζ : ℝ) :=
  Fin (seedLength A I ζ) → Bool

noncomputable def output (A : BinaryRandomizedAlgorithm) (I : Input) (ζ : ℝ)
    (s : Seed A I ζ) : Finset I.Point :=
  I.metric.decodeOutput (A.run (queryBits I ζ, List.ofFn s))

noncomputable def successProbability (A : BinaryRandomizedAlgorithm) (I : Input)
    (ζ target : ℝ) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun s : Seed A I ζ =>
    (I.metric.cost (output A I ζ s) : ℝ) ≤ target)).card : ℝ) /
    2 ^ seedLength A I ζ

noncomputable def workBound (A : BinaryRandomizedAlgorithm) (I : Input) (ζ : ℝ) : ℕ :=
  (queryBits I ζ).length + seedLength A I ζ +
    A.computation.time.eval (pairBits
      (queryBits I ζ, List.replicate (seedLength A I ζ) false)).length

def PolynomialWork (A : BinaryRandomizedAlgorithm) (bound : Polynomial ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ d : ℕ,
    ∀ I : Input, I.Bounded bound → ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
      (workBound A I ζ : ℝ) ≤
        c * ((I.size : ℝ) + 1) ^ d * (1 + Real.log (1 / ζ)) ^ d


end MetricKMedianRecovery.RefinedRecovery

namespace MetricKMedianRecovery.RefinedRecovery



end MetricKMedianRecovery.RefinedRecovery
end OAI


