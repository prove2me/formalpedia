-- Prove2me | Definitions.Def_SecondKahnKalai
-- name    : SecondKahnKalai
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:52.890509+00:00
-- url     : https://prove2.me/theorems/551c0dce-3836-483b-93f3-c5705ba3c6f8
-- statement:
--   For a finite type X, bernoulliWeight(p,W) is the product over x of p if x lies in the subset W and 1-p otherwise, bernoulliExpectation(p,f) is the sum over all subsets W of bernoulliWeight(p,W)·f(W), and bernoulliProbability(p,P) is the sum of the weights of the subsets satisfying P; these are the product-measure expectation and probability for independent inclusion with parameter p, without any requirement that p lie in [0,1]. Edge(n) is the type of unordered pairs of distinct vertices of Fin n, graphOfEdges(W) is the simple graph on Fin n whose edges are those in W, and edgeCount(H) is the cardinality of the edge set of H via Nat.card (so it is 0 if the edge set is infinite). In the random graph G(n,p), where each edge is included independently with probability p, expectedCopies(n,p,H) is the expected value of Mathlib's copyCount of H in the graph, i.e. the number of unlabelled non-induced copies, and containmentProbability(n,p,H) is the probability that this count is positive. criticalThreshold(n,H) is the infimum of those p in [0,1] for which containmentProbability is at least 1/2. expectationThreshold(n,H) is the infimum of those p in [0,1] for which every subgraph F of H (viewed as a graph on its own vertex set) has expectedCopies(n,p,F) at least 1/2. logTwo(x) is log x / log 2. SecondKahnKalaiBounds(n,H) is a defined proposition, not an established theorem, asserting two inequalities: criticalThreshold ≤ min(1, 2048·e^50·expectationThreshold·(1+log₂(edgeCount H))), and criticalThreshold ≤ 6144·e^50·expectationThreshold·log₂ n.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SecondKahnKalai.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SecondKahnKalai.lean; bytes 215..2483
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

noncomputable section

universe u

namespace LeanBlast.SecondKahnKalai

def bernoulliWeight {X : Type u} [Fintype X] [DecidableEq X]
    (p : ℝ) (W : Finset X) : ℝ :=
  ∏ x, if x ∈ W then p else 1 - p

def bernoulliExpectation {X : Type u} [Fintype X] [DecidableEq X]
    (p : ℝ) (f : Finset X → ℝ) : ℝ :=
  ∑ W, bernoulliWeight p W * f W

def bernoulliProbability {X : Type u} [Fintype X] [DecidableEq X]
    (p : ℝ) (P : Finset X → Prop) : ℝ := by
  classical
  exact ∑ W, if P W then bernoulliWeight p W else 0

/-- The unordered non-loop edges of the complete graph on `n` vertices. -/
abbrev Edge (n : ℕ) := {e : Sym2 (Fin n) // ¬e.IsDiag}

/-- A set of edges, interpreted as an ordinary graph on all `n` vertices. -/
def graphOfEdges {n : ℕ} (W : Finset (Edge n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (Subtype.val '' (W : Set (Edge n)))

/-- The number of unordered edges, each counted once. -/
def edgeCount {V : Type u} (H : SimpleGraph V) : ℕ := Nat.card H.edgeSet

/-- Expected number of actual unlabelled non-induced copies in `G(n,p)`. -/
def expectedCopies {V : Type u} (n : ℕ) (p : ℝ) (H : SimpleGraph V) : ℝ :=
  bernoulliExpectation p (fun W : Finset (Edge n) =>
    ((graphOfEdges W).copyCount H : ℝ))

/-- Probability that `G(n,p)` contains at least one non-induced copy. -/
def containmentProbability {V : Type u} (n : ℕ) (p : ℝ)
    (H : SimpleGraph V) : ℝ :=
  bernoulliProbability p (fun W : Finset (Edge n) =>
    0 < (graphOfEdges W).copyCount H)

def criticalThreshold {V : Type u} (n : ℕ) (H : SimpleGraph V) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc 0 1 ∧ (1 / 2 : ℝ) ≤ containmentProbability n p H}

def expectationThreshold {V : Type u} (n : ℕ) (H : SimpleGraph V) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc 0 1 ∧
    ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤ expectedCopies n p F.coe}

def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

def SecondKahnKalaiBounds {V : Type u} (n : ℕ) (H : SimpleGraph V) : Prop :=
  criticalThreshold n H ≤
      min 1 (2048 * Real.exp 50 * expectationThreshold n H *
        (1 + logTwo (edgeCount H : ℝ))) ∧
    criticalThreshold n H ≤
      6144 * Real.exp 50 * expectationThreshold n H * logTwo (n : ℝ)



end LeanBlast.SecondKahnKalai
end
end OAI


