-- Prove2me | Definitions.Def_KServer
-- name    : KServer
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:16.3071+00:00
-- url     : https://prove2.me/theorems/5f58d93b-086f-4ac6-81fc-9d7dba0db5d6
-- statement:
--   A configuration of k servers in a space X is a function from Fin k to X, giving each server's location (servers may coincide). A label distribution is a probability vector on the k server labels, and a (randomized, online) policy maps the history of past (request, chosen label) pairs together with the current request to a label distribution. Serving a request with a given label moves that server to the request point, leaving the others unchanged. For a metric space X, the service cost of a request sequence with a chosen label sequence is the sum, over successive requests, of the distance the chosen server travels to reach the request, with configurations updated as the sequence proceeds. The path probability of a label sequence under a policy is the product of the probabilities the policy assigns to each chosen label given the history so far, and the expected cost is the sum over all label sequences of path probability times service cost, starting from an initial configuration s. The optimal cost is the infimum of the service cost over all label sequences (the offline optimum). MainStatement is a defined proposition, not an established theorem: there exists a constant C>0 such that for every k≥2 and every metric space X (in the given universe) containing at least k+1 distinct points, and every initial configuration s, there are a policy A and a number B≥0, with B=0 whenever s is injective (servers at distinct points), such that for every finite request sequence the expected cost of A is at most C(log(k+1))² times the optimal cost plus B. This is a polylogarithmic competitive-ratio statement for randomized k-server, where C does not depend on k or X.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/KServer.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/KServer.lean; bytes 16..2142
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace KServer

universe u

abbrev Configuration (k : ℕ) (X : Type u) := Fin k → X

def LabelDistribution (k : ℕ) :=
  {probability : Fin k → ℝ //
    (∀ label, 0 ≤ probability label) ∧ ∑ label, probability label = 1}

abbrev Policy (k : ℕ) (X : Type u) :=
  List (X × Fin k) → X → LabelDistribution k

def serve {k : ℕ} {X : Type u} (s : Configuration k X)
    (label : Fin k) (request : X) : Configuration k X :=
  Function.update s label request

def serviceCost {k : ℕ} {X : Type u} [MetricSpace X]
    (s : Configuration k X) : (requests : List X) → (Fin requests.length → Fin k) → ℝ
  | [], _ => 0
  | request :: requests, labels =>
      dist (s (labels 0)) request +
        serviceCost (serve s (labels 0) request) requests (fun index => labels index.succ)

def pathProbability {k : ℕ} {X : Type u} (A : Policy k X)
    (history : List (X × Fin k)) :
    (requests : List X) → (Fin requests.length → Fin k) → ℝ
  | [], _ => 1
  | request :: requests, labels =>
      (A history request).val (labels 0) *
        pathProbability A (history ++ [(request, labels 0)]) requests
          (fun index => labels index.succ)

def expectedCost {k : ℕ} {X : Type u} [MetricSpace X]
    (A : Policy k X) (s : Configuration k X) (requests : List X) : ℝ :=
  ∑ labels : Fin requests.length → Fin k,
    pathProbability A [] requests labels * serviceCost s requests labels

def optimalCost {k : ℕ} {X : Type u} [MetricSpace X]
    (s : Configuration k X) (requests : List X) : ℝ :=
  sInf (Set.range (serviceCost s requests))

def MainStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 2 ≤ k →
    ∀ (X : Type u) (_ : MetricSpace X),
      (∃ embedding : Fin (k + 1) → X, Function.Injective embedding) →
      ∀ s : Configuration k X,
        ∃ A : Policy k X, ∃ B : ℝ,
          0 ≤ B ∧ (Function.Injective s → B = 0) ∧
          ∀ requests : List X,
            expectedCost A s requests ≤
              C * (Real.log (k + 1)) ^ 2 * optimalCost s requests + B



end KServer
end
end OAI


