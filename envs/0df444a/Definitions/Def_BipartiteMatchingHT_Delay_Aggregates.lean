-- Prove2me | Definitions.Def_BipartiteMatchingHT_Delay_Aggregates
-- name    : BipartiteMatchingHT_Delay_Aggregates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:13:29.533257+00:00
-- url     : https://prove2.me/theorems/fb6159c5-cb90-4d3a-8295-7295f7b7d04e
-- title:
--   Compressed queue events and product-form comparison expressions
-- statement:
--   Busy servers are extracted from the arrival-ordered in-service jobs, followed by the idle-server list. Each waiting-count coordinate counts only jobs between two successive in-service customers, or after the final in-service customer. Compressed states have a server permutation, a busy count between zero and $m$, and an unrestricted natural-number waiting vector of that length. Their stationary mass is the sum of the genuine operational equilibrium probabilities of states with those coordinates. Aggregate mass retains only the server permutation and busy count, summing over all queue lengths. It is a real probability on stable inputs.
--
--   The product factor in equation (7), the total probability of all fully busy permutations induced by an order, and the rational expression on the right of Lemma 6 are defined separately for theorem comparisons. In particular, neither the stationary measure nor the tagged waiting mean is defined using these expressions. The all-idle state is included, and the interval counts exclude customers in service.
--
--   The interval interpretation follows the explicit description of N_ell in the proof of Lemma 6 on p. 47, which resolves the abbreviated wording of the compressed coordinates on p. 17.
-- source:
--   Afèche, Caldentey and Gupta, On the Optimal Design of a Bipartite Matching Queueing System, Operations Research (catalog 2021), https://doi.org/10.1287/opre.2020.2027; acquired artifact dated November 3, 2019; citation_basis published; printed/PDF pp. 16–19, (7)–(8), Lemmas 5–6

import Definitions.Def_BipartiteMatchingHT_Delay_Queue
import Definitions.Def_BipartiteMatchingHT_Delay_Components

open scoped BigOperators ENNReal
noncomputable section

namespace BipartiteMatchingHT.Delay
variable {n m : ℕ}

def busyServers (q : QueueState n m) : List (Fin m) := q.jobs.filterMap Job.server
def aggregateOrder (q : QueueState n m) : List (Fin m) := busyServers q ++ q.idle

/-- Counts the waiting customers between each in-service customer and the next
in-service customer, or after the final one. In-service jobs are not counted. -/
def intervalCounts : List (Job n m) → List ℕ
  | [] => []
  | x :: xs => if x.server.isSome then
      (xs.takeWhile (fun y => y.server.isNone)).length :: intervalCounts xs
    else intervalCounts xs

/-- Countable compressed states with busy count 0 through m, including all-idle
states, and no artificial bound on queue lengths. -/
abbrev Compressed (m : ℕ) :=
  (b : Fin (m + 1)) × (Equiv.Perm (Fin m) × (Fin b.val → ℕ))

def compressedEvent (q : QueueState n m) (x : Compressed m) : Prop :=
  aggregateOrder q = serverList x.2.1 ∧
    (busyServers q).length = x.1.val ∧ intervalCounts q.jobs = List.ofFn x.2.2

def aggregateEvent (q : QueueState n m) (s : Equiv.Perm (Fin m)) (b : ℕ) : Prop :=
  aggregateOrder q = serverList s ∧ (busyServers q).length = b

def compressedMass (D : Model n m) (ρ : ℝ) (x : Compressed m) : ℝ≥0∞ := by
  classical
  exact ∑' q, if compressedEvent q x then equilibrium D ρ q else 0

def aggregateMass (D : Model n m) (ρ : ℝ) (s : Equiv.Perm (Fin m)) (b : ℕ) : ℝ := by
  classical
  exact (∑' q, if aggregateEvent q s b then equilibrium D ρ q else (0 : ℝ≥0∞)).toReal

/-- The right side of (7) without B, for comparison to the genuine operational
law; this is not the definition of equilibrium. -/
def productFactor (D : Model n m) (ρ : ℝ) (x : Compressed m) : ℝ :=
  (∏ a : Fin x.1.val,
    (ρ * D.demand (onlyClasses D.edge (serverPrefix x.2.1 (a.val + 1)))) ^ (x.2.2 a) /
    (D.capacity (serverPrefix x.2.1 (a.val + 1))) ^ (x.2.2 a + 1)) *
  ∏ a : Fin m, if x.1.val ≤ a.val then
    (ρ * D.demand (someClasses D.edge (serverSuffix x.2.1 a.val)))⁻¹ else 1

def orderMass (D : Model n m) (ρ : ℝ) (σ : ComponentOrder D) : ℝ :=
  ∑ s ∈ inducedServers D σ, aggregateMass D ρ s m

def finiteWaitFormula (D : Model n m) (ρ : ℝ) (i : Fin n) : ℝ := by
  classical
  exact ∑ s : Equiv.Perm (Fin m), ∑ b ∈ Finset.Icc 1 m,
    (∑ r ∈ Finset.Icc 1 b,
      (if i ∈ onlyClasses D.edge (serverPrefix s r) then (1 : ℝ) else 0) /
        D.slack ρ (serverPrefix s r)) * aggregateMass D ρ s b

end BipartiteMatchingHT.Delay


