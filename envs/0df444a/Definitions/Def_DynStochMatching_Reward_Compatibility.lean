-- Prove2me | Definitions.Def_DynStochMatching_Reward_Compatibility
-- name    : DynStochMatching_Reward_Compatibility
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T20:40:53.05373+00:00
-- url     : https://prove2.me/theorems/ba8f40c9-f104-47dd-a4bc-942e53c9fa0f
-- title:
--   Backward decomposition and chronological greedy execution
-- statement:
--   The positive support of each outgoing flow is sorted by decreasing flow-to-passive-rate ratio, with a fixed stable tie rule. Backward recursion implements equations (24)–(25). Arrivals are labeled passive with probability passive rate divided by arrival rate; conditional active labels have the normalized decomposition weights. Empty support or zero active mass produces an isolated active label, which can never match. Passive arrivals take the highest-reward available compatible active agent; ties use type, compatibility index and agent identity. Chronological recursion removes matched identities. No saturation adjustment is inserted, and the policy reward is always calculated from its execution.
-- source:
--   Aouad and Sarıtaç (2022), Dynamic Stochastic Matching Under Limited Time, https://doi.org/10.1287/opre.2022.2293, held published-basis manuscript, B.3, printed 42–45 / PDF 43–46

import Definitions.Def_DynStochMatching_Reward_Flows

open scoped Classical

namespace DynStochMatching.Reward

noncomputable def support {n : ℕ} (x : Flow n) (i : Fin n) : List (Fin n) :=
  ((List.finRange n).filter (fun j => 0 < x.edge i j)).mergeSort
    (fun j k => x.edge i j / passiveRate x j ≥ x.edge i k / passiveRate x k)

/-- Zero-based label index l corresponds to source label l+1. -/
noncomputable def compatibility {n : ℕ} (x : Flow n) (i : Fin n) (l : ℕ) : Finset (Fin n) :=
  ((support x i).take (l + 1)).toFinset

noncomputable def finiteDeathRate (l : Lifetime) : ℝ :=
  match l with | .exponential μ _ => μ | .immediate => 0

noncomputable def decompositionDenominator {n : ℕ} (D : Instance n)
    (x : Flow n) (i : Fin n) (l : ℕ) : ℝ :=
  finiteDeathRate (D.lifetime i) + ∑ j ∈ compatibility x i l, passiveRate x j

/-- Equations (24)-(25), evaluated backwards; no abandonment saturation is inserted. -/
noncomputable def decomposition {n : ℕ} (D : Instance n) (x : Flow n)
    (i : Fin n) : ℕ → ℝ :=
  (List.range (support x i).length).foldr (fun l acc =>
    match (support x i)[l]? with
    | none => acc
    | some j => Function.update acc l
      (decompositionDenominator D x i l / passiveRate x j *
        (x.edge i j - ∑ q ∈ (Finset.range (support x i).length).filter (fun q => l < q),
          passiveRate x j / decompositionDenominator D x i q * acc q))) (fun _ => 0)

noncomputable def activeMass {n : ℕ} (D : Instance n) (x : Flow n) (i : Fin n) : ℝ :=
  ∑ l ∈ Finset.range (support x i).length, decomposition D x i l

/-- Passive, active with a compatibility index, or an active agent with no possible partner.
The last branch completes the empty-support case without inventing a probability on an empty set. -/
inductive VertexLabel where
  | passive
  | active (index : ℕ)
  | isolated
  deriving DecidableEq

noncomputable def labelVertex {n : ℕ} (D : Instance n) (x : Flow n)
    (i : Fin n) (passiveCoin activeCoin : ℝ) : VertexLabel :=
  if passiveCoin < passiveRate x i / D.arrivalRate i then .passive
  else if (support x i).isEmpty ∨ activeMass D x i = 0 then .isolated
  else match categorical (support x i).length
      (fun l => decomposition D x i l.val / activeMass D x i) activeCoin with
    | some l => .active l.val
    | none => .isolated

noncomputable def agentLabel {n : ℕ} (D : Instance n) (x : Flow n)
    (ω : RandomSeeds) (k : ℕ) : VertexLabel :=
  match arrivalType D.toMarkedPoissonData ω k with
  | none => .isolated
  | some i => labelVertex D x i (Real.exp (-ω (k, 3))) (Real.exp (-ω (k, 4)))

noncomputable def agentOrderKey {n : ℕ} (D : Instance n) (x : Flow n)
    (ω : RandomSeeds) (m : ℕ) : ℕ × ℕ × ℕ :=
  match arrivalType D.toMarkedPoissonData ω m, agentLabel D x ω m with
  | some i, .active l => (i.val, l + 1, m)
  | _, _ => (n, n + 1, m)

def identityKeyLE (a b : ℕ × ℕ × ℕ) : Bool :=
  if a.1 = b.1 then
    if a.2.1 = b.2.1 then decide (a.2.2 ≤ b.2.2) else decide (a.2.1 < b.2.1)
  else decide (a.1 < b.1)

/-- Candidate partners are sorted by reward and then identity, making ties observable. -/
noncomputable def greedyPartner {n : ℕ} (D : Instance n) (x : Flow n)
    (ω : RandomSeeds) (k : ℕ) (alreadyMatched : Finset ℕ) : Option ℕ :=
  if agentLabel D x ω k ≠ .passive then none
  else let candidates := (List.range k).filter fun m =>
    m ∉ alreadyMatched ∧ present D ω (arrivalTime D.toMarkedPoissonData ω k) m ∧
      match arrivalType D.toMarkedPoissonData ω m, arrivalType D.toMarkedPoissonData ω k,
          agentLabel D x ω m with
      | some i, some j, .active l => j ∈ compatibility x i l
      | _, _, _ => False
    ((candidates.mergeSort fun m h =>
      if pairReward D ω (m, k) = pairReward D ω (h, k) then identityKeyLE (agentOrderKey D x ω m) (agentOrderKey D x ω h)
      else pairReward D ω (m, k) > pairReward D ω (h, k))).head?

/-- A chronological execution, with previously matched identities removed. -/
noncomputable def matchingHistory {n : ℕ} (D : Instance n) (x : Flow n)
    (ω : RandomSeeds) : ℕ → Finset (ℕ × ℕ)
  | 0 => ∅
  | k + 1 =>
    let old := matchingHistory D x ω k
    let used := old.image Prod.fst ∪ old.image Prod.snd
    match greedyPartner D x ω k used with
    | none => old
    | some m => insert (m, k) old

noncomputable def compatibilityPolicy {n : ℕ} (D : Instance n) (x : Flow n) : MatchingPolicy :=
  fun e ω => if e ∈ matchingHistory D x ω (e.2 + 1) then
    ENNReal.ofReal (arrivalTime D.toMarkedPoissonData ω e.2) else ⊤

end DynStochMatching.Reward


