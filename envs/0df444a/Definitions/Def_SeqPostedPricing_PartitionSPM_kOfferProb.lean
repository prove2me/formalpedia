-- Prove2me | Definitions.Def_SeqPostedPricing_PartitionSPM_kOfferProb
-- name    : SeqPostedPricing_PartitionSPM_kOfferProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:11:54.148036+00:00
-- url     : https://prove2.me/theorems/0e68330b-e4e9-4bc9-a742-be0a4d154f43
-- title:
--   Offer probability in the $k$-unit SPM
-- statement:
--   Let the agents be indexed in offer order and let agent $a$ accept independently with probability $q_a$. The probability that agent $i$ is still offered service in the $k$-unit SPM, i.e. that fewer than $k$ of the agents before $i$ accept, is
--
--   $$
--   c_i = \sum_{A \subseteq \{a : a < i\},\ |A| < k} \ \prod_{a \in A} q_a \prod_{b < i,\ b \notin A} (1 - q_b).
--   $$
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, proof of Theorem 22, p. 15 (PDF p. 17)

import Mathlib

namespace SeqPostedPricing.PartitionSPM

/-- **Offer probability in the `k`-unit SPM** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, proof of Theorem 22, p. 15 = PDF p. 17: the
`c_i` of the `k`-item case). Agents are indexed in offer order and agent `a` accepts independently
with probability `q a`. `kOfferProb k q i` is the probability that fewer than `k` of the agents
before `i` accept, i.e. that agent `i` is still offered service:
`Σ_{A ⊆ {a < i}, |A| < k} Π_{a ∈ A} q_a Π_{b < i, b ∉ A} (1 − q_b)`.

**Formalization Note** Reading 7 of the mission: the offer probabilities depend only on the `q`'s,
so the `k`-uniform claims of Theorem 22's proof are stated about these sums. -/
def kOfferProb {n : ℕ} (k : ℕ) (q : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ A ∈ (Finset.univ.filter (· < i)).powerset.filter (fun A => A.card < k),
    (∏ a ∈ A, q a) * ∏ b ∈ (Finset.univ.filter (· < i)) \ A, (1 - q b)

end SeqPostedPricing.PartitionSPM


