-- Prove2me | Definitions.Def_SeqPostedPricing_PartitionSPM_IsQuantilePrice
-- name    : SeqPostedPricing_PartitionSPM_IsQuantilePrice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:07:38.70644+00:00
-- url     : https://prove2.me/theorems/f03f2b3a-b90c-4f6f-a90a-fee499d30d8d
-- title:
--   The price $F^{-1}(1-q)$
-- statement:
--   For a distribution $\nu$ on $\mathbb R$ and $q \in [0,1]$, a real number $p$ is the price $F^{-1}(1 - q)$ if it is the largest price at which a value drawn from $\nu$ exceeds the price with probability exactly $q$:
--
--   $$
--   \nu\big((p, \infty)\big) = q \quad\text{and}\quad \nu\big((p', \infty)\big) < q \ \text{ for every } p' > p.
--   $$
--
--   For a regular distribution and $0 < q < 1$ this price exists and is unique; for $q = 1$ it is the bottom of the support.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, Lemma 2, p. 5 (PDF p. 7), and §4, p. 6 (PDF p. 8): "p_i = F_i^{−1}(1 − q_i)"

import Mathlib

namespace SeqPostedPricing.PartitionSPM

open MeasureTheory in
/-- **The price `F^{−1}(1 − q)`** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, Lemma 2, p. 5 = PDF p. 7, and §4, p. 6 = PDF p. 8:
"p_i = F_i^{−1}(1 − q_i)"). `p` is the largest price at which a value drawn from `ν` exceeds the
price with probability exactly `q`: `ν((p, ∞)) = q` and `ν((p', ∞)) < q` for every `p' > p`.

**Formalization Note** Reading 3 of the mission. For a regular `ν` and `0 < q < 1` such a `p` is
unique; at `q = 1` it is the bottom of the support (the infimum convention would give `−∞`, which
is not a price). A predicate rather than an `sInf`, which would return junk at `q = 1`. -/
def IsQuantilePrice (ν : Measure ℝ) (q p : ℝ) : Prop :=
  (ν (Set.Ioi p)).toReal = q ∧ ∀ p', p < p' → (ν (Set.Ioi p')).toReal < q

end SeqPostedPricing.PartitionSPM


