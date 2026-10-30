-- Prove2me | Definitions.Def_SeqPostedPricing_PartitionSPM_Mechanism
-- name    : SeqPostedPricing_PartitionSPM_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:02:36.193796+00:00
-- url     : https://prove2.me/theorems/a048447a-9cc3-4d0c-b2fa-094b8024af2d
-- title:
--   Deterministic mechanism for single-parameter agents
-- statement:
--   There are $n$ single-parameter agents and one seller. A (deterministic) **mechanism** $M$ maps every vector $b = (b_1, \dots, b_n)$ of reported values to
--
--   1. an **allocation** $M(b)$, the set of agents served, and
--   2. a **pricing** $\pi(b) = (\pi_1(b), \dots, \pi_n(b))$, where $\pi_i(b)$ is the price paid by agent $i$.
--
--   Feasibility of the allocation, truthfulness and individual rationality are separate conditions on a mechanism.
--
--   **Formalization Note** Agents are `Fin n`. A mechanism is a pair of functions `alloc : (Fin n → ℝ) → Finset (Fin n)` and `pay : (Fin n → ℝ) → Fin n → ℝ`.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.1, unnumbered, p. 4 (PDF p. 6)

import Mathlib

namespace SeqPostedPricing.PartitionSPM

/-- **A (deterministic) mechanism for the BSMD** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.1, unnumbered, p. 4 = PDF p. 6:
"A mechanism M for this problem is a function that maps a vector of values v to an allocation
M(v) ∈ J and a pricing π(v) with a price πi to be paid by agent i"). `alloc v` is the set of agents
served at the value (bid) profile `v`, and `pay v i` is the price `π_i(v)` paid by agent `i`.

**Formalization Note** Agents are `Fin n` (0-based). Feasibility `M(v) ∈ J` is not part of the
structure; it is imposed by `IsAdmissible`. Mechanisms are deterministic, as Myerson's mechanism is. -/
structure Mechanism (n : ℕ) where
  /-- The set of agents served at the bid profile. -/
  alloc : (Fin n → ℝ) → Finset (Fin n)
  /-- The payment of each agent at the bid profile. -/
  pay : (Fin n → ℝ) → Fin n → ℝ

end SeqPostedPricing.PartitionSPM


