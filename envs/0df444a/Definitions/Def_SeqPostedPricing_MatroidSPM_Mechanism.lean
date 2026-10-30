-- Prove2me | Definitions.Def_SeqPostedPricing_MatroidSPM_Mechanism
-- name    : SeqPostedPricing_MatroidSPM_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:27:49.984318+00:00
-- url     : https://prove2.me/theorems/94a63959-07d6-460a-98c1-628395ade10f
-- title:
--   Mechanism $M=(M(\mathbf v),\pi(\mathbf v))$ for $n$ single-parameter agents
-- statement:
--   A **mechanism** for $n$ single-parameter agents $[n]$ maps every vector of (reported) values $\mathbf v=(v_1,\dots,v_n)\in\mathbb R^n$ to
--
--   1. an **allocation** $M(\mathbf v)\subseteq[n]$, the set of agents served, and
--   2. a **pricing** $\pi(\mathbf v)=(\pi_1(\mathbf v),\dots,\pi_n(\mathbf v))$, where $\pi_i(\mathbf v)$ is the price paid by agent $i$.
--
--   This is the object that the revenue benchmark (Myerson's mechanism) and the sequential posted-price mechanisms are compared over.
--
--   **Formalization Note** Agents are `Fin n`. Mechanisms are deterministic. Feasibility $M(\mathbf v)\in\mathcal J$ is not part of the structure; it is required by `IsAdmissible`.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.1, unnumbered, p. 4

import Mathlib

namespace SeqPostedPricing.MatroidSPM

/-- **A (deterministic) mechanism for the BSMD with `n` agents.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §2.1, unnumbered, p. 4 (PDF p. 6): "A mechanism M for this problem is a function that maps a
vector of values v to an allocation M(v) ∈ J and a pricing π(v) with a price πi to be paid by
agent i."

`alloc v` is the set of agents served at the reported value profile `v : Fin n → ℝ`, and
`pay v i` is the price `π_i(v)` charged to agent `i`.

**Formalization Note.** Agents are `Fin n` (the paper's `[n]`). Feasibility of the allocation
(`M(v) ∈ J`) is not bundled into the structure; it is the first clause of `IsAdmissible`, so the
same structure serves every feasibility constraint. Mechanisms are deterministic, as are the
paper's mechanisms (Myerson's mechanism and the SPMs). -/
structure Mechanism (n : ℕ) where
  /-- The set of agents served at the value profile. -/
  alloc : (Fin n → ℝ) → Finset (Fin n)
  /-- The payment charged to each agent at the value profile. -/
  pay : (Fin n → ℝ) → Fin n → ℝ

end SeqPostedPricing.MatroidSPM


