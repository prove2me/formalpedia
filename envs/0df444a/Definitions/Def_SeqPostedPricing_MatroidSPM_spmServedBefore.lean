-- Prove2me | Definitions.Def_SeqPostedPricing_MatroidSPM_spmServedBefore
-- name    : SeqPostedPricing_MatroidSPM_spmServedBefore
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:36:49.09371+00:00
-- url     : https://prove2.me/theorems/792732f1-8029-44b7-8615-1616e71063e9
-- title:
--   Agents served by the SPM in its first $t$ steps
-- statement:
--   A **sequential posted-price mechanism** (SPM) with order $\sigma$ and prices $p$ starts from $A=\emptyset$ and runs the steps for the agents $\sigma(1),\sigma(2),\dots,\sigma(n)$ in turn; it serves the final set $A$. This definition is the set $A$ after the first $t$ steps; after $n$ steps it is the set of agents the SPM serves.
--
--   **Formalization Note** The order is a permutation $\sigma$ of `Fin n`, step $s$ (counted from $0$) considering agent $\sigma(s)$; prices are indexed by agent.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.2, unnumbered, p. 4

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_spmStep
open MeasureTheory
open scoped Classical

namespace SeqPostedPricing.MatroidSPM

/-- **Agents served by the SPM in its first `t` steps.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §2.2, unnumbered, p. 4 (PDF p. 6): "1. Initialize A ← ∅. 2. For i = 1 through n, do: …
3. Serve the agents in A."

`spmServedBefore Feas p active σ v t` is the set `A` after the first `t` steps, the agent
offered at step `s` being `σ s`; `spmServedBefore … n` is the set of agents the SPM serves.

**Formalization Note.** The order is a permutation `σ : Fin n ≃ Fin n` mapping a step (counted
from `0`) to an agent: `σ s` is the paper's `σ(s + 1)`. Prices are indexed by agent (`p (σ s)`
is the price offered at step `s`). -/
noncomputable def spmServedBefore {n : ℕ} (Feas : Finset (Fin n) → Prop) (p : Fin n → ℝ)
    (active : Finset (Fin n)) (σ : Fin n ≃ Fin n) (v : Fin n → ℝ) (t : ℕ) : Finset (Fin n) :=
  ((List.ofFn (fun s => σ s)).take t).foldl (spmStep Feas p active v) ∅

end SeqPostedPricing.MatroidSPM


