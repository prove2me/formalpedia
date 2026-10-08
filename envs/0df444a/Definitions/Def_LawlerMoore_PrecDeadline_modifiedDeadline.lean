-- Prove2me | Definitions.Def_LawlerMoore_PrecDeadline_modifiedDeadline
-- name    : LawlerMoore_PrecDeadline_modifiedDeadline
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T13:06:57.018354+00:00
-- url     : https://prove2.me/theorems/be00f73e-edff-4c95-aff8-e109ee5bfb3a
-- title:
--   Section 2 — the modified deadlines $\bar d_j = \min\{d_k \mid j\rho k\} + j\varepsilon$
-- statement:
--   Consider $n$ jobs, numbered $1,\dots,n$, to be processed on a single machine; job $j$ has a deadline $d_j \in \mathbb R$. Precedence constraints are given by a relation $\rho$ on the jobs: $i\rho j$ means that job $i$ must precede job $j$. Following Lawler and Moore, call $k$ a **successor** of $j$ if $j\rho k$, and count every job as one of its own successors. For a real number $\varepsilon$, the **modified deadline** of job $j$ is
--
--   $$
--   \bar d_j \;=\; \min\{\, d_k \mid k = j \text{ or } j\rho k \,\} \;+\; j\varepsilon .
--   $$
--
--   The first term is the earliest deadline among job $j$ and its successors: job $j$ must be finished before every successor starts, so it inherits their deadlines. The second term $j\varepsilon$, with $\varepsilon$ a small positive number, breaks ties in favour of the job with the smaller number. Ordering the jobs by increasing $\bar d_j$ is the sequencing rule of the paper's Theorem in §2.
--
--   **Formalization Note** Jobs are `Fin n`, 0-based: the Lean job `j` is the paper's job $j+1$, so the tie-breaking term is $((j:\mathbb N)+1)\,\varepsilon$, exactly the paper's $j\varepsilon$. The minimum is taken over `insert j {k | ρ j k}`, which is nonempty for every relation; for the reflexive (partial-order) relation $\rho$ of the paper this set is exactly $\{k \mid j\rho k\}$, as the paper's phrase "considering a job to be one of its own successors" (p. 78) indicates. No hypothesis on $\varepsilon$ is built into the definition; the theorems state $\varepsilon > 0$ and the smallness condition they need.
-- source:
--   Lawler, Moore, A Functional Equation and Its Application to Resource Allocation and Sequencing Problems, Management Sci. 16 (1969), p. 78, Section 2

import Mathlib

namespace LawlerMoore.PrecDeadline

/-- The modified deadline of Lawler and Moore (1969, §2, p. 78):
`d̄_j = min {d_k | j ρ k} + j ε`.

Jobs are `Fin n`, 0-based: the Lean job `j` is the paper's job `j + 1`, so the tie-breaking term
`j ε` of the paper is `((j : ℕ) + 1) * ε` here. `ρ j k` means that job `j` must precede job `k`.
The minimum runs over the successors of `j` *including `j` itself* ("considering a job to be one
of its own successors", p. 78); for the reflexive relation of the paper the set
`insert j {k | ρ j k}` is exactly `{k | ρ j k}`, and inserting `j` makes the minimum range over a
nonempty set for every relation. -/
def modifiedDeadline {n : ℕ} (ρ : Fin n → Fin n → Prop) [DecidableRel ρ] (d : Fin n → ℝ)
    (ε : ℝ) (j : Fin n) : ℝ :=
  (insert j (Finset.univ.filter (ρ j))).inf' (Finset.insert_nonempty _ _) d
    + ((j : ℕ) + 1 : ℝ) * ε

end LawlerMoore.PrecDeadline


