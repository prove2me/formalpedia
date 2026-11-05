-- Prove2me | Definitions.Def_ReusableMatching_seedMeasure
-- name    : ReusableMatching_seedMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:29:48.214715+00:00
-- url     : https://prove2.me/theorems/ce1dd207-9e93-4a0d-abdd-6288e73ee974
-- title:
--   Seed vectors and their uniform product law
-- statement:
--   A **seed vector** $Y$ assigns a seed $y_i^k\in[0,1]$ to every resource $i$ and every period $k\in\{0,\dots,n\}$. Periodic Reranking reads, at an arrival of period $k$, the seeds $y_i^k$ of that period.
--
--   The **seed law** makes all seeds independent and uniform on $[0,1]$: it is the product of the uniform probability measures on $[0,1]$, one factor for each pair (resource, period). Expectations over the randomness of the algorithm are integrals against this law.
--
--   **Formalization Note** Seeds of periods that contain no arrival are drawn but never read, so the law of everything the algorithm outputs is that of the paper.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, Algorithm 1, p.8 ("Every d time units: Generate new i.i.d. ranks y_i ∼ U[0,1]"); §3.1 Notations, p.8

import Mathlib

namespace ReusableMatching

/-- **A seed vector** `Y` of Periodic Reranking (arXiv:2110.07084v2, §3.1, p.8: "Let `y_i^k` denote
the `k`-th seed of resource `i`. … Let `Y` denote the vector of all random seeds"): one seed
`Y (i, k) ∈ [0, 1]` for every resource `i` and every period `k`.

**Formalization Note.** Periods are indexed by `Fin (n + 1)` (period `0` is the dummy period of
p.8, see `period`). With `n` arrivals and `d ≥ 1` only the periods `1, …, ⌈n / d⌉` contain
arrivals; the seeds of the other periods are never read by the algorithm. -/
abbrev Seeds (V : Type*) (n : ℕ) : Type _ := V × Fin (n + 1) → unitInterval

/-- **The law of the seeds** (arXiv:2110.07084v2, Algorithm 1, p.8: "Every `d` time units:
Generate new i.i.d. ranks `y_i ∼ U[0,1]` `∀ i ∈ V`"; p.7: the algorithm "(independently) samples a
random seed `y_i ∈ U[0,1]`"): all seeds are independent and uniform on `[0, 1]`.

**Formalization Note.** The product of the uniform (Lebesgue) probability measures on
`unitInterval`, one factor for every pair (resource, period). Seeds of periods without arrivals
are drawn too but never read, so the law of everything the algorithm outputs is the paper's. -/
noncomputable def seedMeasure (V : Type*) [Fintype V] (n : ℕ) :
    MeasureTheory.Measure (Seeds V n) :=
  MeasureTheory.Measure.pi (fun _ => (MeasureTheory.volume : MeasureTheory.Measure unitInterval))

end ReusableMatching


