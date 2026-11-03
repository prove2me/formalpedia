-- Prove2me | Definitions.Def_SparseBatchBandit_subInterval
-- name    : SparseBatchBandit_subInterval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:27:57.22773+00:00
-- url     : https://prove2.me/theorems/0fdc2db4-8350-498d-80dd-4d5e5fa7f0cd
-- title:
--   Sub-interval $T_m^{(j)}$
-- statement:
--   Each batch is split evenly into $M$ intervals. If batch $m$ has $n$ rounds, its $q$-th round belongs to $T_m^{(j)}$, the **$j$-th interval of the $m$-th batch**, exactly when
--
--   $$
--   \Big\lfloor\frac{(j-1)n}{M}\Big\rfloor<q\le\Big\lfloor\frac{jn}{M}\Big\rfloor,\qquad j\in[M].
--   $$
--
--   **Formalization Note** The paper says only that the batch is partitioned into $M$ intervals evenly; this formula is the standard floor partition. The index $j$ is meant in $1,\dots,M$.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Algorithm 1, p.16; §4.2.1, p.17

import Mathlib
import Definitions.Def_SparseBatchBandit_batch

namespace SparseBatchBandit

/-- The `j`-th interval `T_m^{(j)}` of the `m`-th batch, `j ∈ [M]`, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, Algorithm 1, p.16 (PDF 16)
and §4.2.1, p.17 (PDF 17). If batch `m` has `n` rounds, its `q`-th round (`1 ≤ q ≤ n`) lies in
`T_m^{(j)}` iff `⌊(j−1)n/M⌋ < q ≤ ⌊jn/M⌋`.

**Formalization Note.** The page says only that each batch is partitioned into `M` intervals
evenly. Natural division is the floor. `j` is meant in `1..M`, where `j − 1` is exact. -/
noncomputable def subInterval (T s₀ M m j : ℕ) : Finset (Fin T) :=
  (batch T s₀ M m).filter (fun t =>
    let n := (batch T s₀ M m).card
    let q := ((batch T s₀ M m).filter (fun u => u ≤ t)).card
    (j - 1) * n / M < q ∧ q ≤ j * n / M)

end SparseBatchBandit


