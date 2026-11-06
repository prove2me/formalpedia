-- Prove2me | Definitions.Def_TIESharp_kernelExpansion
-- name    : TIESharp_kernelExpansion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:36:02.958817+00:00
-- url     : https://prove2.me/theorems/ffa2b69b-1c86-4ce4-a62b-5902cc66f085
-- title:
--   Kernel expansion (4.14) of the first job's assignment probability
-- statement:
--   Given kernels $h_{i,k}$, $k\ge0$, each a function of a distinguished column and $k$ further columns, the **expansion (4.14)** of the probability of assigning job $1$ to machine $i$ at a profile $t$ with $m$ jobs is
--   $$q^{m,*}_{i1}(t)=\sum_{k=0}^{\min(n-2,\,m-1)}\ \sum_{J\subseteq\{2,\dots,m\},\ |J|=k}h_{i,k}(t_{\cdot1};t_J),$$
--   with $t_J$ the columns of $J$ in increasing order. Each term involves the distinguished column and at most $n-2$ others, and the same kernel is used at every job count.
--
--   **Formalization Note.** The profile has `m + 1` jobs `Fin (m+1)`, with distinguished job `0` and the others `Fin m` (via `Fin.succ`), so the paper's upper limit $\min(n-2,m-1)$ reads `min (n - 2) m`.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §4.3.2, p.21, (4.14)

import Mathlib

set_option autoImplicit false

namespace TIESharp

/-- The **kernel expansion (4.14)** of the probability of assigning the distinguished job to
machine `i` (Li, *Sharp Bounds for Truthful-in-Expectation Scheduling*, arXiv:2611.05134, §4.3.2,
p.21): for a profile with `m + 1` jobs whose job `1` is distinguished,
`q_{i1}(t) = Σ_{k=0}^{min(n−2, m)} Σ_{J ⊆ {2,…,m+1}, |J| = k} h_{i,k}(t_{·1}; t_J)`,
where `h_{i,k}` takes the distinguished column and then the `k` columns of `J` in increasing order.

**Formalization Note.** Jobs are `Fin (m + 1)` with the distinguished job `0`; the other jobs are
`Fin m`, embedded by `Fin.succ`, so `J : Finset (Fin m)` and `J.orderEmbOfFin` lists its columns in
increasing order. The paper's job count `m ≥ 1` is `m + 1` here, so the upper limit
`min(n − 2, m − 1)` of (4.14) reads `min (n - 2) m`. A kernel of order `k` is
`h i k : (Fin n → ℝ) → (Fin k → Fin n → ℝ) → ℝ`, a column followed by `k` columns. -/
noncomputable def kernelExpansion {n : ℕ}
    (h : Fin n → (k : ℕ) → (Fin n → ℝ) → (Fin k → Fin n → ℝ) → ℝ)
    (m : ℕ) (i : Fin n) (t : Fin n → Fin (m + 1) → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (min (n - 2) m + 1),
    ∑ J : {J : Finset (Fin m) // J.card = k},
      h i k (fun a => t a 0) (fun l a => t a (J.1.orderEmbOfFin J.2 l).succ)

end TIESharp


