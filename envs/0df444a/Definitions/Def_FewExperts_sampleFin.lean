-- Prove2me | Definitions.Def_FewExperts_sampleFin
-- name    : FewExperts_sampleFin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:18.673352+00:00
-- url     : https://prove2.me/theorems/657e13c5-5fe5-4856-b4e8-f09699abfb2b
-- title:
--   Sampling devices: inverse-CDF draw from a mixture, and the threshold index with $\Pr[r\le j]=p^{K-j}$
-- statement:
--   Two ways of turning a uniform variable $u\in[0,1]$ into a random choice.
--
--   1. **Drawing an expert from a mixture** $\mathcal D$: take the least expert $i$ with $u<\sum_{k\le i}\mathcal D(k)$. If $u$ is uniform and $\mathcal D$ is a probability vector, expert $i$ is drawn with probability exactly $\mathcal D(i)$, and the drawn expert always has $\mathcal D(i)>0$.
--   2. **The threshold index** of HarvestGain: take the least $j\in\{1,\dots,K\}$ with $u\le p^{K-j}$. For $p\in[0,1]$ and uniform $u$ this has the law (8),
--   $$
--   \Pr[r\le j]=p^{K-j},\qquad 1\le j\le K .
--   $$
--
--   These are the sampling devices of the formalized algorithm.
--
--   **Formalization Note** In the null events where no index qualifies, the draw returns the least expert with positive weight (or expert $0$) and the threshold index returns $1$.
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), §3.1, p.13 (PDF p.14); Algorithm 3, line 5 and (8), p.16 (PDF p.17); Algorithm 4, line 4, p.20 (PDF p.21)

import Mathlib

namespace FewExperts

open Classical in
/-- **Inverse-CDF sampling of an expert from a mixture.**
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), §3.1, p.13 (PDF 14) ("the algorithm could have sampled from this mix") and
Algorithm 4, line 4, p.20 ("Sample a multiset I = (i₁, …, i_m) of m experts independently from
𝒟").

`sampleFin D u` is the least expert `i` with `u < ∑_{k ≤ i} D k`. If `u` is uniform on `[0, 1]`
and `D` is a probability vector, then `sampleFin D u = i` with probability exactly `D i`, and the
returned expert always has `D i > 0`.

**Formalization Note** This is the sampling device of the formalization. If no index satisfies
`u < ∑_{k ≤ i} D k` (for a probability vector, only at `u = 1`, a null event), the least `i` with
`D i > 0` is returned, and the expert `0` if there is none. -/
noncomputable def sampleFin {N : ℕ} [NeZero N] (D : Fin N → ℝ) (u : ℝ) : Fin N :=
  if h : ∃ i : Fin N, u < ∑ k ∈ Finset.univ.filter (· ≤ i), D k then
    (Finset.univ.filter (fun i : Fin N => u < ∑ k ∈ Finset.univ.filter (· ≤ i), D k)).min'
      (by obtain ⟨i, hi⟩ := h; exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩)
  else if h' : ∃ i : Fin N, 0 < D i then
    (Finset.univ.filter (fun i : Fin N => 0 < D i)).min'
      (by obtain ⟨i, hi⟩ := h'; exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩)
  else 0

open Classical in
/-- **The threshold index of Algorithm 3, drawn from a uniform variable.**
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), Algorithm 3, line 5, and (8), p.16 (PDF 17): "Pick integers r_i ∈ {1, …, 1/α}
independently with Pr[r_i ≤ j] = p^{1/α−j}."

`thrIndex K p u` is the least `j ∈ {1, …, K}` with `u ≤ p^{K−j}`. For `p ∈ [0, 1]` the map
`j ↦ p^{K−j}` is nondecreasing with value `1` at `j = K`, so for `u` uniform on `[0, 1]`,
`Pr[thrIndex K p u ≤ j] = Pr[u ≤ p^{K−j}] = p^{K−j}` for `1 ≤ j ≤ K`: this is the law (8) with
`K = ⌊1/α⌋` levels.

**Formalization Note** If no `j ∈ {1, …, K}` qualifies (only when `K = 0`, or `u > 1`), the index
is `1`. -/
noncomputable def thrIndex (K : ℕ) (p : ℝ) (u : ℝ) : ℕ :=
  if h : ∃ j, 1 ≤ j ∧ j ≤ K ∧ u ≤ p ^ (K - j) then Nat.find h else 1

end FewExperts


