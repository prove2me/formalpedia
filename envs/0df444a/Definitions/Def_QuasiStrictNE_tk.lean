-- Prove2me | Definitions.Def_QuasiStrictNE_tk
-- name    : QuasiStrictNE_tk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:00.502064+00:00
-- url     : https://prove2.me/theorems/e00356aa-0f8d-40ae-8236-6158279d3493
-- title:
--   The projection threshold $t_k(z)$
-- statement:
--   For $z\in\mathbb R^k$ let $z_{(1)}\ge\cdots\ge z_{(k)}$ be its coordinates in decreasing order. The **threshold** is
--   $$
--   t_k(z)=\max_{1\le a\le k}\frac{\sum_{i=1}^a z_{(i)}-1}{a}.
--   $$
--   It is the unique $t$ with $\sum_i \max\{z_i-t,0\}=1$ (Lemma 1).
--
--   **Formalization Note** The sorted coordinates are the multiset of values of $z$ sorted by `Multiset.sort (· ≥ ·)`. The maximum is a supremum over the $k$ values $a=1,\dots,k$; the paper assumes $k\ge 1$.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Lemma 1, p.9

import Mathlib

namespace QuasiStrictNE

/-- **The projection threshold `tk(z)`** (Hansen & Nie, *On Existence and Computational Complexity of
Quasi-strict Equilibria*, arXiv:2611.06350, Lemma 1, p.9: "For z ∈ R^k, let z(1) ≥ · · · ≥ z(k) be
its coordinates in decreasing order, and define tk(z) = max_{1≤a≤k} (∑_{i=1}^a z(i) − 1)/a").

Let `z₍₁₎ ≥ ⋯ ≥ z₍ₖ₎` be the coordinates of `z` sorted in decreasing order (with multiplicity). Then
`tk k z` is the largest of the `k` numbers `(z₍₁₎ + ⋯ + z₍ₐ₎ − 1)/a`, `a = 1, …, k`.

**Formalization Note** The sorted coordinates are the list `Multiset.sort (· ≥ ·)` of the multiset of
values of `z`; its first `a` entries are `z₍₁₎, …, z₍ₐ₎`. The index `a ∈ {1, …, k}` is written
`a.val + 1` for `a : Fin k`, and the maximum is the supremum over `Fin k`. For `k = 0` (excluded by the
paper's standing convention `k ≥ 1`, p.4) the supremum over the empty index set is `0`. -/
noncomputable def tk (k : ℕ) (z : Fin k → ℝ) : ℝ :=
  ⨆ a : Fin k,
    ((((Finset.univ.val.map z).sort (· ≥ ·)).take (a.val + 1)).sum - 1) / ((a.val : ℝ) + 1)

end QuasiStrictNE


