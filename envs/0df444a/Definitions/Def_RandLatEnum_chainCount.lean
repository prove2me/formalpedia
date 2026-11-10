-- Prove2me | Definitions.Def_RandLatEnum_chainCount
-- name    : RandLatEnum_chainCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:15:02.033302+00:00
-- url     : https://prove2.me/theorems/a83c1398-f536-442a-ae98-2a3a84edf83c
-- title:
--   Number of admissible complete chains $F_n(h;L)$
-- statement:
--   For a ceiling $h:[0,1]\to\mathbb R$ and a lattice $L\subset\mathbb R^n$ ($n\ge2$),
--   $$
--   F_n(h;L)=\#\Bigl\{M_1\subset\dots\subset M_{n-1}\subset L:\ M_k\text{ primitive},\ \operatorname{rank}M_k=k,\ \det M_k\le n^{n\,h(k/n)}\ (1\le k<n)\Bigr\}.
--   $$
--   Chains of sublattices are counted, so different bases with the same prefix chain contribute once. Every basis whose prefix log-determinants satisfy $P_k(B)\le n\,h(k/n)\ln n$ for $1\le k<n$ yields such a chain.
--
--   **Formalization Note** A chain is a monotone family $M:\{0,\dots,n-2\}\to$ sublattices, with $M(k)$ the paper's $M_{k+1}$; the ranks make the inclusions strict and $M_{n-1}\ne L$. Rank is `Module.finrank ℤ`. The count is `Set.encard`, an extended natural number, so an infinite count is $\infty$, never $0$.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §7.1, (7.1), p.28

import Mathlib
import Definitions.Def_RandLatEnum_IsPrimitiveSub
import Definitions.Def_RandLatEnum_subDet

namespace RandLatEnum

/-- The number of admissible complete chains (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §7.1, (7.1), p.28):
`F_n(h; L) = #{M_1 ⊂ ⋯ ⊂ M_{n−1} ⊂ L : M_k primitive, rank M_k = k, det M_k ≤ n^{n h(k/n)}
(1 ≤ k < n)}`.

**Formalization Note.** A chain is a monotone family `M : Fin (n − 1) → Submodule`, with
`M k` the paper's `M_{k+1}` (0-based); the ranks make the inclusions strict and `M_{n−1} ≠ L`.
Chains, not bases, are counted. The count is `Set.encard` (an extended natural), so an infinite
count is `⊤`, never `0`. Rank is `Module.finrank ℤ`. Used for `n ≥ 2`. -/
noncomputable def chainCount (n : ℕ) (h : ℝ → ℝ)
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℕ∞ :=
  {M : Fin (n - 1) → Submodule ℤ (EuclideanSpace ℝ (Fin n)) |
    Monotone M ∧ ∀ k : Fin (n - 1), IsPrimitiveSub L (M k) ∧
      Module.finrank ℤ (M k) = (k : ℕ) + 1 ∧
      subDet (M k) ≤ (n : ℝ) ^ ((n : ℝ) * h (((k : ℕ) + 1 : ℝ) / n))}.encard

end RandLatEnum


