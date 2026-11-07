-- Prove2me | Definitions.Def_DoublingMST_NetHierarchy
-- name    : DoublingMST_NetHierarchy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:29:33.853008+00:00
-- url     : https://prove2.me/theorems/2effbffb-0c73-424a-ac4f-490926133881
-- title:
--   Net hierarchy $N_0\supseteq\dots\supseteq N_L$ (§2.1, (9))
-- statement:
--   A **net hierarchy** is a sequence of sets $X=N_0\supseteq N_1\supseteq\dots\supseteq N_L$, with $L=\lceil\log_2\Delta\rceil+4$, such that $N_L$ is a single point and for every $0\le\ell\le L$
--
--   $$N_\ell\text{ is }2^{\ell-3}\text{-packing and }2^{\ell-2}\text{-covering for }X. \qquad (9)$$
--
--   Its **elements** are the pairs $(u,\ell)$ with $0\le\ell\le L$ and $u\in N_\ell$; $\ell=\operatorname{lev}(u)$ is the level.
--
--   **Formalization Note** The exponents are integers. The structure does not include the minimum-distance assumption, the doubling dimension or a construction; statements assume minimum distance $>1$ separately.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), §2.1, p.12 (PDF p.14), (9)

import Mathlib
import Definitions.Def_DoublingMST_IsPacking
import Definitions.Def_DoublingMST_IsCovering
import Definitions.Def_DoublingMST_topLevel

namespace DoublingMST

/-- **Net hierarchy.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), §2.1, p.12 (PDF p.14): "Construct a sequence of nested nets on X = N_0 ⊇ N_1 ⋯ ⊇ N_L,
such that ∀ 0 ≤ ℓ ≤ L, N_ℓ is 2^{ℓ−3}-packing and 2^{ℓ−2}-covering for X. (9) Specifically,
N_0 = X and N_L contains only one point in X."

A net hierarchy over `(Fin n, d)` with `L = topLevel d`: sets `N ℓ`, `N 0 = X`, nested for
`ℓ < L`, `|N L| = 1`, and (9) for every `ℓ ≤ L`.

**Formalization Note.** `N` is a function on `ℕ`; only `ℓ ≤ L` matters, and the hierarchy's
elements are the pairs `(u, ℓ)` with `ℓ ≤ L`, `u ∈ N ℓ`. The exponents `ℓ − 3`, `ℓ − 2` are
integers (`zpow`). The structure bundles neither ddim, nor the minimum-distance assumption, nor
any construction; the §2.1 assumption "minimum interpoint distance > 1" is a hypothesis of each
statement (`MinDistGtOne`), and under it such hierarchies exist (p.12). -/
structure NetHierarchy {n : ℕ} (d : Fin n → Fin n → ℝ) where
  /-- The nets `N_0, …, N_L`. -/
  N : ℕ → Finset (Fin n)
  /-- `N_0 = X`. -/
  base : N 0 = Finset.univ
  /-- `N_{ℓ+1} ⊆ N_ℓ`. -/
  nested : ∀ ℓ, ℓ < topLevel d → N (ℓ + 1) ⊆ N ℓ
  /-- `N_L` is a single point. -/
  top_card : (N (topLevel d)).card = 1
  /-- (9), packing. -/
  packing : ∀ ℓ, ℓ ≤ topLevel d → IsPacking d (N ℓ) ((2 : ℝ) ^ ((ℓ : ℤ) - 3))
  /-- (9), covering. -/
  covering : ∀ ℓ, ℓ ≤ topLevel d →
    IsCovering d (N ℓ) Finset.univ ((2 : ℝ) ^ ((ℓ : ℤ) - 2))

end DoublingMST


