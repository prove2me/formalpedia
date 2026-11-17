-- Prove2me | Definitions.Def_SubspaceConv_Supplement_chromPoly
-- name    : SubspaceConv_Supplement_chromPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:47:41.19793+00:00
-- url     : https://prove2.me/theorems/50618cbd-82d8-421c-99a8-b597d9457026
-- title:
--   Chromatic polynomial and chromatic number
-- statement:
--   Let $G$ be a graph on $N$ vertices. For $t \ge 0$ let $a_t$ be the number of partitions of $V(G)$ into exactly $t$ nonempty independent sets. The **chromatic polynomial** is
--
--   $$P_G(z) = \sum_{t=0}^{N} a_t\, (z)_t, \qquad (z)_t = z(z-1)\cdots(z-t+1),$$
--
--   the integer polynomial whose value at every $z \in \mathbb N$ is the number of proper colorings $V(G) \to \{1, \dots, z\}$. The **chromatic number** $\chi(G)$ is the least number of colors in a proper coloring.
--
--   These are the outputs of Theorem 6, and $\chi(G)$ is the decided quantity of Theorem 8.
--
--   **Formalization Note** $a_t$ is computed as the number of proper colorings onto exactly $t$ colors divided by $t!$ (an exact division). $\chi(G)$ is Mathlib's `chromaticNumber`, which is finite for finite graphs, taken as a natural number. `properCount G z` is the number of proper maps to $z$ colors.
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4e583122875209a3e25ee95aa3a7af933526e165d47c274634e604ab2), §6, eq. (20), p.17 (PDF p.18); Theorem 6, p.16

import Mathlib

set_option autoImplicit false

open Classical

namespace SubspaceConv.Supplement

variable {N : ℕ}

/-- The number of proper maps `Fin N → Fin z` of a graph `G` (adjacent vertices get distinct
colors). -/
noncomputable def properCount (G : SimpleGraph (Fin N)) (z : ℕ) : ℕ :=
  Fintype.card {c : Fin N → Fin z // ∀ u v, G.Adj u v → c u ≠ c v}

/-- `a_t`, the number of color partitions of `G` into exactly `t` classes (Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §6, p.17
(PDF p.18): "partitions into t nonempty independent classes"), computed as the number of proper
colorings onto `Fin t` divided by `t!` (each partition with `t` classes has exactly `t!` such
colorings, so the division is exact). -/
noncomputable def partitionCount (G : SimpleGraph (Fin N)) (t : ℕ) : ℕ :=
  Fintype.card {c : Fin N → Fin t // (∀ u v, G.Adj u v → c u ≠ c v) ∧ Function.Surjective c} /
    t.factorial

/-- The **chromatic polynomial** of `G` by eq. (20) of Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), p.17 (PDF p.18):
`P_G(z) = ∑_{t=0}^{N} a_t (z)_t`, with `(z)_t = z(z − 1)⋯(z − t + 1)` the falling factorial
(Mathlib `descPochhammer ℤ t`) and `a_t` = `partitionCount G t`.

**Formalization Note** `P_G` is an integer polynomial with `P_G(z) = properCount G z` for every
`z ∈ ℕ` (the defining property of the chromatic polynomial, which pins it uniquely). -/
noncomputable def chromPoly (G : SimpleGraph (Fin N)) : Polynomial ℤ :=
  ∑ t ∈ Finset.range (N + 1), (partitionCount G t : ℤ) • descPochhammer ℤ t

/-- The **chromatic number** `χ(G)` as a natural number: Mathlib's `G.chromaticNumber : ℕ∞`,
which is finite for a graph on `Fin N` (it is at most `N`). -/
noncomputable def chromNum (G : SimpleGraph (Fin N)) : ℕ :=
  G.chromaticNumber.toNat

end SubspaceConv.Supplement


