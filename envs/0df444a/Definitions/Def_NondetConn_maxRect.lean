-- Prove2me | Definitions.Def_NondetConn_maxRect
-- name    : NondetConn_maxRect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:26:22.105923+00:00
-- url     : https://prove2.me/theorems/7b6dcbc9-c514-4210-90d4-29abffc877ec
-- title:
--   Size of the largest 1-monochromatic rectangle of $\mathsf{bConn}_N$
-- statement:
--   For $n \ge 0$, let $\mathrm{maxRect}(n)$ be the largest value of $|\mathcal A| \cdot |\mathcal B|$ over sets $\mathcal A, \mathcal B \subseteq P_n$ of permutations of $[n]$ with $\mathsf{bConn}_N(a,b) = 1$ for all $a \in \mathcal A$, $b \in \mathcal B$ ($N = 2n$):
--   $$
--   \mathrm{maxRect}(n) = \max_{\mathcal A \times \mathcal B \subseteq \mathsf{bConn}_N^{-1}(1)} |\mathcal A|\cdot|\mathcal B| .
--   $$
--
--   This is $2^{S_n}$ in the paper's notation.
--
--   **Formalization Note** The maximum runs over all pairs of finite sets of permutations, including empty ones; since a 1-input exists for every $n$, the maximum is at least $1$ and equals the maximum over nonempty rectangles.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), proof of Theorem 4.1, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_NondetConn_bConn

namespace NondetConn

/-- **Largest 1-monochromatic rectangle of `bConn`** (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac),
proof of Theorem 4.1, p.9): the maximum of `|𝒜| · |ℬ|` over pairs of sets
`𝒜, ℬ ⊆ P_n` of permutations of `[n]` with `bConn(a, b)` for every `a ∈ 𝒜`, `b ∈ ℬ`.

**Formalization Note** A maximum over the finite set of all pairs of finsets of permutations of
`Fin n` (`Finset.sup`). The pair `(∅, ∅)` contributes `0`, and the pair of singletons of a
1-input contributes `1` (1-inputs exist for every `n`), so this is the paper's maximum over
nonempty rectangles. -/
def maxRect (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Equiv.Perm (Fin n)) × Finset (Equiv.Perm (Fin n)))).filter
      (fun p => ∀ a ∈ p.1, ∀ b ∈ p.2, bConn n a b)).sup (fun p => p.1.card * p.2.card)

end NondetConn


