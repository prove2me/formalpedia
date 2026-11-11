-- Prove2me | Definitions.Def_ProdMomentConc_kSubsetLaw
-- name    : ProdMomentConc_kSubsetLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:12:16.263148+00:00
-- url     : https://prove2.me/theorems/81cea281-5ed1-425b-8aa9-e758d8c31df8
-- title:
--   The law of a uniformly random $k$-subset of $[n]$
-- statement:
--   For integers $0 \le k \le n$, the **uniformly random $k$-subset** $I$ of $[n]$ has the law that gives each subset $S \subseteq [n]$ with $|S| = k$ probability
--
--   $$
--   \Pr[I = S] = \binom{n}{k}^{-1}.
--   $$
--
--   Probabilities $\Pr_I[\cdot]$ and expectations $\mathbb E_I[\cdot]$ over the random subset are taken with respect to this law, on a sample space separate from the one carrying the underlying bits.
--
--   This is the "additional element of randomness" of the paper: tail bounds for a sum are obtained by averaging product moments over $I$.
--
--   **Formalization Note** It is Mathlib's `uniformOn` (normalized counting measure) on the set $\{S : |S| = k\}$ of `Finset (Fin n)`. For $k > n$ the set is empty and the measure is $0$; every statement of the mission assumes $k \le n$.
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), Lemma 2.3, p.9 (PDF p.9), and §3.2, p.15 ("let I ⊆ [n] be a subset of size k sampled uniformly at random")

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ProdMomentConc

/-- **The law of a uniformly random `k`-subset of `[n]`.**
Saks, Srinivasan, Valieva, arXiv:2608.04125 (held version, sha256 5218e9d0…), Lemma 2.3, p.9 ("Let
I be a uniformly random k-subset of [n]") and §3.2, p.15 ("let I ⊆ [n] be a subset of size k
sampled uniformly at random").

The uniform probability measure on the subsets `S ⊆ Fin n` with `|S| = k`.

**Formalization Note.** Mathlib's `uniformOn` (normalized counting measure on the set) on
`Finset (Fin n)` with its standard σ-algebra, which is discrete because `Fin n` is finite. For
`k ≤ n` it is a probability measure giving each `k`-subset mass `1 / C(n, k)`; for `k > n` the set
is empty and the measure is `0` (every statement of this mission assumes `k ≤ n`). Probabilities
and expectations over `I` are taken with respect to this measure, on a sample space separate from
the one carrying the bits. -/
noncomputable def kSubsetLaw (n k : ℕ) : Measure (Finset (Fin n)) :=
  uniformOn {S : Finset (Fin n) | S.card = k}

end ProdMomentConc


