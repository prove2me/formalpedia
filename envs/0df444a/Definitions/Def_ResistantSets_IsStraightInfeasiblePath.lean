-- Prove2me | Definitions.Def_ResistantSets_IsStraightInfeasiblePath
-- name    : ResistantSets_IsStraightInfeasiblePath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:26:16.458868+00:00
-- url     : https://prove2.me/theorems/2691d569-2771-4e18-844f-cc8cee1d884e
-- title:
--   Straight infeasible path in the skeleton graph $G_n$
-- statement:
--   The **skeleton graph** $G_n$ has vertex set $\{0,1\}^n$, two points being adjacent when they differ in exactly one coordinate. Write $\operatorname{dist}(a,b)$ for the Hamming distance. An $(a,b)$-path of $G_n$ is **straight** if its length is exactly $\operatorname{dist}(a,b)$; for $S\subseteq\{0,1\}^n$, a path of $G_n[\overline S]$ is **infeasible**.
--
--   By Remark 4.2 the straight paths starting at $a$ of length $\ell$ are exactly
--   $$
--   (a,\ a\triangle e_{i_1},\ a\triangle e_{i_1}\triangle e_{i_2},\ \dots,\ a\triangle e_{i_1}\triangle\cdots\triangle e_{i_\ell})
--   $$
--   for distinct coordinates $i_1,\dots,i_\ell$. A straight infeasible path is such a sequence all of whose vertices are infeasible; it has length $\ell$ and ends $a$ and $a\triangle e_{i_1}\triangle\cdots\triangle e_{i_\ell}$.
--
--   Bounds on the length of straight infeasible paths are the hypothesis of Proposition 6.1 and Theorem 6.2.
--
--   **Formalization Note** The path is given by its start $a$ and its sequence of distinct flipped coordinates `ι : Fin ℓ → Fin n` (Remark 4.2 taken as the definition); `pathVertex a ι j` is its $j$-th vertex, $0\le j\le\ell$. A path of length $0$ is a single vertex.
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, p.3 (G_n), pp.14–15 (dist, straight path, Remark 4.2, feasible/infeasible path)

import Mathlib
import Definitions.Def_ResistantSets_twist

namespace ResistantSets

/-- The set `{i₁, …, i_j}` of the first `j` coordinates of a coordinate sequence
`ι = (i₁, …, i_ℓ)` (stored 0-indexed: positions `p < j`). -/
def seqPrefix {n ℓ : ℕ} (ι : Fin ℓ → Fin n) (j : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter fun p : Fin ℓ => p.val < j).image ι

/-- The `j`-th vertex `a △ e_{i₁} △ ⋯ △ e_{i_j}` (`0 ≤ j ≤ ℓ`) of the walk from `a` that flips
the coordinates `i₁, …, i_ℓ` in this order. -/
def pathVertex {n ℓ : ℕ} (a : Fin n → Bool) (ι : Fin ℓ → Fin n) (j : ℕ) : Fin n → Bool :=
  vxor a (chi (seqPrefix ι j))

/-- **Straight infeasible path** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §4, pp.14–15). The skeleton graph `Gₙ` has vertex set
`{0,1}ⁿ`, two points being adjacent if they differ in exactly one coordinate (p.3); "An
(a, b)-path of Gn is straight if it has length exactly dist(a, b)" (p.14), `dist` being the
Hamming distance; "a path in Gn[S̄] is called an infeasible path" (p.15). By Remark 4.2 (p.15) the
straight paths from `a` of length `ℓ` are exactly `(a, a△e_{i₁}, …, a△e_{i₁}△⋯△e_{i_ℓ})` for
distinct coordinates `i₁, …, i_ℓ`.

`IsStraightInfeasiblePath S a ι` says that the coordinates `ι = (i₁, …, i_ℓ)` are distinct and
every vertex `pathVertex a ι j` (`0 ≤ j ≤ ℓ`) is infeasible. The path has length `ℓ` and ends
`a` and `pathVertex a ι ℓ`.

**Formalization Note** A straight path is given by its start and its sequence of distinct flipped
coordinates (Remark 4.2 taken as the definition); a path of length `0` is a single vertex. -/
def IsStraightInfeasiblePath {n ℓ : ℕ} (S : Finset (Fin n → Bool)) (a : Fin n → Bool)
    (ι : Fin ℓ → Fin n) : Prop :=
  Function.Injective ι ∧ ∀ j ≤ ℓ, pathVertex a ι j ∉ S

end ResistantSets


