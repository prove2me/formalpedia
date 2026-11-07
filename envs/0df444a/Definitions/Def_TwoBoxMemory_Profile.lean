-- Prove2me | Definitions.Def_TwoBoxMemory_Profile
-- name    : TwoBoxMemory_Profile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:33:50.745772+00:00
-- url     : https://prove2.me/theorems/976afacf-b760-4cd3-91a6-4b0a8f2861ba
-- title:
--   Repetition profile $\ell(i,j)$, $D_M$, $H_M$, $F_M$ of an infinite word
-- statement:
--   For an infinite word $W$ over $\{A,B\}$ and positions $i<j$, let
--
--   $$\ell(i,j)=\max\{n\ge0: W_{i+h}=W_{j+h}\ (0\le h<n)\}$$
--
--   be the common-prefix length of the suffixes starting at $i$ and $j$. For $M\ge1$,
--
--   $$D_M=\max_{0\le i<j\le M}\ell(i,j),\qquad H_M=\max_{0\le i<j\le M}\{j+\ell(i,j)\},\qquad F_M=M+D_M+1 .$$
--
--   $H_M$ is the longest prefix of $W$ that a deterministic lasso with $M$ labels can generate, and $F_M$ is the horizon at which the rank lower bound tests a controller.
--
--   **Formalization Note** $\ell(i,j)$ is a supremum of a set of natural numbers, which Lean evaluates to $0$ if the set is unbounded; for a word that is not eventually periodic (the greedy word of a saddle, milestone (B.10)–(B.11)) every such set is bounded. The maxima are taken over the finite set of pairs $0\le i<j\le M$, nonempty for $M\ge1$.
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), (6.3), p.9 (PDF 11); (B.5), p.22 (PDF 24)

import Mathlib

namespace TwoBoxMemory

/-!
# The repetition profile `ℓ(i, j)`, `D_M`, `H_M`, `F_M` of an infinite word

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
(6.3), p.9 (PDF 11); (B.5), p.22 (PDF 24).

For a word `W` and positions `i < j`, `ℓ(i, j) = max{n ≥ 0 : W_{i+h} = W_{j+h} (0 ≤ h < n)}` is
the common-prefix length of the suffixes starting at `i` and `j`;
`D_M = max_{0 ≤ i < j ≤ M} ℓ(i, j)`, `H_M = max_{0 ≤ i < j ≤ M} (j + ℓ(i, j))`,
`F_M = M + D_M + 1`.

**Formalization Note.**
* The definitions are stated for an arbitrary word `ℕ → Fin 2`; the paper applies them to the
  greedy word.
* `commonPrefix` is an `sSup` in `ℕ`, which is `0` for an unbounded set. For a word that is not
  eventually periodic every such set is bounded (the paper's "All these numbers are finite";
  milestone (B.10)–(B.11) proves it for the greedy word), so no junk value occurs there.
* The maxima are `Finset.sup`s over the pairs `0 ≤ i < j ≤ M`, nonempty for `M ≥ 1`; every
  statement using them assumes `M ≥ 1`.
-/

/-- `ℓ(i, j)`: the length of the common prefix of the suffixes of `W` starting at `i` and `j`. -/
noncomputable def commonPrefix (W : ℕ → Fin 2) (i j : ℕ) : ℕ :=
  sSup {n : ℕ | ∀ k < n, W (i + k) = W (j + k)}

/-- The pairs `0 ≤ i < j ≤ M`. -/
def labelPairs (M : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter fun q => q.1 < q.2

/-- `D_M = max_{0 ≤ i < j ≤ M} ℓ(i, j)`. -/
noncomputable def profD (W : ℕ → Fin 2) (M : ℕ) : ℕ :=
  (labelPairs M).sup fun q => commonPrefix W q.1 q.2

/-- `H_M = max_{0 ≤ i < j ≤ M} (j + ℓ(i, j))`. -/
noncomputable def profH (W : ℕ → Fin 2) (M : ℕ) : ℕ :=
  (labelPairs M).sup fun q => q.2 + commonPrefix W q.1 q.2

/-- `F_M = M + D_M + 1`. -/
noncomputable def profF (W : ℕ → Fin 2) (M : ℕ) : ℕ :=
  M + profD W M + 1

end TwoBoxMemory


