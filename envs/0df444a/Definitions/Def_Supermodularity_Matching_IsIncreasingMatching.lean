-- Prove2me | Definitions.Def_Supermodularity_Matching_IsIncreasingMatching
-- name    : Supermodularity_Matching_IsIncreasingMatching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:19:42.140285+00:00
-- url     : https://prove2.me/theorems/f2f02ecd-2990-4704-9a2b-8ca4d4a4d344
-- title:
--   An increasing matching (§3.2)
-- statement:
--   A matching $x : \mathrm{Fin}\,m \to \prod_{i=1}^n X_i$ (see `IsOptimalMatching`) is
--   **increasing** if the quality vectors it assigns to the $m$ firms rise with the firm index:
--   $$x^j \preceq x^{j+1} \qquad \text{for } j = 1,\dots,m-1,$$
--   where $\preceq$ is the pointwise (product) order on $\prod_i X_i$ induced by each $X_i$'s
--   own lattice order. Equivalently, $x$ is monotone as a function of $j$.
--
--   Topkis (p. 96): "A matching $x^1,\dots,x^m$ is increasing if $x^j \le x^{j+1}$ for
--   $j = 1,\dots,m-1$; that is, if $x^j$ is increasing in $j$."
--
--   **Formalization Note.** Monotonicity of $x : \mathrm{Fin}\,m \to \prod_i X_i$ with respect
--   to the usual linear order on $\mathrm{Fin}\,m$ and the product (pointwise) lattice order on
--   $\prod_i X_i$ is exactly the chain condition $x^1 \preceq x^2 \preceq \cdots \preceq x^m$
--   stated pairwise by the book.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 96, Section 3.2

import Mathlib

/-!
Topkis, *Supermodularity and Complementarity*, Princeton University Press, 2011,
p. 96-97, Section 3.2 (definition of an increasing matching).
-/

namespace Supermodularity.Matching

/-- `IsIncreasingMatching x` says the matching `x : Fin m → ∀ i, X i`, which assigns to each
of `m` firms a vector of qualities of `n` worker types (one worker of each type), is
*increasing*: `x 1 ⪯ x 2 ⪯ ⋯ ⪯ x m`, i.e. `x` is monotone in the firm index `j`, with respect
to the pointwise (product) order on `∀ i, X i`. -/
def IsIncreasingMatching {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)]
    (x : Fin m → ∀ i, X i) : Prop :=
  Monotone x

end Supermodularity.Matching


