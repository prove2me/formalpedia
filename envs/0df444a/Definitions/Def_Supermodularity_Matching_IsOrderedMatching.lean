-- Prove2me | Definitions.Def_Supermodularity_Matching_IsOrderedMatching
-- name    : Supermodularity_Matching_IsOrderedMatching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:20:14.249335+00:00
-- url     : https://prove2.me/theorems/3b3cd8c1-9876-4e2e-92ea-5e5808b8416e
-- title:
--   An ordered matching (§3.2)
-- statement:
--   A matching $x : \mathrm{Fin}\,m \to \prod_{i=1}^n X_i$ (see `IsOptimalMatching`) is
--   **ordered** if every two of its firm-assignments are comparable in the pointwise order on
--   $\prod_i X_i$:
--   $$\forall\, j, k \in \{1,\dots,m\}, \quad x^j \preceq x^k \ \text{ or } \ x^k \preceq x^j.$$
--
--   Topkis (p. 97): "A matching $x^1,\dots,x^m$ is ordered if the vectors $x^{j'}$ and $x^{j''}$
--   of worker assignments to any two distinct firms $j'$ and $j''$ are ordered; that is, if
--   either $x^{j'} \le x^{j''}$ or $x^{j''} \le x^{j'}$." Every increasing matching is ordered
--   (pairwise comparability follows from the total chain), but an ordered matching need not be
--   increasing: the $m$ vectors are only pairwise comparable, not arranged as a single chain
--   from firm $1$ to firm $m$ in that order.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 97, Section 3.2

import Mathlib

/-!
Topkis, *Supermodularity and Complementarity*, Princeton University Press, 2011,
p. 97, Section 3.2 (definition of an ordered matching).
-/

namespace Supermodularity.Matching

/-- `IsOrderedMatching x` says the matching `x : Fin m → ∀ i, X i` is *ordered*: the quality
vectors `x j'` and `x j''` assigned to any two firms `j'` and `j''` are comparable in the
pointwise (product) order on `∀ i, X i`. Every increasing matching is ordered, but an ordered
matching need not be increasing (the `m` vectors are only pairwise comparable, not one total
chain from firm `1` to firm `m`). -/
def IsOrderedMatching {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)]
    (x : Fin m → ∀ i, X i) : Prop :=
  ∀ j k : Fin m, x j ≤ x k ∨ x k ≤ x j

end Supermodularity.Matching


