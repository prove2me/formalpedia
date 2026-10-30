-- Prove2me | Definitions.Def_NisanRonen_Rounding_unitMakespan
-- name    : NisanRonen_Rounding_unitMakespan
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:23:17.307757+00:00
-- url     : https://prove2.me/theorems/c81bbf15-a6fd-4db3-8b21-fdd0bc26d807
-- title:
--   Make-span of an allocation on a rounded instance, in $\delta$-units
-- statement:
--   For a rounded instance in $\delta$-units (task columns $c_1, \dots, c_k \in \mathbb N^n$) and an allocation given as a list of agents $(i_1, \dots, i_k)$, pair the $j$-th column with the $j$-th agent. The load of agent $i$ is $\sum_{j : i_j = i} (c_j)_i$ and
--
--   $$
--   \mathrm{unitMakespan} = \max_i \sum_{j : i_j = i} (c_j)_i .
--   $$
--
--   Multiplied by $\delta$ this is the rounded make-span $\hat g$ of the allocation on the instance. In particular the bonus $b^i = -\hat g(x, \mathrm{corr}^i)$ of the rounding mechanism is $-\delta$ times the unit make-span of the instance whose $j$-th column is constant, equal to $\lceil \mathrm{corr}^i_j / \delta \rceil$.
--
--   **Formalization Note** Unmatched entries of the two lists are dropped; the maximum is taken in $\mathbb N$.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, Definition 34, p. 193 (PDF p. 28): "b^i(t, t̃) = −ĝ(x(t̂), corr^i(x(t), t, t̃))"

import Mathlib

namespace NisanRonen.Rounding

/-- **Make-span of an allocation on a δ-unit instance** (the bonus computation of
Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001), Definition 34, p. 193, in δ-units). For an instance (list of columns
`c : Fin n → ℕ`) and an allocation (list of agents), pair the `j`-th column with the `j`-th agent;
the load of agent `i` is the sum of `c i` over the pairs `(c, i)`, and `unitMakespan` is the
largest load. Multiplied by `δ`, it is the rounded make-span `ĝ` of the allocation on the
instance; the bonus `−ĝ(x, corr^i)` is `−δ` times `unitMakespan` of the constant-column
instance of the corrected time vector.

**Formalization Note** `List.zip` drops unmatched entries; the maximum over agents is
`Finset.sup` in `ℕ` (`0` if there are no agents). -/
def unitMakespan {n : ℕ} (p : List (Fin n → ℕ) × List (Fin n)) : ℕ :=
  Finset.univ.sup fun i : Fin n =>
    (((p.1.zip p.2).filter (fun q => decide (q.2 = i))).map (fun q => q.1 i)).sum

end NisanRonen.Rounding


