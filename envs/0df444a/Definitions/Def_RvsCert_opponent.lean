-- Prove2me | Definitions.Def_RvsCert_opponent
-- name    : RvsCert_opponent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:38:22.298258+00:00
-- url     : https://prove2.me/theorems/4854649e-fedf-46ac-88dc-499ec32ec0ee
-- title:
--   The $j$-th opponent of a country
-- statement:
--   Each country $c\in\{0,\dots,2n-1\}$ races against the $2n-1$ other countries. They are listed in increasing order: for $j\in\{0,\dots,2n-2\}$ the $j$-th opponent of $c$ is $j$ if $j<c$ and $j+1$ otherwise. Entry $j$ of a proposal card refers to the race against the $j$-th opponent.
--
--   **Formalization Note** The paper does not fix the order of an athlete's races on the card; this fixed order is used throughout.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 2, p.2

import Mathlib

namespace RvsCert

/-- **The `j`-th opponent of country `c`** (encoding convention for the proposal card, Section 2,
p.2 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1: the card lists one number "for each race in which the athlete
participates"). The `2n − 1` opponents `d ≠ c` are listed in increasing order: `j` if `j < c`,
else `j + 1` (this is `Fin.succAbove c j`). The paper does not fix the order of the races on the
card; this is a fixed choice used consistently. -/
def opponent {n : ℕ} (c : Fin (2 * n)) (j : Fin (2 * n - 1)) : Fin (2 * n) :=
  ⟨if (j : ℕ) < c then j else j + 1, by
    have := j.isLt; have := c.isLt; split <;> omega⟩

end RvsCert


