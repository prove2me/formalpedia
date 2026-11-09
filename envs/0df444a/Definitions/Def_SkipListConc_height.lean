-- Prove2me | Definitions.Def_SkipListConc_height
-- name    : SkipListConc_height
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:55.841303+00:00
-- url     : https://prove2.me/theorems/7b08ef61-d542-422f-b055-b4752e16c192
-- title:
--   Height process $H_x(j)$ of the promotion rule
-- statement:
--   Given a realization $\xi$ of the promotion randomness, the **height process** of item $x$ is
--   $$
--   H_x(0)=1,\qquad H_x(1)=(J_{(x,1)}(0)+1)+G_{(x,1)},
--   $$
--   and for $j\ge 1$, writing $c=H_x(j)$ and $(U,J,G)=\xi(x,j+1)$,
--   $$
--   H_x(j+1)=\begin{cases} c+(J(c)+1)+G, & U\le p^{c},\\ c, & \text{otherwise.}\end{cases}
--   $$
--   So $H_x(j)$ is the height of $x$ after its $j$-th operation; $H_x(0)=1$ is the paper's convention for the search performed by an insertion. Heights are at least $1$ and never decrease.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Definition 1.1, pp.5–6; §1.1, p.5

import Mathlib

namespace SkipListConc

/-- The height process `H_x(j)` of item `x` under the height-based promotion rule, Definition 1.1
(Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), Definition 1.1, pp.5–6, and §1.1, p.5).

`height p ξ x j ω` is the height of `x` after its `j`-th operation, with the draw
`ξ (x, j) ω = (U, J, G)` of that operation:
* `H_x(0) = 1` (the paper's convention for the search of an insertion, p.5);
* `H_x(1) = (J 0 + 1) + G` (insertion: `J₀ + G₀`);
* for `j ≥ 1`, with `c = H_x(j)`: `H_x(j+1) = c + (J c + 1) + G` if `U ≤ p^c` (the gate opens),
  and `H_x(j+1) = c` otherwise.

**Formalization Note** The jump at source height `c` is `J c + 1 ∈ {1, …, K}`. The gate test reads
the height before the update. -/
noncomputable def height (p : ℝ) {K : ℕ} {α Ω : Type*}
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (x : α) : ℕ → Ω → ℕ
  | 0, _ => 1
  | 1, ω => (((ξ (x, 1) ω).2.1 0 : ℕ) + 1) + (ξ (x, 1) ω).2.2
  | j + 2, ω =>
      if (ξ (x, j + 2) ω).1 ≤ p ^ height p ξ x (j + 1) ω then
        height p ξ x (j + 1) ω + (((ξ (x, j + 2) ω).2.1 (height p ξ x (j + 1) ω) : ℕ) + 1)
          + (ξ (x, j + 2) ω).2.2
      else height p ξ x (j + 1) ω

end SkipListConc


