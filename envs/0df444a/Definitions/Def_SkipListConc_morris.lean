-- Prove2me | Definitions.Def_SkipListConc_morris
-- name    : SkipListConc_morris
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:54.561215+00:00
-- url     : https://prove2.me/theorems/e989fdcf-1bbd-4498-b751-45b082a761d7
-- title:
--   Morris unit-promotion chain $M_x(j)$ (Definition 2.4)
-- statement:
--   The **Morris unit-promotion chain** of item $x$ (Definition 2.4) is indexed by the operations on $x$: $M_x(1)=1$ and, for $j\ge 2$, $M_x(j)=M_x(j-1)+1$ with probability $p^{M_x(j-1)}$ and $M_x(j)=M_x(j-1)$ otherwise; also $M_x(0)=1$.
--
--   It is coupled to the height process through one shared uniform per update (proof of Lemma 2.5): with $U$ the gate uniform of the $(j+1)$-th operation on $x$, $M_x(j+1)=M_x(j)+1$ if $U\le p^{M_x(j)}$ and $M_x(j+1)=M_x(j)$ otherwise.
--
--   **Formalization Note** Under the promotion noise each update rises with probability exactly $p^{M_x(j)}$, independently of the past, which is Definition 2.4's chain.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Definition 2.4, p.14; proof of Lemma 2.5, pp.14–15; M_x(0) = 1, p.24

import Mathlib

namespace SkipListConc

/-- The Morris unit-promotion chain `M_x(j)` coupled to the height process (Kapoor–Tanveer,
*Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript
(sha256 f82c3d35…6dab6c), Definition 2.4, p.14, with the coupling of the proof of Lemma 2.5,
pp.14–15, and `M_x(0) = 1`, p.24).

`M_x(0) = M_x(1) = 1`, and for `j ≥ 1`, `M_x(j+1) = M_x(j) + 1` if `U ≤ p^{M_x(j)}` and
`M_x(j+1) = M_x(j)` otherwise, where `U` is the gate uniform of the `(j+1)`-th operation on `x`,
the same uniform that opens the gate of the height process.

**Formalization Note** Driven by the uniforms `U = (ξ (x, j)).1` of the promotion noise, the chain
rises with probability exactly `p^{M_x(j)}` at each update, independently across updates, which is
Definition 2.4; this is the shared-uniform coupling of Lemma 2.5. -/
noncomputable def morris (p : ℝ) {K : ℕ} {α Ω : Type*}
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (x : α) : ℕ → Ω → ℕ
  | 0, _ => 1
  | 1, _ => 1
  | j + 2, ω =>
      if (ξ (x, j + 2) ω).1 ≤ p ^ morris p ξ x (j + 1) ω then morris p ξ x (j + 1) ω + 1
      else morris p ξ x (j + 1) ω

end SkipListConc


