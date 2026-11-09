-- Prove2me | Definitions.Def_SkipListConc_IsPromotionNoise
-- name    : SkipListConc_IsPromotionNoise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:06.340502+00:00
-- url     : https://prove2.me/theorems/73d55a91-2c70-495b-acef-98f4fda562e5
-- title:
--   Randomness of the height-based promotion rule (Definition 1.1)
-- statement:
--   Fix $0<p<1$ and an integer $K\ge 1$. In the **height-based promotion rule** (Definition 1.1), an access to an item of current height $c\ge 1$ (i) opens a gate with probability $p^{c}$, and if it opens (ii) draws a jump $J_c\in\{1,\dots,K\}$ whose law may depend on $c$ only and (iii) an independent $G\sim\mathrm{Geom}_0(1-p)$, and sets $c\leftarrow c+J_c+G$. An insertion sets the initial height $J_0+G_0$. All variables are fresh at each update, independent across updates and across items.
--
--   This definition says what a probability space $(\Omega,P)$ must carry to run the rule: for every item $x$ and operation index $j$ one draw $\xi(x,j)=(U,J,G)$, where $U$ is uniform on $[0,1]$ (the gate opens when $U\le p^{c}$), $J:\mathbb N\to\{0,\dots,K-1\}$ is a jump table (the jump at source height $c$ is $J(c)+1$, and $J(0)+1$ is the insertion jump), and $G\sim\mathrm{Geom}_0(1-p)$. The three components are independent, with law $\mathrm{Uniform}[0,1]\otimes\mu_J\otimes\mathrm{Geom}_0(1-p)$ for an arbitrary probability law $\mu_J$ of jump tables, and the draws are mutually independent over all pairs $(x,j)$.
--
--   **Formalization Note** One law $\mu_J$ for all draws encodes "the distribution of $J_c$ may depend on $c$ but on nothing else": update $j$ reads only coordinate $c$ of its table. Jumps lie in $\{1,\dots,K\}$ on every outcome.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Definition 1.1, pp.5–6

import Mathlib
import Definitions.Def_SkipListConc_geom0

open MeasureTheory ProbabilityTheory

namespace SkipListConc

/-- The randomness of the height-based promotion rule, Definition 1.1 (Kapoor–Tanveer,
*Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript
(sha256 f82c3d35…6dab6c), Definition 1.1, pp.5–6).

For every item `x` and operation index `j` (the `j`-th operation on `x`) there is one draw
`ξ (x, j) = (U, J, G)`: a gate uniform `U ∼ Uniform[0,1]`, a jump table `J : ℕ → Fin K` (the jump
at source height `c` is `J c + 1 ∈ {1, …, K}`; coordinate `0` is the insertion jump `J₀`), and
`G ∼ Geom₀(1 − p)`. The three components are independent (product law), the draws are
independent across all `(x, j)` (`iIndepFun`), and every draw has the same law, the jump law `μJ`
being arbitrary.

**Formalization Note** "Choose `J_c` whose distribution may depend on `c` but on nothing else" is
encoded by one arbitrary probability law `μJ` on jump tables, of which update `j` reads the
coordinate `c` = the current height; the joint law of different coordinates is never used. The jump
`J c + 1` lies in `{1, …, K}` on every outcome. The gate opens when `U ≤ p^c`, an event of
probability exactly `p^c`. Draws for `j = 0` exist but are never read. -/
structure IsPromotionNoise (p : ℝ) (K : ℕ) {α Ω : Type*} [MeasurableSpace Ω]
    (μJ : Measure (ℕ → Fin K)) (P : Measure Ω)
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) : Prop where
  /-- `P` is a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure P
  /-- the jump law is a probability measure -/
  isProbabilityMeasure_jump : IsProbabilityMeasure μJ
  /-- every draw is a random variable -/
  measurable : ∀ i, Measurable (ξ i)
  /-- draws are independent across items and updates -/
  indep : iIndepFun ξ P
  /-- each draw has law `Uniform[0,1] ⊗ μJ ⊗ Geom₀(1 − p)` -/
  law : ∀ i, P.map (ξ i) = (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (μJ.prod (geom0 p))

end SkipListConc


