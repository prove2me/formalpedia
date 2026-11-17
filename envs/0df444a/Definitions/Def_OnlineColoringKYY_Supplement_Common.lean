-- Prove2me | Definitions.Def_OnlineColoringKYY_Supplement_Common
-- name    : OnlineColoringKYY_Supplement_Common
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:07:29.659702+00:00
-- url     : https://prove2.me/theorems/01fcdd5a-5293-44d3-a016-7fb157a61397
-- title:
--   Prefix adjacency, fresh and eligible colors, level-$i$ colors, expected number of colors
-- statement:
--   Basic notions shared by the randomized algorithms of Section 5 and the deterministic algorithm of Section 6. The vertices $0, 1, \dots, n-1$ of a graph $G$ arrive in this order, and the vertex $v$ is colored knowing only the prefix graph $G[\{0,\dots,v\}]$.
--
--   1. **Prefix adjacency.** At the arrival of $v$, two arrived vertices $a, b \le v$ are adjacent iff they are adjacent in $G[\{0,\dots,v\}]$.
--   2. **Fresh color.** If the earlier vertices carry the colors $c(0), \dots, c(v-1) \in \mathbb N$, a fresh color is $1 + \max_u c(u)$ (or $0$ if $v = 0$): a color never used before.
--   3. **Eligible color.** A color $x$ is eligible for $v$ iff $v$ is not adjacent to any earlier vertex of color $x$.
--   4. **Level-$i$ colors.** A color currently used on exactly $i$ of the earlier vertices is a level-$i$ color. The set $E_i(v)$ collects the eligible level-$i$ colors at the arrival of $v$.
--   5. **Expected number of colors.** For a random coloring $\mu$ (a distribution over the list of colors of the vertices), the expected number of colors is
--   $$
--   \mathbb E_\mu\bigl[\,|\{c(v) : v \in V\}|\,\bigr] = \sum_{c} \mu(c)\,|\{c(0), c(1), \dots\}| .
--   $$
--
--   These notions are the vocabulary of Theorems 5.5 and 5.15.
--
--   **Formalization Note** Arrived vertices are named by natural numbers; prefix adjacency is read off the published prefix graph. The expectation is a sum in $[0,\infty]$, so it needs no integrability condition.
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Definition 3.1, Definition 3.2, printed p.10 (PDF p.12); Section 5.2, printed p.15 (PDF p.17)

import Mathlib
import Definitions.Def_OnlineColoringKYY_prefixGraph

set_option autoImplicit false

namespace OnlineColoringKYY.Supplement

open Classical

/-- Adjacency of two arrived vertices, read off the **prefix graph** at the arrival of `v`
(Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios Separating Randomized and
Deterministic Algorithms*, STOC 2027 submission (manuscript sha256 3d1eeea6…), Definition 3.1,
printed p.10 = PDF p.12).

`prefixAdj G v a b` holds iff `a, b ≤ v` and `a, b` are adjacent in `G[{0, …, v}]`, the part of
the input the online algorithm has seen when it colors `v`.

**Formalization Note** The vertices of `G : SimpleGraph (Fin n)` arrive in the order
`0, 1, …, n − 1`. Arrived vertices are named by their natural-number index. Every algorithm of the
supplement reads the graph only through `prefixAdj G v` at the arrival of `v`, so it is online by
construction. -/
def prefixAdj {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (a b : ℕ) : Prop :=
  ∃ (ha : a < v.val + 1) (hb : b < v.val + 1), (prefixGraph G v).Adj ⟨a, ha⟩ ⟨b, hb⟩

/-- A **fresh color** for a vertex arriving after the vertices colored `c` (in arrival order):
one more than the largest color used so far (`0` if nothing is colored yet), so it is never one of
the colors in `c` (Kawarabayashi–Yoneda–Yoneda, STOC 2027 submission (manuscript sha256 3d1eeea6…),
Section 5.3, printed p.15 = PDF p.17: "we assign a fresh color"). -/
def freshColor (c : List ℕ) : ℕ :=
  c.foldr (fun x m => max (x + 1) m) 0

/-- A color `x` is **eligible** for the vertex `v` arriving after the vertices `0, …, v − 1`, colored
`c` in arrival order, iff `v` is not adjacent to any earlier vertex of color `x`
(Kawarabayashi–Yoneda–Yoneda, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 5.2,
printed p.15 = PDF p.17). -/
def Eligible {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (c : List ℕ) (x : ℕ) : Prop :=
  ∀ u : ℕ, u < v.val → prefixAdj G v u v.val → c.getD u 0 ≠ x

/-- The eligible **level-`i` colors** for `v`: the colors currently used on exactly `i` of the
earlier vertices (colored `c`) that are eligible for `v` (Kawarabayashi–Yoneda–Yoneda, STOC 2027
submission (manuscript sha256 3d1eeea6…), Section 5.2, printed p.15 = PDF p.17: "a color that is
(currently) used in exactly ℓ vertices"). Levels are evaluated at the arrival of `v`. -/
noncomputable def eligibleLevel {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (c : List ℕ)
    (i : ℕ) : Finset ℕ :=
  c.toFinset.filter (fun x => c.count x = i ∧ Eligible G v c x)

/-- The **expected number of colors** `E[|{c(v) : v ∈ V}|]` of a random coloring `μ`, a
distribution over the list of colors of the vertices in arrival order
(Kawarabayashi–Yoneda–Yoneda, STOC 2027 submission (manuscript sha256 3d1eeea6…), Definition 3.2,
printed p.10 = PDF p.12: `E[ALG(I)]`, the expectation over the algorithm's randomness on a fixed
input).

**Formalization Note** The number of colors of a list `c` is the cardinality of its set of
entries. The expectation is a sum in `ℝ≥0∞`, so it needs no integrability side condition. -/
noncomputable def expColors (μ : PMF (List ℕ)) : ENNReal :=
  ∑' c, μ c * (c.toFinset.card : ENNReal)

end OnlineColoringKYY.Supplement


