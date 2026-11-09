-- Prove2me | Definitions.Def_MetricTSPSublinear_rdist
-- name    : MetricTSPSublinear_rdist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:27:58.671203+00:00
-- url     : https://prove2.me/theorems/a62af20d-7279-48e0-a0e3-f943b4645af4
-- title:
--   The distance $d_{R(T)}$ on the continuous extension
-- statement:
--   For a tree $T$ with nonnegative edge weights, $d_{R(T)}$ extends the tree metric $d_T$ to $R(T)$: the distance between two points is the length of the path joining them in $T$ with edges as segments of length $w_T(e)$. In particular the interior point at fraction $\alpha$ of the edge $(u,v)$ is at distance $\alpha\,w_T(e)$ from $u$ and $(1-\alpha)\,w_T(e)$ from $v$.
--
--   **Formalization Note.** The value is computed by cases: two nodes are at distance $d_T$; a node and an interior point are at the smaller of the two distances through the ends of the point's edge; two interior points of the same edge are at distance $|\alpha-\beta|\,w_T(e)$; two interior points of different edges are at the least of the four sums through an end of each edge. In a tree this is the path length. With zero-weight edges it is a pseudometric, as is the paper's $R(C)$ when $C$ has such edges.
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §3, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_TreeCoverLB_WeightedTree
import Definitions.Def_MetricTSPSublinear_RPoint

namespace MetricTSPSublinear

/-- **The distance `d_{R(T)}` of the continuous extension of a weighted tree.**
Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §3, p.10 (PDF p.12): "We use R(T) to denote the continuous extension of this tree metric. … for
edge e = (u, v) and α ∈ (0, 1), there is an interior point p on e that satisfies d_{R(T)}(u, p) = α w_T(e) and
d_{R(T)}(v, p) = (1 − α) w_T(e). We use d_{R(T)}(·, ·) and d_T(·, ·) interchangeably."

For a weighted tree `T` (the published `TreeCoverLB.WeightedTree`; `T.dist` is the tree metric on nodes):
* two nodes are at distance `d_T(a, b)`;
* a node `c` and the point at fraction `α` of the edge `{a, b}` are at distance
  `min (α w + d_T(a, c)) ((1 − α) w + d_T(b, c))`, `w = T.w {a, b}`;
* two interior points of the same edge are at distance `|α − β| w`;
* two interior points of different edges `{a, b}`, `{c, d}` are at the least of the four sums
  (offset to an end of the first edge) + (tree distance between the ends) + (offset from an end of the second edge).

**Formalization Note.** In a tree the geodesic between points of different edges leaves the first edge through one
of its ends and enters the second through one of its ends, so with nonnegative weights the minimum over the four
choices is the length of the path in `R(T)`. With zero-weight edges this is a pseudometric, as the page's `R(C)` is
when `C` has such edges. -/
noncomputable def rdist {m : ℕ} (T : TreeCoverLB.WeightedTree (Fin m)) :
    RPoint T.G → RPoint T.G → ℝ
  | .vtx a, .vtx b => T.dist a b
  | .vtx c, .inner a b _ _ α _ =>
      min (α * T.w s(a, b) + T.dist a c) ((1 - α) * T.w s(a, b) + T.dist b c)
  | .inner a b _ _ α _, .vtx c =>
      min (α * T.w s(a, b) + T.dist a c) ((1 - α) * T.w s(a, b) + T.dist b c)
  | .inner a b _ _ α _, .inner c d _ _ β _ =>
      if a = c ∧ b = d then |α - β| * T.w s(a, b)
      else min
        (min (α * T.w s(a, b) + T.dist a c + β * T.w s(c, d))
             (α * T.w s(a, b) + T.dist a d + (1 - β) * T.w s(c, d)))
        (min ((1 - α) * T.w s(a, b) + T.dist b c + β * T.w s(c, d))
             ((1 - α) * T.w s(a, b) + T.dist b d + (1 - β) * T.w s(c, d)))

end MetricTSPSublinear


