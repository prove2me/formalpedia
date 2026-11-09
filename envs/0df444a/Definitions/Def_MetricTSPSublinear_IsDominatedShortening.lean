-- Prove2me | Definitions.Def_MetricTSPSublinear_IsDominatedShortening
-- name    : MetricTSPSublinear_IsDominatedShortening
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:26:05.591288+00:00
-- url     : https://prove2.me/theorems/64e0f120-933d-404e-8f20-5c74be1bfc4a
-- title:
--   Dominated shortenings of an MST
-- statement:
--   Let $T$ be a minimum spanning tree of a metric $d$. A **shortening** $T'$ of $T$ is a tree with the same edges whose weights satisfy
--   $$0\le w_{T'}(e)\le w_T(e)\qquad(e\in T).$$
--   It is **dominated by the metric** if $d_{T'}(u,v)\le d(u,v)$ for all vertices $u,v$. Its weight is $w(T')=\sum_{e\in T}w_{T'}(e)$.
--
--   When $D=M-K$ is small, a dominated shortening of the MST is a nearly optimal dual solution (Lemma 4.3).
--
--   **Formalization Note.** A shortening is recorded as its weight function $w'$ on the edge set of $T$; values off $T$ are irrelevant.
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §2.1, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_DoublingMST_edgeCost
import Definitions.Def_MetricTSPSublinear_treeDist

namespace MetricTSPSublinear

/-- **A dominated shortening of a spanning tree.**
Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §2.1, p.3 (PDF p.5): "Given an MST T in a metric, a shortening T′ is a tree with the same edges
whose weights satisfy 0 ≤ w_{T′}(e) ≤ w_T(e). … We say a shortening T′ is dominated by the metric if for any two
vertices u and v, it holds that d_{T′}(u, v) ≤ d(u, v)."

`IsDominatedShortening d E w'` says: `0 ≤ w' e ≤ w(e)` for every edge `e ∈ E`, where `w(e)` is the metric weight
(`DoublingMST.edgeCost d e`), and `d_{T′}(u, v) = treeDist E w' u v ≤ d u v` for all `u, v`. The weight of the
shortening is `w(T′) = ∑_{e ∈ E} w' e`.

**Formalization Note.** A shortening keeps the edge set `E` and changes only the weights, so it is recorded as the
new weight function `w'`; its values off `E` are irrelevant. -/
def IsDominatedShortening {n : ℕ} (d : Fin n → Fin n → ℝ) (E : Finset (Sym2 (Fin n)))
    (w' : Sym2 (Fin n) → ℝ) : Prop :=
  (∀ e ∈ E, 0 ≤ w' e ∧ w' e ≤ DoublingMST.edgeCost d e) ∧ ∀ u v, treeDist E w' u v ≤ d u v

end MetricTSPSublinear


