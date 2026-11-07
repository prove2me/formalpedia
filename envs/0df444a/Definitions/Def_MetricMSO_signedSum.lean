-- Prove2me | Definitions.Def_MetricMSO_signedSum
-- name    : MetricMSO_signedSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:43.381455+00:00
-- url     : https://prove2.me/theorems/4921a708-e33f-4905-bf5f-811715215fd4
-- title:
--   Reference orientations and the signed sum $\delta(W)$ of a walk
-- statement:
--   A **reference orientation** chooses, independently for each edge $uv$, one of the directions $u\to v$ and $v\to u$. For $\delta:E(G)\to\mathbb Z$ and a walk $W=v_0v_1\cdots v_\ell$, the **signed sum** is
--   $$\delta(W):=\sum_{i=1}^\ell\varepsilon_i\,\delta(v_{i-1}v_i),$$
--   where $\varepsilon_i=1$ if the reference orientation of $v_{i-1}v_i$ is $v_{i-1}\to v_i$, and $\varepsilon_i=-1$ otherwise. Each traversal is counted separately, and a walk of length zero has sum zero.
--
--   **Formalization Note** An orientation is a relation `O` with `O u v → G.Adj u v` that picks exactly one direction of every edge. `δ` is a function on `Sym2 V`, of which only the values on edges are used.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), §3.2, p.20 (PDF 22)

import Mathlib

namespace MetricMSO

/-- **A reference orientation** of the edges of `G` (§3.2, p.20 (PDF 22)): "we choose, independently
for each undirected edge e = uv, one of the directions u → v and v → u, which we call its reference
orientation." A relation `O` with `O u v → uv ∈ E(G)` that picks exactly one direction of every
edge. -/
def IsRefOrientation {V : Type} (G : SimpleGraph V) (O : V → V → Prop) : Prop :=
  (∀ u v, O u v → G.Adj u v) ∧ ∀ u v, G.Adj u v → (O u v ↔ ¬ O v u)

open Classical in
/-- **The signed sum `δ(W)` of a walk**, §3.2, p.20 (PDF 22): "Given a function δ: E(G) → Z, we
interpret δ(e) as the increment in the reference direction, and −δ(e) as the increment in the
opposite direction. For a walk W = v0v1 · · · vℓ, we define its signed sum by
δ(W) := ∑_{i=1}^ℓ εi δ(vi−1vi), where εi = 1 if the reference orientation of vi−1vi is vi−1 → vi,
and εi = −1 otherwise. We count each traversal separately … and for a walk of length zero we take
the sum to be zero."

**Formalization Note** `δ` is a function on `Sym2 V`; only its values on edges are used. -/
noncomputable def signedSum {V : Type} {G : SimpleGraph V} (O : V → V → Prop) (δ : Sym2 V → ℤ) :
    {u v : V} → G.Walk u v → ℤ
  | _, _, .nil => 0
  | u, _, @SimpleGraph.Walk.cons _ _ _ w _ _ p =>
      (if O u w then δ s(u, w) else -δ s(u, w)) + signedSum O δ p

end MetricMSO


