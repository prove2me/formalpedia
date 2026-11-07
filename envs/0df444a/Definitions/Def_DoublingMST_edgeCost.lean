-- Prove2me | Definitions.Def_DoublingMST_edgeCost
-- name    : DoublingMST_edgeCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:26:30.197911+00:00
-- url     : https://prove2.me/theorems/43fc5e41-8722-445a-94be-1b6dbebbae74
-- title:
--   Edge weight $w(e)$
-- statement:
--   The weight of an edge $e=\{x,y\}$ is $w(e)=d(x,y)$.
--
--   **Formalization Note** Computed as $\min(d(x,y),d(y,x))$, which is well defined on unordered pairs and equals $d(x,y)$ for a metric.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), §4.2, p.19 (PDF p.21)

import Mathlib

namespace DoublingMST

/-- **Edge weight.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), §4.2, p.19 (PDF p.21): "w(e) = d(x, y) for e = (x, y)".

**Formalization Note.** On an unordered pair `s(x, y)` the weight is `min (d x y) (d y x)`, which
is well defined on `Sym2` without a symmetry hypothesis and equals `d x y` for a metric. -/
def edgeCost {n : ℕ} (d : Fin n → Fin n → ℝ) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun x y => min (d x y) (d y x), fun _ _ => min_comm _ _⟩

end DoublingMST


