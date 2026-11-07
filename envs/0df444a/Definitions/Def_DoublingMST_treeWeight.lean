-- Prove2me | Definitions.Def_DoublingMST_treeWeight
-- name    : DoublingMST_treeWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:28:12.010557+00:00
-- url     : https://prove2.me/theorems/82407995-b0d8-4186-a616-214cd94a5544
-- title:
--   Weight $w(E)$ of an edge set
-- statement:
--   For a finite set $E$ of edges, $w(E)=\sum_{e\in E}w(e)$.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), §4.2, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_DoublingMST_edgeCost

namespace DoublingMST

/-- **Weight of an edge set.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), §4.2, p.19 (PDF p.21): "For every subset E ⊆ T* of edges, denote the edge weight of E as
w(E) := Σ_{e∈E} w(e)". -/
noncomputable def treeWeight {n : ℕ} (d : Fin n → Fin n → ℝ) (E : Finset (Sym2 (Fin n))) : ℝ :=
  ∑ e ∈ E, edgeCost d e

end DoublingMST


