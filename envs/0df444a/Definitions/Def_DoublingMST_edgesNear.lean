-- Prove2me | Definitions.Def_DoublingMST_edgesNear
-- name    : DoublingMST_edgesNear
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:28:04.813205+00:00
-- url     : https://prove2.me/theorems/cc6741a4-3265-4ce3-b379-43d243322526
-- title:
--   Tree edges near a set, $P\cap T^*$
-- statement:
--   For $P\subseteq X$ and an edge set $T$, $P\cap T=\{e\in T: e\text{ has at least one endpoint in }P\}$.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), §4.2, p.19 (PDF p.21)

import Mathlib
open scoped Classical

namespace DoublingMST

/-- **Tree edges near a set, P ∩ T\*.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), §4.2, p.19 (PDF p.21): "For a subset P ⊆ X, we slightly abuse notation and write
P ∩ T* := {e ∈ T* : e has at least one endpoint in P}." -/
noncomputable def edgesNear {n : ℕ} (P : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) : Finset (Sym2 (Fin n)) :=
  T.filter fun e => ∃ x ∈ e, x ∈ P

end DoublingMST


