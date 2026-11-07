-- Prove2me | Definitions.Def_DoublingMST_decodeEdges
-- name    : DoublingMST_decodeEdges
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:26:59.546787+00:00
-- url     : https://prove2.me/theorems/f3f7e1dd-5fd0-47e5-be41-be55755a6bfe
-- title:
--   Edge set named by a list of label pairs
-- statement:
--   Given the labelling $\iota$ of the points and a list of integer pairs, the **named edge set** consists of the edges $\{a,b\}$ such that $(\iota(a),\iota(b))$ occurs in the list. Pairs that are not pairs of labels name no edge.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Definition 2.1, p.11 (PDF p.13): output as a list of n − 1 pairs of point labels

import Mathlib
open scoped Classical

namespace DoublingMST

/-- **The edge set named by a list of label pairs.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Definition 2.1, p.11 (PDF p.13): "An explicit spanning tree is output as a list of n − 1
pairs of point labels stored in integer registers."

`decodeEdges ι out` is the set of unordered pairs `s(a, b)` of points such that `(ι a, ι b)` is an
entry of `out`. Entries that are not pairs of labels name no edge. -/
noncomputable def decodeEdges {n : ℕ} (ι : Fin n → ℤ) (out : List (ℤ × ℤ)) :
    Finset (Sym2 (Fin n)) :=
  Finset.univ.filter fun e => ∃ p ∈ out, ∃ a b : Fin n, ι a = p.1 ∧ ι b = p.2 ∧ e = s(a, b)

end DoublingMST


