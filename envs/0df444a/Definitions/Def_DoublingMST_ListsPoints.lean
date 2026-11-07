-- Prove2me | Definitions.Def_DoublingMST_ListsPoints
-- name    : DoublingMST_ListsPoints
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:28:24.897563+00:00
-- url     : https://prove2.me/theorems/83204388-faf2-449f-b956-c4a9cfc31fac
-- title:
--   An explicit list of points in integer memory
-- statement:
--   For a pointer $p$ and a set $B$ of points: the cell at $p$ holds $|B|$, and the next $|B|$ cells hold the labels of the points of $B$, each once and in any order.
--
--   This represents a ball in the output of Lemma 3.3's algorithm.
--
--   **Formalization Note** The paper fixes no layout, so this one is a convention of this formalization.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Lemma 3.3, p.15 (PDF p.17), and its proof, p.55 (PDF p.57)

import Mathlib

namespace DoublingMST

/-- **An explicit list of points in integer memory.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Lemma 3.3, p.15 (PDF p.17), and its proof, p.55 (PDF p.57): "To construct Φ from Ψ, it
suffices to construct B(u, 2^{lev(u)}) for every net point u on the net hierarchy."

`ListsPoints ι mem p B`: the cell `mem p` holds `|B|` and the next `|B|` cells hold the labels of the
points of `B`, each once, in any order.

**Formalization Note.** A fixed layout, chosen for the output of Lemma 3.3 (running time). -/
def ListsPoints {n : ℕ} (ι : Fin n → ℤ) (mem : ℤ → ℤ) (p : ℤ) (B : Finset (Fin n)) : Prop :=
  ∃ xs : List (Fin n), xs.Nodup ∧ xs.toFinset = B ∧ mem p = xs.length ∧
    ∀ j (hj : j < xs.length), mem (p + 1 + j) = ι (xs[j])

end DoublingMST


