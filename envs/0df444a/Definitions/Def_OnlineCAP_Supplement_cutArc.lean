-- Prove2me | Definitions.Def_OnlineCAP_Supplement_cutArc
-- name    : OnlineCAP_Supplement_cutArc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:19:07.792106+00:00
-- url     : https://prove2.me/theorems/0743d8b3-c299-4eb0-9940-15bb730c1399
-- title:
--   The interval $[a,b]$ of a cut of the cycle
-- statement:
--   Order the vertices of the cycle as $v_0,v_1,\dots,v_{n-1}$. A minimum cut $C$ of the cycle separates it into two paths; the side **not containing $v_0$** is an arc $\{v_a,v_{a+1},\dots,v_b\}$ with $1\le a\le b\le n-1$, and the cut is written $C=[a,b]$.
--
--   The definition takes the side of $C$ not containing $v_0$ (that is, $C$ itself if $v_0\notin C$ and its complement otherwise) and returns the pair $(a,b)$ of its smallest and largest vertex index. This is how Algorithm 1 turns an arriving cut into the rectangles $R_L(a,b)$ and $R_T(a,b)$.
--
--   **Formalization Note** On vertex sets that are not 2-cuts of the cycle the value is an arbitrary pair (and $(0,0)$ when the side is empty); such sets never occur in a valid request sequence.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §3.1, pp.10–11 (PDF p.10–11)

import Mathlib

namespace OnlineCAP.Supplement

/-- **The side of a cycle cut not containing `v₀`.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted
and Unweighted Online Connectivity Augmentation via Geometric Hitting Set*, manuscript of Nov. 3,
2026 (sha256 e3b9cb64…), §3.1, pp.10–11 (PDF p.10–11): "A minimum cut C separates the cycle into
two paths; we choose the path that does not contain v0 to represent the cut".

`cutSide C` is the set of indices of `C` if `v₀ ∉ C`, and of its complement otherwise. -/
noncomputable def cutSide {n : ℕ} (C : Finset (Fin n)) : Finset ℕ := by
  classical
  exact if (0 : ℕ) ∈ C.image Fin.val then (Finset.univ \ C).image Fin.val else C.image Fin.val

/-- **The interval `[a, b]` of a cycle cut.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and
Unweighted Online Connectivity Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026
(sha256 e3b9cb64…), §3.1, p.11 (PDF p.11): "C = {va, va+1, . . . , vb}, where 1 ≤ a ≤ b ≤ n − 1. We
refer to this cut as C = [a, b]."

`cutArc C = (a, b)` with `a` and `b` the smallest and largest index of the side of `C` not
containing `v₀`.

**Formalization Note.** For a 2-cut of the standard cycle this side is the arc
`{v_a, …, v_b}`, `1 ≤ a ≤ b ≤ n − 1`, as on p.11. On other vertex sets (not requests of a valid
sequence) the value is a junk pair, and `(0, 0)` when the side is empty. -/
noncomputable def cutArc {n : ℕ} (C : Finset (Fin n)) : ℕ × ℕ :=
  if h : (cutSide C).Nonempty then ((cutSide C).min' h, (cutSide C).max' h) else (0, 0)

end OnlineCAP.Supplement


