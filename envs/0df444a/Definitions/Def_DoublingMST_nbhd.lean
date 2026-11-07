-- Prove2me | Definitions.Def_DoublingMST_nbhd
-- name    : DoublingMST_nbhd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:24:16.73077+00:00
-- url     : https://prove2.me/theorems/84f048f6-94b0-48a5-9ccb-9b78755bbc4f
-- title:
--   Neighbourhood $B(S,r)$ of a set
-- statement:
--   For $S\subseteq X$, the **$r$-neighbourhood** is $B(S,r)=\bigcup_{x\in S}B(x,r)$, the set of points within distance $r$ of some point of $S$.
--
--   For nonempty $S$, $y\in B(S,r)$ is the condition $d(y,S)\le r$ with $d(y,S)=\min_{x\in S}d(y,x)$; for $S=\emptyset$ the neighbourhood is empty. Statements write "$d(u,T)\le r$" as $u\in B(T,r)$.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), §2, pp.11–12 (PDF pp.13–14)

import Mathlib
open scoped Classical

namespace DoublingMST

/-- **The `r`-neighbourhood of a set.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), §2, p.11 (PDF p.13): "The r-neighborhood of a subset S ⊆ X is defined as
B(S, r) := ⋃_{x∈S} B(x, r)."

**Formalization Note.** `y ∈ nbhd d S r` iff some `x ∈ S` has `d x y ≤ r`. For a nonempty `S`
this is `d(y, S) ≤ r` in the paper's notation `d(y, S) := min_{x∈S} d(y, x)`; for `S = ∅` it is
empty, matching `min ∅ = +∞`. Statements write `d(u, T) ≤ r` as `u ∈ nbhd d T r`. -/
noncomputable def nbhd {n : ℕ} (d : Fin n → Fin n → ℝ) (S : Finset (Fin n)) (r : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun y => ∃ x ∈ S, d x y ≤ r

end DoublingMST


