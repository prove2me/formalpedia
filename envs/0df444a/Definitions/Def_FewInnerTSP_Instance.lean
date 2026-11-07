-- Prove2me | Definitions.Def_FewInnerTSP_Instance
-- name    : FewInnerTSP_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:35.564239+00:00
-- url     : https://prove2.me/theorems/33cdbf90-d69b-40e6-b39f-436899361b71
-- title:
--   Planar Euclidean TSP instances: general position, hull and interior points, tour length
-- statement:
--   An **instance** is a list of $n$ points $P_0,\dots,P_{n-1}$ in the Euclidean plane $\mathbb R^2$ (with the Euclidean distance, never the sup metric).
--
--   1. **General position**: no three points with pairwise distinct indices are collinear. For $n\ge 3$ this already forces the points to be distinct, since a repeated point makes a collinear triple.
--   2. The **hull indices** $H$ are the $i$ with $P_i$ an extreme point (a vertex) of the convex hull $\mathrm{CH}(P)$; the **interior indices** $I$ are the others, and $k=|I|$.
--   3. A **tour** is a permutation $\pi$, read as the cycle $\pi(0),\pi(1),\dots,\pi(n-1),\pi(0)$. Its **length** is
--   $$\mathrm{len}(\pi)=\sum_{i=0}^{n-1}\bigl|P_{\pi(i)}P_{\pi(i+1 \bmod n)}\bigr|,$$
--   the published cyclic sum `MetricTSP.tourCost` at Euclidean distances, and $\pi$ is **shortest** if $\mathrm{len}(\pi)\le\mathrm{len}(\tau)$ for every permutation $\tau$.
--   4. The **machine input** of an instance is the list $(n, x_0, y_0, x_1, y_1, \dots)$ of reals.
--
--   These are the objects of Theorem 1.1 and of every milestone.
--
--   **Formalization Note** The plane is `EuclideanSpace ℝ (Fin 2)`. A real-RAM program reads $n$ from its first cell by a counting loop.
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), §1, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_MetricTSP_model

namespace FewInnerTSP

/-- The Euclidean plane. Never `ℝ × ℝ`, whose `dist` is the sup metric. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- **General position.** No three points with pairwise distinct indices are collinear.
Source: Li, Ma, Gong, STOC 2027 submission (manuscript sha256 6541f631…), §1, p.1 (PDF p.3):
"n ≥ 3 distinct points with no three collinear".

**Formalization Note** For `n ≥ 3` this already gives injectivity of `P`, because a repeated point
makes a collinear triple, so no separate distinctness hypothesis is stated. -/
def GeneralPos {n : ℕ} (P : Fin n → Pt) : Prop :=
  ∀ i j l, i ≠ j → j ≠ l → i ≠ l → ¬ Collinear ℝ {P i, P j, P l}

open Classical in
/-- The indices of the hull vertices `H = vert(CH(P))`.
Source: Li, Ma, Gong, §1, p.1 (PDF p.3). -/
noncomputable def hullIdx {n : ℕ} (P : Fin n → Pt) : Finset (Fin n) :=
  Finset.univ.filter fun i => P i ∈ (convexHull ℝ (Set.range P)).extremePoints ℝ

/-- The indices of the interior points `I = P \ H`.
Source: Li, Ma, Gong, §1, p.1 (PDF p.3). -/
noncomputable def interiorIdx {n : ℕ} (P : Fin n → Pt) : Finset (Fin n) :=
  (hullIdx P)ᶜ

/-- The number `k = |I|` of (strict) interior points. Source: Li, Ma, Gong, §1, p.1 (PDF p.3). -/
noncomputable def interiorCount {n : ℕ} (P : Fin n → Pt) : ℕ :=
  (interiorIdx P).card

/-- The Euclidean length of the tour visiting `π 0, …, π (n-1), π 0`: the published cyclic sum
`MetricTSP.tourCost` at true Euclidean distances. Source: Li, Ma, Gong, §1, p.1 (PDF p.3): "Costs are
true Euclidean lengths". -/
noncomputable def tourLen {n : ℕ} (P : Fin n → Pt) (π : Equiv.Perm (Fin n)) : ℝ :=
  MetricTSP.tourCost (fun i j => dist (P i) (P j)) π

/-- `π` is a shortest Euclidean Hamiltonian cycle. Source: Li, Ma, Gong, Theorem 1.1, p.1 (PDF p.3). -/
def IsShortestTour {n : ℕ} (P : Fin n → Pt) (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ τ : Equiv.Perm (Fin n), tourLen P π ≤ tourLen P τ

/-- The coordinates of a list of indexed points, two cells per point. -/
noncomputable def coordsOf {n : ℕ} (P : Fin n → Pt) (L : List (Fin n)) : List ℝ :=
  L.flatMap fun i => [P i 0, P i 1]

/-- **The machine's input for an instance.** The real `n`, then the two coordinates of each point
in index order.

**Formalization Note** Index cells of the machine start at `0`, and there is no real-to-index cast,
so `n` is read by a counting loop in `O(n)` steps, which fits every bound below. -/
noncomputable def layout {n : ℕ} (P : Fin n → Pt) : List ℝ :=
  (n : ℝ) :: coordsOf P (List.finRange n)

end FewInnerTSP


