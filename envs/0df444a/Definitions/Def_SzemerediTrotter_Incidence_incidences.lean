-- Prove2me | Definitions.Def_SzemerediTrotter_Incidence_incidences
-- name    : SzemerediTrotter_Incidence_incidences
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T10:45:32.571055+00:00
-- url     : https://prove2.me/theorems/629bab74-39b4-4dae-9903-07c85cbc7f30
-- title:
--   Lines in the plane, degrees, densities and the incidence count $I(\mathcal P,\mathcal L)$
-- statement:
--   Let $\mathbb R^2$ denote the Euclidean plane. A **line** is an affine subspace $l \subseteq \mathbb R^2$ whose direction space is one-dimensional; equivalently $l = \{a + \lambda v : \lambda \in \mathbb R\}$ for a point $a$ and a nonzero vector $v$.
--
--   Let $\mathcal P$ be a finite set of $n$ points and $\mathcal L$ a finite family of $t$ distinct lines. The **number of incidences** between $\mathcal P$ and $\mathcal L$ is
--
--   $$I(\mathcal P,\mathcal L) = \#\{(p,l) \in \mathcal P \times \mathcal L : p \in l\}.$$
--
--   The **degree** of a point $p$ is the number $d(p) = \#\{l \in \mathcal L : p \in l\}$ of lines of $\mathcal L$ through $p$, and the **density** of a line $l$ is the number $y(l) = \#\{p \in \mathcal P : p \in l\}$ of points of $\mathcal P$ on $l$. Counting the incidences by points or by lines gives $I = \sum_{p} d(p) = \sum_{l} y(l)$.
--
--   These are the objects of Szemerédi and Trotter's Section 3, where the points are labelled $p_1,\dots,p_n$, the lines $l_1,\dots,l_t$, and $d_i$, $y_j$ denote the degree of $p_i$ and the density of $l_j$.
--
--   **Formalization Note** The plane is `EuclideanSpace ℝ (Fin 2)` (abbreviated `Plane`). A line is an `AffineSubspace ℝ Plane` whose `direction` has `Module.finrank` equal to $1$ (predicate `IsLine`); the definitions of the counts themselves accept any affine subspaces, and every theorem that uses them requires `IsLine` of each member of $\mathcal L$. The point set is a `Finset Plane` and the line family a `Finset (AffineSubspace ℝ Plane)`, which makes the lines distinct. Membership of a point in an affine subspace is not decidable, so the counts are `Finset.filter` cardinalities under classical decidability.
-- source:
--   Szemerédi, Trotter, Extremal Problems in Discrete Geometry, Combinatorica 3 (1983), p. 383, Section 3 (degree dᵢ, density yⱼ, incidence count I); lines in the Euclidean plane, Theorem 1, p. 381

import Mathlib

namespace SzemerediTrotter.Incidence

open Classical

/-- The Euclidean plane `ℝ²`; the coordinates of `x : Plane` are `x 0` and `x 1`. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- A line of the plane: an affine subspace whose direction is one-dimensional. -/
def IsLine (l : AffineSubspace ℝ Plane) : Prop :=
  Module.finrank ℝ l.direction = 1

/-- The number of incidences `I(𝒫, ℒ)`: pairs `(p, l) ∈ 𝒫 × ℒ` with `p ∈ l`. -/
noncomputable def incidences (P : Finset Plane) (L : Finset (AffineSubspace ℝ Plane)) : ℕ :=
  ((P ×ˢ L).filter (fun x => x.1 ∈ x.2)).card

/-- The degree of a point `p`: the number of members of `ℒ` that contain `p`. -/
noncomputable def degree (L : Finset (AffineSubspace ℝ Plane)) (p : Plane) : ℕ :=
  (L.filter (fun l => p ∈ l)).card

/-- The density of a line `l`: the number of points of `𝒫` that lie on `l`. -/
noncomputable def density (P : Finset Plane) (l : AffineSubspace ℝ Plane) : ℕ :=
  (P.filter (fun p => p ∈ l)).card

end SzemerediTrotter.Incidence


