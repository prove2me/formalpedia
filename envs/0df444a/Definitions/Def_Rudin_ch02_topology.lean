-- Prove2me | Definitions.Def_Rudin_ch02_topology
-- name    : Rudin_ch02_topology
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-12T18:44:40.922855+00:00
-- url     : https://prove2.me/theorems/4a9d94a0-3465-428c-9585-04c29be70375
-- title:
--   Limit points, open-cover compactness, and $k$-cells
-- statement:
--   Three notions from Rudin's Chapter 2 that have no directly reusable counterpart in Mathlib in his exact shape. (i) $p$ is a **limit point** of $E$ if every neighbourhood of $p$ contains a point $q \in E$ with $q \ne p$ (Definition 2.18(b)); note that this is strictly stronger than $p \in \bar E$, since isolated points of $E$ are excluded. (ii) $K$ is **compact** if every family of open sets whose union contains $K$ has a finite subfamily whose union still contains $K$ (Definitions 2.31, 2.32). (iii) The **$k$-cell** determined by $a, b \in \mathbb{R}^k$ is $\{x : a_j \le x_j \le b_j \text{ for all } j\}$ (Section 2.17). All other notions of the chapter — open, closed, closure, perfect, bounded, connected — are taken from Mathlib.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 2, pp. 31-36, Section 2.17, Definitions 2.18, 2.31, 2.32

import Mathlib

/-!
# Rudin, Chapter 2 — metric-space vocabulary

Definitions transcribed from Walter Rudin, *Principles of Mathematical Analysis*, 3rd edition,
Chapter 2 (Definitions 2.18, 2.31, 2.32 and Section 2.17).

Mathlib's `Metric.ball`, `IsOpen`, `IsClosed`, `closure`, `interior`, `Perfect`, `IsCompact`,
`IsConnected` and `Bornology.IsBounded` are the same notions Rudin defines in 2.18, 2.26,
2.32 and 2.45, and are reused.  Three items have no directly reusable Mathlib counterpart in
Rudin's exact shape and are introduced here: his metric-space notion of *limit point*, his
*open-cover* definition of compactness (Mathlib's `IsCompact` is the filter formulation, and
the agreement of the two is itself one of the mission's milestones), and the *k-cell*.
-/

namespace Rudin

variable {X : Type*} [MetricSpace X]

/-- Rudin, Definition 2.18(b): `p` is a **limit point** of the set `E` if every neighbourhood
of `p` contains a point `q ≠ p` with `q ∈ E`. -/
def IsLimitPoint (p : X) (E : Set X) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ q ∈ E, q ≠ p ∧ dist q p < r

/-- Rudin, Definitions 2.31 and 2.32: `K` is **compact** if every open cover of `K` contains a
finite subcover.  A cover is given here as a family `𝒢` of open sets whose union contains `K`,
and a finite subcover as a finite subfamily of `𝒢` whose union still contains `K`. -/
def IsCoverCompact (K : Set X) : Prop :=
  ∀ 𝒢 : Set (Set X), (∀ G ∈ 𝒢, IsOpen G) → K ⊆ ⋃₀ 𝒢 →
    ∃ ℱ ⊆ 𝒢, ℱ.Finite ∧ K ⊆ ⋃₀ ℱ

/-- Rudin, Section 2.17: the **k-cell** with corners `a` and `b` is the set of points
`x ∈ ℝ^k` with `a j ≤ x j ≤ b j` for every coordinate `j`. -/
def kCell (k : ℕ) (a b : Fin k → ℝ) : Set (EuclideanSpace ℝ (Fin k)) :=
  {x | ∀ j, a j ≤ x j ∧ x j ≤ b j}

end Rudin


