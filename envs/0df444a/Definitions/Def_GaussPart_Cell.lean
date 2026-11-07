-- Prove2me | Definitions.Def_GaussPart_Cell
-- name    : GaussPart_Cell
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:15.52319+00:00
-- url     : https://prove2.me/theorems/358899eb-3104-44e8-a6a1-c6df0b0e2c6e
-- title:
--   Polyhedral cells, their point sets and constraint subspaces
-- statement:
--   Points are vectors of $\mathbb R^d$ with the Euclidean inner product. A **constraint** is a triple $(w,b,s)$ with $w\in\mathbb R^d$, $b\in\mathbb R$ and a flag $s$; it reads $w\cdot x\le b$ when $s$ is false and $w\cdot x<b$ when $s$ is true. A **polyhedral cell** $R$ is a finite list of constraints, and its point set is the set of $x$ satisfying all of them (the empty list is all of $\mathbb R^d$). The **constraint subspace** of $R$ is
--   $$V_R=\operatorname{span}\{w : (w,b,s)\in R\},$$
--   the span of the normals of the listed constraints.
--
--   These are the cells of the partitions built by the Gaussian partitioning algorithm; certified cells are thin in $V_R$ and unrestricted on $V_R^\perp$.
--
--   **Formalization Note** Section 2 prints only "$\le$" constraints, while Definition 3.4 cuts the line into half-open intervals, so a cell may also carry strict constraints. A cell is its list, not its point set: $V_R$ depends on the representation, as on the page, and a redundant constraint enlarges it.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), §2, p.13 (PDF p.15); Definition 3.4, p.16 (PDF p.18)

import Mathlib

open scoped RealInnerProductSpace

namespace GaussPart

/-- Points of `ℝᵈ` with the Euclidean inner product. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- One defining inequality of a polyhedral cell: `w · x ≤ b` (`strict = false`) or `w · x < b`
(`strict = true`). -/
structure Constraint (d : ℕ) where
  normal : Vec d
  bound : ℝ
  strict : Bool

/-- `x` satisfies the constraint. -/
def Constraint.Holds {d : ℕ} (c : Constraint d) (x : Vec d) : Prop :=
  if c.strict then ⟪c.normal, x⟫ < c.bound else ⟪c.normal, x⟫ ≤ c.bound

/-- **Polyhedral cell** (§2, p.13, PDF p.15; Definition 3.4, p.16, PDF p.18 of arXiv:2611.05264,
sha256 7e0ca6d4…): a finite list of constraints.

**Formalization Note.** §2 prints only `w⁽ⁱ⁾ · x ≤ bᵢ`, while Definition 3.4 cuts `ℝ` into half-open
intervals, so a cell also carries strict inequalities. A cell is its constraint list, not its point
set: `V_R` below depends on the list, as on the page, and a redundant constraint enlarges `V_R`. -/
abbrev Cell (d : ℕ) := List (Constraint d)

/-- The point set of a cell: all constraints hold. The empty list is all of `ℝᵈ`. -/
def cellSet {d : ℕ} (R : Cell d) : Set (Vec d) := {x | ∀ c ∈ R, c.Holds x}

/-- `V_R = span(w⁽¹⁾, …, w⁽ᵐ⁾)`, the span of the normals of the listed constraints (§2, p.13). -/
def constraintSpace {d : ℕ} (R : Cell d) : Submodule ℝ (Vec d) :=
  Submodule.span ℝ {w | ∃ c ∈ R, c.normal = w}

end GaussPart


