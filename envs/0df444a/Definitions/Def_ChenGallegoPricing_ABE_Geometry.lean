-- Prove2me | Definitions.Def_ChenGallegoPricing_ABE_Geometry
-- name    : ChenGallegoPricing_ABE_Geometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:32:24.425368+00:00
-- url     : https://prove2.me/theorems/d74c21b7-0a73-4c6a-8021-0c2e4c9e57c7
-- title:
--   Covariate geometry, rectangles and dyadic cells
-- statement:
--   The covariate space is $[0,1)^d$ with its Euclidean norm and Borel measurable structure, and the price space is $[0,1]$. A rectangle is any nonempty measurable coordinatewise product of intervals, intersected with the covariate cube; degenerate rectangles and singletons are included. Its diameter is the Euclidean diameter of its image in $\mathbb R^d$.
--
--   A dyadic cell is addressed by its level $k$ and nonnegative integer coordinate indices $a_i$. Its region is $\prod_i[a_i2^{-k},(a_i+1)2^{-k})$ inside the cube. The root has $k=0$ and all indices zero. Splitting replaces the cell by the $2^d$ cells with indices $2a_i+v_i$, $v_i\in\{0,1\}$. Raw addresses outside the cube are harmless empty cells; only valid addresses are generated from the root. Geometry itself permits $d=0$; the goal requires $d>0$.
--
--   Differences from the source: none.
-- source:
--   Chen and Gallego, Nonparametric Pricing Analytics with Customer Covariates, arXiv:1805.01136v3 (16 February 2020), https://arxiv.org/abs/1805.01136v3; §2.2 and Definition 1, printed/PDF pp. 9, 11–12

import Mathlib

open MeasureTheory

namespace ChenGallegoPricing.ABE


abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Ctx (d : ℕ) := {x : Point d // ∀ i, x i ∈ Set.Ico (0 : ℝ) 1}
abbrev Price := Set.Icc (0 : ℝ) 1

/-- All nonempty measurable axis-parallel rectangles, including degenerate ones. -/
def IsRectangle {d : ℕ} (B : Set (Ctx d)) : Prop :=
  B.Nonempty ∧ MeasurableSet B ∧ ∃ I : Fin d → Set ℝ,
    (∀ i, Set.OrdConnected (I i)) ∧ B = {x | ∀ i, x.val i ∈ I i}

/-- Euclidean diameter; rectangles here are bounded subsets of the unit cube. -/
noncomputable def diameter {d : ℕ} (B : Set (Ctx d)) : ℝ :=
  Metric.diam (Subtype.val '' B : Set (Point d))

/-- A dyadic cell is represented by its level and integer coordinate indices. -/
abbrev Cell (d : ℕ) := ℕ × (Fin d → ℕ)

def root (d : ℕ) : Cell d := (0, fun _ => 0)

noncomputable def cellSet {d : ℕ} (b : Cell d) : Set (Ctx d) :=
  {x | ∀ i, (b.2 i : ℝ) / (2 : ℝ) ^ b.1 ≤ x.val i ∧
    x.val i < ((b.2 i : ℝ) + 1) / (2 : ℝ) ^ b.1}

def child {d : ℕ} (b : Cell d) (v : Fin d → Bool) : Cell d :=
  (b.1 + 1, fun i => 2 * b.2 i + if v i then 1 else 0)

noncomputable def children {d : ℕ} (b : Cell d) : Finset (Cell d) := by
  classical
  exact Finset.univ.image (child b)

end ChenGallegoPricing.ABE


