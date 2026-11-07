-- Prove2me | Definitions.Def_GaussPart_IsGoodOutput
-- name    : GaussPart_IsGoodOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:10.538204+00:00
-- url     : https://prove2.me/theorems/e1981688-8783-4e7e-aa11-b6cc18f7ff71
-- title:
--   The output guarantee of the Gaussian partitioning theorem
-- statement:
--   Let $P=N(0,I_d)$, $Q$ a probability measure on $\mathbb R^d$, $k\in\mathbb N$, and $\eta,\delta,\Delta,B$ reals. A list $L$ of cells with flags (the flagged cells form $\mathcal G$, all cells form $\mathcal U$) is a **good output** if
--   1. the point sets of the cells are pairwise disjoint and cover $\mathbb R^d$;
--   2. $|\mathcal U|\le B$ and $Q\big(\bigcup_{R\in\mathcal G}R\big)\ge 1-\eta$;
--   3. every $R\in\mathcal G$ satisfies (i) $Q(R)\ge 1/B$, (ii) $\|\mathrm{proj}_{V_R}x-\mathrm{proj}_{V_R}y\|\le\delta$ for all $x,y\in R$, i.e. $\operatorname{diam}(R)\le\delta$ measured in $V_R$, and (iii) $P\mid R$ and $Q\mid R$ match their first $k$ directional moments on $V_R^\perp$ with slack $\Delta$.
--
--   **Formalization Note** The diameter clause is written for all pairs of points rather than with a supremum, so an unbounded cell cannot pass it by a default value. Conditional laws are `ProbabilityTheory.cond`; a certified cell has $Q(R)\ge1/B>0$, and smoothness then gives $P(R)>0$.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Theorem 3.1, p.14 (PDF p.16); §2, p.13

import Mathlib
import Definitions.Def_GaussPart_Cell
import Definitions.Def_GaussPart_MatchesMoments

open MeasureTheory ProbabilityTheory

namespace GaussPart

/-- The point sets of the listed cells are pairwise disjoint (by list position) and cover `ℝᵈ`.
An empty cell is allowed. -/
def IsPartition {d : ℕ} (U : List (Cell d)) : Prop :=
  (U.map cellSet).Pairwise Disjoint ∧ ∀ x : Vec d, ∃ R ∈ U, x ∈ cellSet R

/-- `diam(R) ≤ δ`, with the diameter measured in `V_R` (§2, p.13):
`‖proj_{V_R} x − proj_{V_R} y‖ ≤ δ` for all `x, y ∈ R`.

**Formalization Note.** This is the universally quantified form, not `Metric.diam`, which would be
`0` on an unbounded set. -/
def DiamLE {d : ℕ} (R : Cell d) (δ : ℝ) : Prop :=
  ∀ x ∈ cellSet R, ∀ y ∈ cellSet R,
    ‖(constraintSpace R).starProjection x - (constraintSpace R).starProjection y‖ ≤ δ

/-- The output guarantee of **Theorem 3.1**, arXiv:2611.05264 (sha256 7e0ca6d4…), p.14 (PDF p.16),
with `P = N(0, I_d)`: the list `L` of cells, each with a certification flag (`true` means `R ∈ G`),
is a polyhedral partition with `|U| ≤ Bd` and `Q(⋃_{R∈G} R) ≥ 1 − η`, and every certified `R` has
(i) `Q(R) ≥ 1/Bd`, (ii) `diam(R) ≤ δ` in `V_R`, (iii) `P | R` and `Q | R` match their first `k`
directional moments on `V_R^⊥` with slack `Δ`.

**Formalization Note.** Conditional laws are `ProbabilityTheory.cond`. A certified cell has
`Q(R) ≥ 1/Bd > 0`, and smoothness gives `P(R) > 0`, so neither conditional law is the zero measure. -/
def IsGoodOutput {d : ℕ} (Q : Measure (Vec d)) (k : ℕ) (η δ Δ Bd : ℝ)
    (L : List (Cell d × Bool)) : Prop :=
  IsPartition (L.map Prod.fst) ∧
  (L.length : ℝ) ≤ Bd ∧
  1 - η ≤ (Q {x | ∃ e ∈ L, e.2 = true ∧ x ∈ cellSet e.1}).toReal ∧
  ∀ R : Cell d, (R, true) ∈ L →
    1 / Bd ≤ (Q (cellSet R)).toReal ∧
    DiamLE R δ ∧
    MatchesMoments (ProbabilityTheory.cond (stdGaussian (Vec d)) (cellSet R))
      (ProbabilityTheory.cond Q (cellSet R)) (constraintSpace R)ᗮ k Δ

end GaussPart


