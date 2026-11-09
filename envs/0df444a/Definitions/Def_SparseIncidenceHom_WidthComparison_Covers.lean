-- Prove2me | Definitions.Def_SparseIncidenceHom_WidthComparison_Covers
-- name    : SparseIncidenceHom_WidthComparison_Covers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:14.167762+00:00
-- url     : https://prove2.me/theorems/7ab96028-2cba-49a8-a367-d92967c1d4f0
-- title:
--   Real fractional edge covers and edge-dominated modular weightings
-- statement:
--   For a finite covered hypergraph $H=(V,E)$ and real vertex demands $x$, a fractional cover is a vector $y\in\mathbb R_{\ge0}^{E}$ with $\sum_{e\ni v}y_e\ge x(v)$ for every vertex. Its optimum cost is
--   $$\rho_H^*(x)=\inf\left\{\sum_{e\in E}y_e:y\ge0,\ \sum_{e\ni v}y_e\ge x(v)\ (v\in V)\right\}.$$
--   The feasible set is nonempty; for the source demands $0\le x\le1$, the all-one edge vector suffices. The infimum is finite and attained. For a set $S$, define $\mathbf1_S(v)=1$ on $S$ and zero elsewhere, and $\rho_H^*(S)=\rho_H^*(\mathbf1_S)$. All edges of $H$ are available to cover $S$.
--
--   An edge-dominated modular weighting is $w\in\mathbb R^V$ such that
--   $$w_v\ge0,\qquad \sum_{v\in e}w_v\le1\quad(e\in E),\qquad b_w(S)=\sum_{v\in S}w_v.$$
--   The family of these weightings is $M_H$ in singleton coordinates. Coverage implies $w_v\le1$. The logarithm used throughout is $\log_2 t=\ln(t)/\ln(2)$ on its positive source domain.
--
--   This interface defines actual cover optimization problems and modular bag costs, independently of either width. Real weights remain continuous and are not restricted to rational vectors.
-- source:
--   Matthias Lanzinger, STOC 2027 submission #662 (October 2026), pp. 8–9, Section 2.2 and Section 3.1 fractional-cover definitions; p. 7 logarithm convention

import Mathlib
import Definitions.Def_SparseIncidenceHom_WidthComparison_Hypergraphs

namespace SparseIncidenceHom.WidthComparison

/-- Real vertex demands and nonnegative real edge covers, pp. 8–9. -/
noncomputable def IsFractionalCover {V : Type} [Fintype V] (H : FiniteHypergraph V)
    (x : V → ℝ) (y : Edge H → ℝ) : Prop := by
  classical
  exact (∀ e, 0 ≤ y e) ∧ ∀ v, x v ≤ ∑ e : Edge H, if v ∈ e.val then y e else 0

noncomputable def coverCost {V : Type} [Fintype V] (H : FiniteHypergraph V)
    (x : V → ℝ) : ℝ :=
  sInf {c | ∃ y : Edge H → ℝ, IsFractionalCover H x y ∧ c = ∑ e, y e}

noncomputable def indicator {V : Type} (S : Set V) : V → ℝ := by
  classical
  exact fun v => if v ∈ S then 1 else 0

noncomputable def setCoverCost {V : Type} [Fintype V] (H : FiniteHypergraph V)
    (S : Set V) : ℝ := coverCost H (indicator S)

/-- The family M_H in singleton coordinates; no rationality restriction. -/
noncomputable def IsModularWeight {V : Type} [Fintype V] (H : FiniteHypergraph V)
    (w : V → ℝ) : Prop := by
  classical
  exact (∀ v, 0 ≤ w v) ∧ ∀ e : Edge H, (∑ v : V, if v ∈ e.val then w v else 0) ≤ 1

noncomputable def modularCost {V : Type} [Fintype V] (w : V → ℝ) (S : Set V) : ℝ := by
  classical
  exact ∑ v : V, if v ∈ S then w v else 0

noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

end SparseIncidenceHom.WidthComparison


