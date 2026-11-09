-- Prove2me | Definitions.Def_SignRankMargin_OREquality_Geometry
-- name    : SignRankMargin_OREquality_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:41:44.835238+00:00
-- url     : https://prove2.me/theorems/87d13465-d83b-4248-b826-afca3c4b47c9
-- title:
--   Uniform matrix averages, one-counts, and exact unit-vector realizations
-- statement:
--   Let $X,Y$ be finite sets and $K:X\times Y\to\mathbb R$. Define its uniform average and the number of ones of a Boolean matrix $F$ by
--
--   $$
--   \operatorname{uniformAverage}(K)=\frac{1}{|X||Y|}\sum_{x\in X}\sum_{y\in Y}K(x,y),\qquad
--   \operatorname{oneCount}(F)=\sum_{x\in X}\sum_{y\in Y}\mathbf1[F(x,y)=1].
--   $$
--
--   For a natural dimension $r$, a unit-vector realization is a pair of families $u_x,v_y\in\mathbb R^r$ such that every vector has Euclidean norm exactly one and $H(x,y)=\langle u_x,v_y\rangle$ strictly realizes $F$.
--
--   These definitions give the averaging, sparsity and geometric interfaces shared by Lemmas 11, 12 and 13. The dimension in a unit realization is arbitrary; minimum dimension is required only by Lemma 11.
--
--   **Formalization Note** Vectors belong to Mathlib's real `EuclideanSpace`, with its inner product and Euclidean norm. Averages are finite sums, not integrals. All theorems using the average assume nonempty row and column sets. The helper returns zero on an empty set by real division's total convention; no geometric theorem uses that case.
-- source:
--   Gabriel Hart, Kaave Hosseini, STOC 2027 submission #728 (October 2026), Section 4, Section 4.1, p. 11; Lemma 13, p. 12

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_SignRank

namespace SignRankMargin.OREquality

/-- Uniform average over every row-column pair. All averaging lemmas use nonempty index types. -/
noncomputable def uniformAverage {X Y : Type*} [Fintype X] [Fintype Y]
    (H : Matrix X Y ℝ) : ℝ :=
  (∑ x, ∑ y, H x y) / ((Fintype.card X : ℝ) * (Fintype.card Y : ℝ))

/-- Total number of true entries, with no restriction to a submatrix. -/
def oneCount {X Y : Type*} [Fintype X] [Fintype Y] (F : Matrix X Y Bool) : ℕ :=
  ∑ x, ∑ y, if F x y then 1 else 0

/-- Each row and column vector has norm exactly one in real Euclidean r-space,
and their inner products strictly realize the Boolean matrix (§4.1, p.11). -/
def UnitRealization {X Y : Type*} (F : Matrix X Y Bool) (r : ℕ)
    (u : X → EuclideanSpace ℝ (Fin r)) (v : Y → EuclideanSpace ℝ (Fin r)) : Prop :=
  (∀ x, ‖u x‖ = 1) ∧ (∀ y, ‖v y‖ = 1) ∧
    StrictRealizes F (fun x y => inner ℝ (u x) (v y))

end SignRankMargin.OREquality


