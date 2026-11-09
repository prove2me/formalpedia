-- Prove2me | Definitions.Def_CommutativeRankNC_Approximation_MatrixSpace
-- name    : CommutativeRankNC_Approximation_MatrixSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:45.874201+00:00
-- url     : https://prove2.me/theorems/9303332a-ae9c-44f4-8a0a-93ca1bf297a3
-- title:
--   Rational matrix spaces and generic pencils
-- statement:
--   Let $B_1,\ldots,B_m$ be rational $n\times n$ matrices. Their matrix space is $\mathcal B=\operatorname{span}_{\mathbb Q}\{B_i\}$, their scalar pencil is $B(a)=\sum_i a_iB_i$, and their commutative rank is
--
--   $$c=\max_{A\in\mathcal B}\operatorname{rank}A.$$
--
--   The maximum is represented by the supremum of its natural-valued ranks; this set contains zero and is bounded by $n$. The generic pencil has entries in the actual fraction field $\mathbb Q(x_1,\ldots,x_m)$. No maximizing witness is supplied. Empty dimensions and empty generating lists are admitted. These definitions are shared by the entire rank argument.
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), pp.1, 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Mathlib

namespace CommutativeRankNC.Approximation

/-- Rational square matrices, with zero dimensions admitted. -/
abbrev QMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℚ

/-- Evaluation of the homogeneous linear pencil on rational coefficients. -/
def pencilEval {n m : ℕ} (B : Fin m → QMatrix n) (a : Fin m → ℚ) : QMatrix n :=
  ∑ i, a i • B i

/-- The entire rational linear span, not a finite coefficient grid. -/
def matrixSpace {n m : ℕ} (B : Fin m → QMatrix n) : Submodule ℚ (QMatrix n) :=
  Submodule.span ℚ (Set.range B)

/-- Maximum rank: supremum in ℕ of the ranks in the span. This set contains zero
and is bounded by n; no maximum-rank witness is supplied to any algorithm. -/
noncomputable def commutativeRank {n m : ℕ} (B : Fin m → QMatrix n) : ℕ :=
  sSup {r | ∃ A ∈ matrixSpace B, A.rank = r}

/-- Actual generic pencil over the fraction field of the multivariate polynomial ring. -/
abbrev RationalFunctions (m : ℕ) := FractionRing (MvPolynomial (Fin m) ℚ)

noncomputable def genericPencil {n m : ℕ} (B : Fin m → QMatrix n) :
    Matrix (Fin n) (Fin n) (RationalFunctions m) :=
  fun u v => algebraMap _ _ (∑ i, MvPolynomial.X i * MvPolynomial.C (B i u v))

end CommutativeRankNC.Approximation


